#!/usr/bin/env python3
"""Monthly pin bump: propose what can move, hold what cannot, and say why.

Driven by `.github/workflows/pin-bump.yml`. Three subcommands, one per job:

  preflight   Resolve the tracked-branch head of every sha-pinned `require` in
              lakefile.lean, read each head's `lean-toolchain` and Mathlib pin, and
              decide per package whether it moves this month. No build, no Lean.
              Writes `report.json`. Exit 0 with status `ok` (something moves) or
              `unchanged` (nothing can); it fails only when the API does.

  rewrite     Apply the plan from `report.json` to the working tree: the shas of the
              packages that move, and the toolchain if it moves. `lake update` is the
              workflow's business, not this script's.

  publish     Read the artifacts and the run's own job list, then open a pull request
              (green), open/update a `pin-bump` issue (red), or close a stale one
              (recovered). The only subcommand that writes anywhere; it handles files as
              data and never runs Lean.

THE RULE. Safety lives in the validation, not in the preflight: whatever this script
proposes is built by ci.yml's `build` job — every checker, the full build, the sorry
ledger, the blanket axiom audit and the kernel replay — and only a green run becomes a
pull request, which nobody merges automatically. The preflight is therefore a cheap
predictor whose job is to spend the build on bumps that can work, and to say plainly
why the others cannot:

  * A package whose head is on the toolchain this repository already uses, or an older
    one, MOVES: Lake builds every dependency with the root's toolchain and the root's
    Mathlib, and whether that compiles is exactly what the validation decides.
  * A package whose head is on a NEWER toolchain is HELD, because moving it alone would
    mean a toolchain this repository's own code was not built on. The toolchain moves
    only when every pinned upstream's head agrees on one newer version and nothing is
    held by policy; then everything moves together, as the original rule asked.
  * A package named in POLICY_HOLD is HELD for the stated reason whatever its head
    says. Today that is Foundation: the pin is the last upstream commit that still
    contains `Foundation.Modal`, which `ModalAgents` is stated over (lakefile.lean), and
    moving past it is a migration, not a bump.
  * Mathlib pins are reported, never used as a gate: the root's Mathlib wins in Lake,
    and a disagreement is a thing the build settles.

A held package is information in the pull request body or the run summary, not a red
issue; a red issue is for a run that tried something and failed. A month in which nothing
can move is green, and it closes any `Pin bump blocked` issue a previous month left open.

Tracked branches. Each `require` tracks its repository's default branch except where
TRACKED_BRANCH says otherwise. `complexitylib` tracks the fork's `faf/v4.31`
compatibility branch (see the lakefile comment); the fork's default branch is upstream's
`dev`, whose head is the *base* of the compatibility branch, so "bumping" to it would roll
the pin backwards and drop the port.
"""

import argparse
import base64
import json
import os
import re
import subprocess
import sys
import urllib.parse

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LAKEFILE = "lakefile.lean"
MANIFEST = "lake-manifest.json"
TOOLCHAIN = "lean-toolchain"
PIN_FILES = (LAKEFILE, MANIFEST, TOOLCHAIN)

TRACKED_BRANCH = {
    "complexitylib": "faf/v4.31",
}

POLICY_HOLD = {
    "Foundation": (
        "the pin is the last upstream commit that still contains `Foundation.Modal`, which "
        "`ModalAgents` is stated over (see the `require Foundation` comment in lakefile.lean); "
        "moving past it is the ModalAgents migration, not a routine bump"
    ),
}

MAINTAINER = "A-M-Berns"
LABEL = "pin-bump"
PFR_PROVENANCE = "ShannonInformation/vendor/PROVENANCE.md"
LOG_LINES = 100

REQUIRE_RE = re.compile(
    r'^require\s+(?P<name>\w+)\s+from\s+git\s*\n?\s*"(?P<url>[^"]+)"\s*@\s*"(?P<rev>[0-9a-f]{40})"',
    re.M,
)


# ----------------------------------------------------------------------------- helpers

def gh(*args, check=True):
    p = subprocess.run(["gh", *args], capture_output=True, text=True)
    if check and p.returncode != 0:
        raise RuntimeError("gh %s failed (%d):\n%s" % (" ".join(args), p.returncode, p.stderr.strip()))
    return p


def gh_json(*args):
    return json.loads(gh("api", *args).stdout)


def repo_from_url(url):
    path = urllib.parse.urlparse(url).path.strip("/")
    return path[:-4] if path.endswith(".git") else path


def read(path):
    with open(os.path.join(ROOT, path), encoding="utf-8") as f:
        return f.read()


def write(path, text):
    with open(os.path.join(ROOT, path), "w", encoding="utf-8") as f:
        f.write(text)


def contents_at(repo, path, ref):
    data = gh_json("repos/%s/contents/%s?ref=%s" % (repo, path, ref))
    return base64.b64decode(data["content"]).decode("utf-8")


def mathlib_entry(manifest_text):
    for p in json.loads(manifest_text).get("packages", []):
        if p.get("name") == "mathlib":
            return p
    return None


def toolchain_key(tc):
    # leanprover/lean4:v4.34.0 -> (4, 34, 0, inf); v4.34.0-rc2 -> (4, 34, 0, 2)
    m = re.search(r"v(\d+)\.(\d+)\.(\d+)(?:-rc(\d+))?", tc)
    if not m:
        return (0, 0, 0, 0, tc)
    rc = int(m.group(4)) if m.group(4) else float("inf")
    return (int(m.group(1)), int(m.group(2)), int(m.group(3)), rc, "")


def short(rev):
    return rev[:10]


def set_output(name, value):
    out = os.environ.get("GITHUB_OUTPUT")
    if out:
        with open(out, "a", encoding="utf-8") as f:
            f.write("%s=%s\n" % (name, value))


def step_summary(text):
    out = os.environ.get("GITHUB_STEP_SUMMARY")
    if out:
        with open(out, "a", encoding="utf-8") as f:
            f.write(text + "\n")


def parse_requires(lakefile_text):
    found = [m.groupdict() for m in REQUIRE_RE.finditer(lakefile_text)]
    if not found:
        raise RuntimeError("no sha-pinned `require ... from git` found in lakefile.lean")
    return found


# --------------------------------------------------------------------------- preflight

def preflight(args):
    os.makedirs(args.out, exist_ok=True)
    root_tc = read(TOOLCHAIN).strip()
    old_ml = mathlib_entry(read(MANIFEST))
    report = {"status": None, "step": "preflight", "packages": [], "detail": "",
              "old_toolchain": root_tc, "new_toolchain": root_tc,
              "old_mathlib": old_ml["rev"] if old_ml else None}

    for req in parse_requires(read(LAKEFILE)):
        repo = repo_from_url(req["url"])
        meta = gh_json("repos/%s" % repo)
        branch = TRACKED_BRANCH.get(req["name"], meta["default_branch"])
        head = gh_json("repos/%s/commits/%s" % (repo, branch))
        toolchain = contents_at(repo, TOOLCHAIN, head["sha"]).strip()
        ml = mathlib_entry(contents_at(repo, MANIFEST, head["sha"]))
        p = {
            "name": req["name"], "url": req["url"], "repo": repo, "branch": branch,
            "default_branch": meta["default_branch"],
            "old_rev": req["rev"], "new_rev": head["sha"],
            "head_date": head["commit"]["committer"]["date"][:10],
            "toolchain": toolchain,
            "mathlib_rev": ml["rev"] if ml else None,
            "mathlib_input_rev": ml.get("inputRev") if ml else None,
            "state": None, "reason": "",
        }
        if p["old_rev"] == p["new_rev"]:
            p["state"], p["reason"] = "current", "already at its tracked head"
        elif p["name"] in POLICY_HOLD:
            p["state"], p["reason"] = "held", POLICY_HOLD[p["name"]]
        elif toolchain_key(toolchain) > toolchain_key(root_tc):
            p["state"] = "held"
            p["reason"] = ("its head is on `%s`, newer than this repository's `%s`; it moves only "
                           "when every pinned upstream agrees on that toolchain" % (toolchain, root_tc))
        else:
            p["state"] = "bump"
            p["reason"] = ("its head is on `%s`" % toolchain if toolchain == root_tc else
                           "its head is on the older `%s`; Lake builds it with this repository's "
                           "toolchain and Mathlib, which the validation decides" % toolchain)
        report["packages"].append(p)
        print("%-14s %s@%s %s -> %s  toolchain=%s  mathlib=%s  [%s]" % (
            p["name"], repo, branch, short(p["old_rev"]), short(p["new_rev"]), toolchain,
            short(p["mathlib_rev"]) if p["mathlib_rev"] else "none", p["state"]))

    pkgs = report["packages"]
    # The toolchain moves only when every head agrees on one newer version and nothing is
    # held by policy; then everything moves together.
    heads_tc = {p["toolchain"] for p in pkgs}
    policy_held = [p for p in pkgs if p["state"] == "held" and p["name"] in POLICY_HOLD]
    if len(heads_tc) == 1 and toolchain_key(next(iter(heads_tc))) > toolchain_key(root_tc) and not policy_held:
        report["new_toolchain"] = next(iter(heads_tc))
        for p in pkgs:
            if p["state"] == "held":
                p["state"] = "bump"
                p["reason"] = "every pinned upstream agrees on `%s`; the toolchain moves with them" % report["new_toolchain"]

    report["bumped"] = [p["name"] for p in pkgs if p["state"] == "bump"]
    report["held"] = [p["name"] for p in pkgs if p["state"] == "held"]
    if report["bumped"] or report["new_toolchain"] != root_tc:
        report["status"] = "ok"
        report["detail"] = "moving %s%s" % (
            ", ".join(report["bumped"]) or "the toolchain",
            "; toolchain %s -> %s" % (root_tc, report["new_toolchain"]) if report["new_toolchain"] != root_tc else "")
    else:
        report["status"] = "unchanged"
        report["detail"] = "nothing can move this month" + (
            " (held: %s)" % ", ".join(report["held"]) if report["held"] else "; every pin is at its tracked head")

    with open(os.path.join(args.out, "report.json"), "w", encoding="utf-8") as f:
        json.dump(report, f, indent=2)
    with open(os.path.join(args.out, "update-args"), "w", encoding="utf-8") as f:
        f.write(" ".join(report["bumped"]) + "\n")
    set_output("status", report["status"])
    step_summary("## Pin bump preflight: %s\n\n%s\n\n%s" % (report["status"], report["detail"], rev_table(report)))
    print("preflight:", report["status"], "-", report["detail"])
    return 0


# ----------------------------------------------------------------------------- rewrite

def rewrite(args):
    with open(args.report, encoding="utf-8") as f:
        report = json.load(f)
    if report["status"] != "ok":
        raise RuntimeError("rewrite called on a report with status %r" % report["status"])
    text = read(LAKEFILE)
    for p in report["packages"]:
        if p["state"] != "bump":
            continue
        old, new = '@ "%s"' % p["old_rev"], '@ "%s"' % p["new_rev"]
        if text.count(old) != 1:
            raise RuntimeError("expected exactly one pin %s for %s in lakefile.lean" % (old, p["name"]))
        text = text.replace(old, new)
    write(LAKEFILE, text)
    if report["new_toolchain"] != report["old_toolchain"]:
        write(TOOLCHAIN, report["new_toolchain"] + "\n")
    print("rewrote", LAKEFILE, "for", ", ".join(report["bumped"]) or "(no package)",
          "; toolchain", report["new_toolchain"])
    return 0


# ----------------------------------------------------------------------------- publish

def run_url():
    return "%s/%s/actions/runs/%s" % (
        os.environ["GITHUB_SERVER_URL"], os.environ["GITHUB_REPOSITORY"], os.environ["GITHUB_RUN_ID"])


def strip_timestamps(lines):
    ts = re.compile(r"^\d{4}-\d\d-\d\dT[0-9:.]+Z ")
    return [ts.sub("", ln) for ln in lines]


def first_error_excerpt(lines, n=LOG_LINES):
    """~n lines starting a little before the first `error` line (or the tail)."""
    lines = strip_timestamps(lines)
    pat = re.compile(r"(^|[\s:])error(:|\b)|\berror\[|FAIL\b|Traceback", re.I)
    for i, ln in enumerate(lines):
        if pat.search(ln) and "##[group]" not in ln:
            start = max(0, i - 5)
            return lines[start:start + n], ln
    return lines[-n:], (lines[-1] if lines else "")


def failed_jobs(repo, run_id):
    data = gh_json("repos/%s/actions/runs/%s/jobs?per_page=100" % (repo, run_id))
    out = []
    for job in data.get("jobs", []):
        if job.get("conclusion") not in ("failure", "timed_out", "cancelled"):
            continue
        steps = [s["name"] for s in job.get("steps", []) if s.get("conclusion") in ("failure", "timed_out")]
        out.append({"id": job["id"], "name": job["name"], "url": job["html_url"], "steps": steps})
    return out


def job_log(repo, job_id):
    p = gh("api", "repos/%s/actions/jobs/%s/logs" % (repo, job_id), check=False)
    return p.stdout.splitlines() if p.returncode == 0 else []


def mentions_pfr(excerpt):
    return any(re.search(r"(^|[\s./])PFR/[\w/]+\.lean", ln) for ln in excerpt)


def rev_table(report):
    rows = ["| package | tracked branch | pinned | head (date) | head toolchain | this month |",
            "| --- | --- | --- | --- | --- | --- |"]
    for p in report.get("packages", []):
        rows.append("| %s | `%s` | `%s` | `%s` (%s) | `%s` | **%s** — %s |" % (
            p["name"], p["branch"], short(p["old_rev"]), short(p["new_rev"]), p.get("head_date", ""),
            p["toolchain"], p.get("state", ""), p.get("reason", "")))
    rows.append("| lean-toolchain | | `%s` | | | %s |" % (
        report["old_toolchain"],
        "moves to `%s`" % report["new_toolchain"] if report.get("new_toolchain") != report["old_toolchain"] else "unchanged"))
    if report.get("old_mathlib"):
        rows.append("| Mathlib (transitive, root's wins) | | `%s` | | | heads pin: %s |" % (
            short(report["old_mathlib"]),
            ", ".join("%s `%s`" % (p["name"], short(p["mathlib_rev"])) for p in report["packages"] if p.get("mathlib_rev"))))
    return "\n".join(rows)


def ensure_label(repo):
    gh("label", "create", LABEL, "-R", repo, "--force",
       "--description", "Opened by the monthly pin-bump workflow", "--color", "0E8A16", check=False)


def open_issues(repo, title_prefix):
    p = gh("issue", "list", "-R", repo, "--state", "open", "--label", LABEL,
           "--json", "number,title,url", "--limit", "20")
    return [i for i in json.loads(p.stdout or "[]") if i["title"].startswith(title_prefix)]


def open_or_update_issue(repo, title_prefix, title, body):
    existing = open_issues(repo, title_prefix)
    if existing:
        issue = sorted(existing, key=lambda i: i["number"])[-1]
        gh("issue", "comment", str(issue["number"]), "-R", repo, "--body", body)
        gh("issue", "edit", str(issue["number"]), "-R", repo, "--add-assignee", MAINTAINER, check=False)
        print("commented on", issue["url"])
        return issue["url"]
    p = gh("issue", "create", "-R", repo, "--title", title, "--body", body, "--label", LABEL,
           "--assignee", MAINTAINER)
    print("opened", p.stdout.strip())
    return p.stdout.strip()


def close_blocked_issues(repo, body):
    """A green month closes what a red month opened."""
    for issue in open_issues(repo, "Pin bump blocked"):
        gh("issue", "comment", str(issue["number"]), "-R", repo, "--body", body)
        gh("issue", "close", str(issue["number"]), "-R", repo, "--reason", "completed")
        print("closed", issue["url"])


def publish(args):
    repo = os.environ["GITHUB_REPOSITORY"]
    run_id = os.environ["GITHUB_RUN_ID"]
    month = os.environ.get("PIN_BUMP_MONTH") or subprocess.run(
        ["date", "-u", "+%Y-%m"], capture_output=True, text=True).stdout.strip()
    report_path = os.path.join(args.report_dir, "report.json")
    report = None
    if os.path.exists(report_path):
        with open(report_path, encoding="utf-8") as f:
            report = json.load(f)
    ensure_label(repo)
    mention = "@%s" % MAINTAINER
    status = report["status"] if report else "failed"
    validate = args.validate_result  # success | failure | cancelled | skipped

    if status == "unchanged":
        summary = "\n".join([
            "%s — the %s pin bump has nothing to move: %s." % (mention, month, report["detail"]),
            "", rev_table(report), "", "**Run:** %s" % run_url(),
            "", "No build was spent and nothing was pushed. Held packages are not blockers: the "
            "rule holds a package whose head needs a newer toolchain, or one held by policy, and "
            "says so here rather than in an issue.",
        ])
        step_summary(summary)
        close_blocked_issues(repo, summary + "\n\nClosing: the blocker this issue reported is no "
                             "longer what the workflow does. Held packages are reported in each run's summary.")
        print("nothing to bump; no pull request, no issue")
        return 0
    if status == "ok" and validate == "success" and args.prepare_result == "success":
        return publish_green(repo, report, month, mention, args.pins_dir)

    # ---- red
    if report is None:
        step, detail, excerpt = "prepare (before preflight could write a report)", "", []
    elif args.prepare_result != "success":
        step, detail, excerpt = "lake update", "", []
        log_path = os.path.join(args.report_dir, "lake-update.log")
        if os.path.exists(log_path):
            with open(log_path, encoding="utf-8", errors="replace") as f:
                excerpt, _ = first_error_excerpt(f.read().splitlines())
    else:
        step, detail, excerpt = "validate (ci.yml build job): %s" % validate, "", []
        for job in failed_jobs(repo, run_id):
            if job["name"].startswith("publish"):
                continue
            step = "validate — job `%s`, step(s): %s" % (
                job["name"], ", ".join("`%s`" % s for s in job["steps"]) or "(none recorded)")
            excerpt, first = first_error_excerpt(job_log(repo, job["id"]))
            detail = "First error: `%s`" % first.strip()[:300]
            break
    pfr_note = ""
    if mentions_pfr(excerpt):
        pfr_note = (
            "\n\n**The first error is inside the vendored PFR slice (`PFR/`).** That directory is "
            "third-party source and this workflow does not edit it; re-vendoring is a deliberate act. "
            "See `%s` for the upstream commit, the compatibility patches and the re-vendor script.\n" % PFR_PROVENANCE)
    body = "\n".join([
        "%s — the %s pin bump is **blocked**." % (mention, month),
        "", "**Failing step:** %s" % step, "", detail, pfr_note,
        "**What was attempted**", "", rev_table(report) if report else "(no report was produced)",
        "", "**Run:** %s" % run_url(), "",
        "```\n%s\n```" % "\n".join(excerpt) if excerpt else "",
        "", "Nothing on `main` was changed. This workflow does not fix breakage; it reports it.",
    ])
    open_or_update_issue(repo, "Pin bump blocked", "Pin bump blocked: %s" % month, body)
    return 0


def publish_green(repo, report, month, mention, pins):
    for name in PIN_FILES:
        if not os.path.exists(os.path.join(pins, name)):
            raise RuntimeError("pins artifact is missing %s" % name)
    branch = "pin-bump/%s" % month
    moved = [p for p in report["packages"] if p["state"] == "bump"]
    title = "Pin bump %s: %s" % (month, ", ".join(
        "%s %s→%s" % (p["name"], short(p["old_rev"]), short(p["new_rev"])) for p in moved)
        + ("; toolchain → %s" % report["new_toolchain"] if report["new_toolchain"] != report["old_toolchain"] else ""))
    body = "\n".join([
        "%s — the %s pin bump validated green; please review." % (mention, month),
        "", rev_table(report), "",
        "**Validating run:** %s" % run_url(),
        "It ran the `build` job of `ci.yml` over exactly this tree — the Python checkers, the full "
        "`lake build`, the sorry ledger, the blanket axiom audit and the kernel replay.",
        "",
        "This pull request was opened with the workflow run's own token, and a pull request opened "
        "with that token does **not** trigger `ci.yml`. The checks you see here (none) are not a "
        "verdict; the validating run above is. Close and reopen it, or push an empty commit, if you "
        "want `ci.yml` to run on the pull request itself.",
        "",
        "Only `lakefile.lean`, `lake-manifest.json` and `lean-toolchain` change. Not merged by the "
        "workflow. Held packages are held for the reasons in the table, not because anything failed.",
    ])

    def git(*a):
        return subprocess.run(["git", *a], cwd=ROOT, check=True, capture_output=True, text=True)

    git("config", "user.name", "github-actions[bot]")
    git("config", "user.email", "41898282+github-actions[bot]@users.noreply.github.com")
    git("checkout", "-B", branch)
    for name in PIN_FILES:
        with open(os.path.join(pins, name), encoding="utf-8") as f:
            write(name, f.read())
    git("add", *PIN_FILES)
    msg = "Bump pins (%s)\n\n%s\n\nValidated by %s" % (
        month, "\n".join("%s: %s -> %s" % (p["name"], p["old_rev"], p["new_rev"]) for p in moved), run_url())
    git("commit", "-m", msg)
    git("push", "--force", "origin", "HEAD:refs/heads/%s" % branch)
    server = os.environ["GITHUB_SERVER_URL"]
    print("pushed", "%s/%s/tree/%s" % (server, repo, branch))

    p = gh("pr", "create", "-R", repo, "--base", "main", "--head", branch, "--title", title,
           "--body", body, "--label", LABEL, "--assignee", MAINTAINER, check=False)
    if p.returncode == 0:
        url = p.stdout.strip()
        print("opened", url)
        close_blocked_issues(repo, "%s — this month's bump validated green: %s" % (mention, url))
        step_summary("Opened %s" % url)
        return 0
    # The repository setting "Allow GitHub Actions to create and approve pull requests"
    # is off by default; without it the token cannot open the pull request. The branch
    # is pushed, so hand the maintainer the compare link instead of failing silently.
    compare = "%s/%s/compare/main...%s?expand=1" % (server, repo, branch.replace("/", "%2F"))
    fallback = "\n".join([
        "%s — the %s pin bump validated green, but the run token could not open the pull request:" % (mention, month),
        "", "```\n%s\n```" % p.stderr.strip()[-2000:], "",
        "The bump is pushed to `%s`; open it as a pull request from here: %s" % (branch, compare),
        "", body,
    ])
    url = open_or_update_issue(repo, "Pin bump ready", "Pin bump ready (pull request not opened): %s" % month, fallback)
    close_blocked_issues(repo, "%s — this month's bump validated green: %s" % (mention, url))
    return 0


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    a = sub.add_parser("preflight")
    a.add_argument("--out", default="pin-bump")
    b = sub.add_parser("rewrite")
    b.add_argument("--report", default="pin-bump/report.json")
    c = sub.add_parser("publish")
    c.add_argument("--report-dir", default="pin-bump")
    c.add_argument("--pins-dir", default="pins")
    c.add_argument("--prepare-result", required=True)
    c.add_argument("--validate-result", required=True)
    args = ap.parse_args()
    return {"preflight": preflight, "rewrite": rewrite, "publish": publish}[args.cmd](args)


if __name__ == "__main__":
    try:
        sys.exit(main())
    except RuntimeError as exc:
        print("pin_bump:", exc, file=sys.stderr)
        sys.exit(2)
