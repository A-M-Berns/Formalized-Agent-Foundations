#!/usr/bin/env python3
"""Monthly pin bump: propose new upstream revisions, or report the blocker.

Driven by `.github/workflows/pin-bump.yml`. Three subcommands, one per job:

  preflight   Resolve the tracked-branch head of every sha-pinned `require` in
              lakefile.lean, read each head's `lean-toolchain` and Mathlib pin, and
              decide whether a bump is even coherent. No build, no Lean. Writes
              `report.json`. Exit 1 when the heads disagree (the blocker names which
              upstream is behind); exit 0 with status `unchanged` when there is nothing
              to bump, or `ok` with the agreed toolchain and the old -> new revisions.

  rewrite     Apply the plan from `report.json` to the working tree: the three shas in
              lakefile.lean and the toolchain in lean-toolchain. `lake update` is the
              workflow's business, not this script's.

  publish     Read the artifacts and the run's own job list, then open a pull request
              (green) or open/update a `pin-bump` issue (red). This is the only
              subcommand that writes anywhere, and it handles files as data: it never
              runs Lean.

This script never fixes breakage. Every red path ends in a report, and `main` is
never touched: the pull request lives on its own branch and is not merged here.

Tracked branches. Each `require` tracks the head of its repository's default branch,
except where TRACKED_BRANCH says otherwise. `complexitylib` is pinned to the fork's
`faf/v4.31` compatibility branch (see the lakefile comment); that fork's default
branch is upstream's `dev`, whose head is the *base* of the compatibility branch, so
"bumping" to it would roll the pin backwards and drop the port.
"""

import argparse
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

MAINTAINER = "A-M-Berns"
LABEL = "pin-bump"
PFR_PROVENANCE = "ShannonInformation/vendor/PROVENANCE.md"
LOG_LINES = 100

REQUIRE_RE = re.compile(
    r'^require\s+(?P<name>\w+)\s+from\s+git\s*\n?\s*"(?P<url>[^"]+)"\s*@\s*"(?P<rev>[0-9a-f]{40})"',
    re.M,
)


# ----------------------------------------------------------------------------- helpers

def gh(*args, check=True, input_text=None):
    p = subprocess.run(["gh", *args], capture_output=True, text=True, input=input_text)
    if check and p.returncode != 0:
        raise RuntimeError("gh %s failed (%d):\n%s" % (" ".join(args), p.returncode, p.stderr.strip()))
    return p


def gh_json(*args):
    return json.loads(gh("api", *args).stdout)


def repo_from_url(url):
    path = urllib.parse.urlparse(url).path.strip("/")
    if path.endswith(".git"):
        path = path[:-4]
    return path


def read(path):
    with open(os.path.join(ROOT, path), encoding="utf-8") as f:
        return f.read()


def write(path, text):
    with open(os.path.join(ROOT, path), "w", encoding="utf-8") as f:
        f.write(text)


def contents_at(repo, path, ref):
    data = gh_json("repos/%s/contents/%s?ref=%s" % (repo, path, ref))
    import base64
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


def parse_requires(lakefile_text):
    found = [m.groupdict() for m in REQUIRE_RE.finditer(lakefile_text)]
    if not found:
        raise RuntimeError("no sha-pinned `require ... from git` found in lakefile.lean")
    return found


# --------------------------------------------------------------------------- preflight

def preflight(args):
    os.makedirs(args.out, exist_ok=True)
    report = {"status": None, "step": "preflight", "packages": [], "detail": ""}
    old_toolchain = read(TOOLCHAIN).strip()
    report["old_toolchain"] = old_toolchain
    old_manifest = mathlib_entry(read(MANIFEST))
    report["old_mathlib"] = old_manifest["rev"] if old_manifest else None

    for req in parse_requires(read(LAKEFILE)):
        repo = repo_from_url(req["url"])
        meta = gh_json("repos/%s" % repo)
        branch = TRACKED_BRANCH.get(req["name"], meta["default_branch"])
        head = gh_json("repos/%s/commits/%s" % (repo, branch))
        toolchain = contents_at(repo, TOOLCHAIN, head["sha"]).strip()
        ml = mathlib_entry(contents_at(repo, MANIFEST, head["sha"]))
        entry = {
            "name": req["name"],
            "url": req["url"],
            "repo": repo,
            "branch": branch,
            "default_branch": meta["default_branch"],
            "old_rev": req["rev"],
            "new_rev": head["sha"],
            "head_date": head["commit"]["committer"]["date"],
            "toolchain": toolchain,
            "mathlib_rev": ml["rev"] if ml else None,
            "mathlib_input_rev": ml.get("inputRev") if ml else None,
        }
        report["packages"].append(entry)
        print("%-14s %s@%s -> %s  toolchain=%s  mathlib=%s" % (
            req["name"], repo, branch, short(head["sha"]), toolchain,
            short(entry["mathlib_rev"]) if entry["mathlib_rev"] else "none"))

    pkgs = report["packages"]
    toolchains = {p["toolchain"] for p in pkgs}
    mathlibs = {p["mathlib_rev"] for p in pkgs}
    behind = []
    if len(toolchains) > 1:
        newest = max(toolchains, key=toolchain_key)
        behind = [p for p in pkgs if p["toolchain"] != newest]
        report["detail"] = (
            "The upstream heads disagree on `lean-toolchain`: "
            + ", ".join("%s is on `%s`" % (p["name"], p["toolchain"]) for p in pkgs)
            + ". Behind the newest (`%s`): %s." % (newest, ", ".join(p["name"] for p in behind))
        )
    elif len(mathlibs) > 1:
        for p in pkgs:
            if p["mathlib_rev"]:
                c = gh_json("repos/leanprover-community/mathlib4/commits/%s" % p["mathlib_rev"])
                p["mathlib_date"] = c["commit"]["committer"]["date"]
            else:
                p["mathlib_date"] = ""
        newest = max(pkgs, key=lambda p: p["mathlib_date"])["mathlib_rev"]
        behind = [p for p in pkgs if p["mathlib_rev"] != newest]
        report["detail"] = (
            "The upstream heads agree on the toolchain but disagree on the Mathlib pin: "
            + ", ".join("%s pins `%s` (%s)" % (p["name"], short(p["mathlib_rev"] or "none"),
                                               p.get("mathlib_date", "")) for p in pkgs)
            + ". Behind the newest (`%s`): %s." % (short(newest), ", ".join(p["name"] for p in behind))
        )

    if behind:
        report["status"] = "blocked"
        report["behind"] = [p["name"] for p in behind]
    elif all(p["old_rev"] == p["new_rev"] for p in pkgs) and old_toolchain in toolchains:
        report["status"] = "unchanged"
        report["detail"] = "Every pinned `require` is already at its tracked head; nothing to bump."
    else:
        report["status"] = "ok"
        report["agreed_toolchain"] = toolchains.pop()
        report["agreed_mathlib"] = mathlibs.pop()

    with open(os.path.join(args.out, "report.json"), "w", encoding="utf-8") as f:
        json.dump(report, f, indent=2)
    set_output("status", report["status"])
    print("preflight:", report["status"], "-", report["detail"] or "bump is coherent")
    return 1 if report["status"] == "blocked" else 0


# ----------------------------------------------------------------------------- rewrite

def rewrite(args):
    with open(args.report, encoding="utf-8") as f:
        report = json.load(f)
    if report["status"] != "ok":
        raise RuntimeError("rewrite called on a report with status %r" % report["status"])
    text = read(LAKEFILE)
    for p in report["packages"]:
        old = '@ "%s"' % p["old_rev"]
        new = '@ "%s"' % p["new_rev"]
        if text.count(old) != 1:
            raise RuntimeError("expected exactly one pin %s for %s in lakefile.lean" % (old, p["name"]))
        text = text.replace(old, new)
    write(LAKEFILE, text)
    write(TOOLCHAIN, report["agreed_toolchain"] + "\n")
    print("rewrote", LAKEFILE, "and", TOOLCHAIN, "->", report["agreed_toolchain"])
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
    if p.returncode != 0:
        return []
    return p.stdout.splitlines()


def mentions_pfr(excerpt):
    return any(re.search(r"(^|[\s./])PFR/[\w/]+\.lean", ln) for ln in excerpt)


def rev_table(report):
    rows = ["| package | tracked branch | old | new |", "| --- | --- | --- | --- |"]
    for p in report.get("packages", []):
        rows.append("| %s | `%s` | `%s` | `%s` |" % (
            p["name"], p["branch"], short(p["old_rev"]), short(p["new_rev"])))
    if report.get("agreed_toolchain"):
        rows.append("| lean-toolchain | | `%s` | `%s` |" % (report["old_toolchain"], report["agreed_toolchain"]))
    if report.get("old_mathlib") and report.get("agreed_mathlib"):
        rows.append("| Mathlib (transitive) | | `%s` | `%s` |" % (
            short(report["old_mathlib"]), short(report["agreed_mathlib"])))
    return "\n".join(rows)


def ensure_label(repo):
    gh("label", "create", LABEL, "-R", repo, "--force",
       "--description", "Opened by the monthly pin-bump workflow", "--color", "0E8A16", check=False)


def open_or_update_issue(repo, title_prefix, title, body):
    p = gh("issue", "list", "-R", repo, "--state", "open", "--label", LABEL,
           "--json", "number,title,url", "--limit", "20")
    existing = [i for i in json.loads(p.stdout) if i["title"].startswith(title_prefix)]
    if existing:
        issue = sorted(existing, key=lambda i: i["number"])[-1]
        gh("issue", "comment", str(issue["number"]), "-R", repo, "--body", body)
        gh("issue", "edit", str(issue["number"]), "-R", repo, "--add-assignee", MAINTAINER, check=False)
        print("commented on", issue["url"])
        return issue["url"]
    p = gh("issue", "create", "-R", repo, "--title", title, "--body", body,
           "--label", LABEL, "--assignee", MAINTAINER)
    url = p.stdout.strip()
    print("opened", url)
    return url


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

    # ---- which step failed, if any
    status = report["status"] if report else "blocked"
    validate = args.validate_result  # success | failure | cancelled | skipped
    if status == "unchanged":
        print("nothing to bump; no pull request, no issue")
        return 0
    if status == "ok" and validate == "success" and args.prepare_result == "success":
        return publish_green(repo, report, month, mention, args.pins_dir)

    # ---- red
    if report is None:
        step, detail, excerpt = "prepare (before preflight could write a report)", "", []
    elif status == "blocked":
        step, detail, excerpt = "preflight", report["detail"], []
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
            step = "validate — job `%s`, step(s): %s" % (job["name"], ", ".join("`%s`" % s for s in job["steps"]) or "(none recorded)")
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
        "",
        "**Failing step:** %s" % step,
        "",
        detail,
        pfr_note,
        "**Revisions attempted**",
        "",
        rev_table(report) if report else "(no report was produced)",
        "",
        "**Run:** %s" % run_url(),
        "",
        "```\n%s\n```" % "\n".join(excerpt) if excerpt else "",
        "",
        "Nothing on `main` was changed. This workflow does not fix breakage; it reports it.",
    ])
    open_or_update_issue(repo, "Pin bump blocked", "Pin bump blocked: %s" % month, body)
    return 0


def publish_green(repo, report, month, mention, pins):
    for name in PIN_FILES:
        if not os.path.exists(os.path.join(pins, name)):
            raise RuntimeError("pins artifact is missing %s" % name)
    branch = "pin-bump/%s" % month
    title = "Pin bump %s: %s" % (month, ", ".join(
        "%s %s→%s" % (p["name"], short(p["old_rev"]), short(p["new_rev"]))
        for p in report["packages"] if p["old_rev"] != p["new_rev"]))
    body = "\n".join([
        "%s — the %s pin bump validated green; please review." % (mention, month),
        "",
        rev_table(report),
        "",
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
        "workflow.",
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
        month,
        "\n".join("%s: %s -> %s" % (p["name"], p["old_rev"], p["new_rev"]) for p in report["packages"]),
        run_url())
    git("commit", "-m", msg)
    git("push", "--force", "origin", "HEAD:refs/heads/%s" % branch)
    branch_url = "%s/%s/tree/%s" % (os.environ["GITHUB_SERVER_URL"], repo, branch)
    print("pushed", branch_url)

    p = gh("pr", "create", "-R", repo, "--base", "main", "--head", branch, "--title", title,
           "--body", body, "--label", LABEL, "--assignee", MAINTAINER, check=False)
    if p.returncode == 0:
        print("opened", p.stdout.strip())
        return 0
    # The repository setting "Allow GitHub Actions to create and approve pull requests"
    # is off by default; without it the token cannot open the pull request. The branch
    # is pushed, so hand the maintainer the compare link instead of failing silently.
    fallback = "\n".join([
        "%s — the %s pin bump validated green, but the run token could not open the pull request:" % (mention, month),
        "",
        "```\n%s\n```" % p.stderr.strip()[-2000:],
        "",
        "The bump is pushed to `%s`; open it as a pull request from here: %s/%s/compare/main...%s?expand=1" % (
            branch, os.environ["GITHUB_SERVER_URL"], repo, branch.replace("/", "%2F")),
        "",
        body,
    ])
    open_or_update_issue(repo, "Pin bump ready", "Pin bump ready (pull request not opened): %s" % month, fallback)
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
