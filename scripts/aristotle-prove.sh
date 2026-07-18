#!/usr/bin/env bash
# Orchestrate an Aristotle proof job end-to-end: submit -> poll -> download ->
# extract. Verification against THIS repo's toolchain is left to the caller
# (the kernel is the trust gate, never Aristotle's word).
#
# Usage:  scripts/aristotle-prove.sh <project-dir> "<prompt>" [out-dir]
#
# <project-dir> should be a small, self-contained Lean project (Mathlib-only is
# ideal) containing the sorry'd goal. A lean-toolchain matching this repo is
# copied in if absent (best-effort; Aristotle may still pin its own Mathlib).
# Requires ARISTOTLE_API_KEY in the environment.
set -euo pipefail

proj_dir="${1:?usage: aristotle-prove.sh <project-dir> \"<prompt>\" [out-dir]}"
prompt="${2:?missing prompt}"
out_dir="${3:-${proj_dir%/}-aristotle-out}"
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

# Best-effort: give Aristotle our toolchain so its build matches ours.
if [ ! -f "$proj_dir/lean-toolchain" ] && [ -f "$repo_root/lean-toolchain" ]; then
  cp "$repo_root/lean-toolchain" "$proj_dir/lean-toolchain"
  echo "[harness] copied repo lean-toolchain into project dir"
fi

echo "[harness] submitting…"
pid="$(aristotle submit "$prompt" --project-dir "$proj_dir" 2>&1 | sed -n 's/^Project created: //p')"
[ -n "$pid" ] || { echo "[harness] submit failed (no project id)"; exit 1; }
echo "[harness] project id: $pid"

echo "[harness] polling (status via list; IDLE = done)…"
for _ in $(seq 1 120); do
  st="$(aristotle list --limit 20 2>/dev/null | awk -v p="$pid" '$1==p {print $NF}')"
  case "$st" in
    RUNNING|QUEUED|"") sleep 30 ;;
    *) echo "[harness] status: $st"; break ;;
  esac
done

archive="${out_dir%/}.tgz"
mkdir -p "$out_dir"
echo "[harness] downloading -> $archive"
aristotle download "$pid" --destination "$archive" >/dev/null 2>&1 || true
if [ -s "$archive" ]; then
  tar -xf "$archive" -C "$out_dir"
  echo "[harness] extracted to $out_dir:"
  find "$out_dir" -name '*.lean' -o -name 'ARISTOTLE_SUMMARY.md' | sed 's/^/  /'
else
  echo "[harness] no archive downloaded; inspect with: aristotle show $pid"
fi
echo "[harness] project id for reference: $pid"
echo "[harness] NEXT: verify any returned .lean compiles in THIS repo before trusting it."
