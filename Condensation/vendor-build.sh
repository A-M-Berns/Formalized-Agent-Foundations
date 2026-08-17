#!/bin/zsh
# Compile a file that imports the vendored PFR entropy substrate.
# Requires vendor-experiment/.build to be populated first (see SPIKE-REPORT.md).
W=/Users/anson/AgentFoundations/.claude/worktrees/spike-2412.02579
R=/Users/anson/AgentFoundations
P=""
for d in $R/.lake/packages/*/.lake/build/lib/lean; do P="$P:$d"; done
export LEAN_PATH="${P#:}:$W/vendor-experiment/.build"
exec lean "$@"
