#!/bin/zsh
# Compile a spike file against the *parent* checkout's already-built oleans, so the
# worktree does not need its own Mathlib build.
R=/Users/anson/AgentFoundations
P=""
for d in $R/.lake/packages/*/.lake/build/lib/lean; do P="$P:$d"; done
export LEAN_PATH="${P#:}"
exec lean "$@"
