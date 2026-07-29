#!/bin/bash
# WorktreeCreate hook: seed Lean olean caches into a freshly created worktree.
# Without this, every agent worktree silently rebuilds Mathlib + Foundation from
# source (hours, OOM-prone under parallel agents). Reads the hook JSON on stdin,
# extracts the worktree path, and copy-on-write clones the main checkout's build
# artifacts. Idempotent; safe to re-run.
set -u
MAIN="${CLAUDE_PROJECT_DIR:-/Users/anson/AgentFoundations}"

input=$(cat 2>/dev/null || true)
WT=$(printf '%s' "$input" | jq -r '.worktree_path // .path // .tool_input.path // empty' 2>/dev/null)
if [ -z "$WT" ] || [ ! -d "$WT" ]; then
  # Fallback: newest worktree directory.
  WT=$(ls -td "$MAIN"/.claude/worktrees/*/ 2>/dev/null | head -1)
fi
[ -n "$WT" ] && [ -d "$WT" ] || exit 0
case "$WT" in "$MAIN"/.claude/worktrees/*) ;; *) exit 0 ;; esac

clone() { # clone SRC DST — copy-on-write if possible, skip if DST populated
  local src="$1" dst="$2"
  [ -d "$src" ] || return 0
  [ -e "$dst" ] && return 0
  mkdir -p "$(dirname "$dst")"
  cp -Rc "$src" "$dst" 2>/dev/null || cp -R "$src" "$dst"
}

clone "$MAIN/.lake/build" "$WT/.lake/build"
for p in "$MAIN"/.lake/packages/*/; do
  name=$(basename "$p")
  [ -d "$WT/.lake/packages/$name" ] || cp -Rc "$p" "$WT/.lake/packages/$name" 2>/dev/null \
    || cp -R "$p" "$WT/.lake/packages/$name" 2>/dev/null
  clone "$p/.lake/build" "$WT/.lake/packages/$name/.lake/build"
done
echo '{"systemMessage": "Seeded Lean build caches into new worktree."}'
exit 0
