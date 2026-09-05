#!/usr/bin/env bash
# Validate `Paper node:` annotations against the paper source and the audited inventory.
#
#   1. Every label cited in a `Paper node:` field exists as a `\label{...}` in the
#      paper source. Catches typos and stale references after a paper/rename.
#   1b. Every backticked `kind:name` token anywhere in a `LogicalInduction/` source —
#      prose as well as annotations — is either a real `\label{...}`, a `dd:` glossary
#      entry, or a `tex:NNNN` line citation. Catches phantom labels cited in explanatory
#      prose, which check 1 never looks at (a whole family of `def:pgen` miscitations
#      survived years of green runs because they sat in module docstrings).
#   2. Every declaration named in `AxiomAudit.lean` (Tier 1 endpoints and Tier 2
#      `#assert_fields` structures) carries a `Paper node:` field. Catches surface
#      members that lost their annotation. A docstring counts as carrying one only if its
#      `Paper node` line bears an actual backticked `kind:label` token: a *sentence* about
#      annotation ("carries no `Paper node` line") must not satisfy the check, which is
#      how three refutation endpoints once passed it.
#
# Run from repo root. Exits nonzero on any violation, and says so on the last line: a
# reader (or a log skimmed through a pipe, where the exit status is the pipeline's and not
# this script's) must never see a cheerful last line from a failing run. The EXIT trap
# covers the `set -e` paths too, where a violation is not what ended the script.
set -euo pipefail
cd "$(dirname "$0")/.."

reported=0
finish() {
  status=$?
  if [ "$status" -ne 0 ] && [ "$reported" -eq 0 ]; then
    echo "paper-node check: FAIL — aborted before finishing (exit $status)"
  fi
}
trap finish EXIT

TEX=LogicalInduction/notes/1609.03543v5-main.tex
LIB=LogicalInduction
AUDIT=AxiomAudit.lean

fail=0

# --- 1. label validity ------------------------------------------------------
grep -oE '\\label\{[a-zA-Z0-9:_-]+\}' "$TEX" | sed 's/\\label{//;s/}//' | sort -u > /tmp/_pn_labels
# every backticked `kind:name` token appearing on a `Paper node` line
grep -rhoE 'Paper nodes?:.*' --include='*.lean' "$LIB" \
  | grep -oE '`[a-z]+:[a-zA-Z0-9_-]+`' | tr -d '`' | sort -u > /tmp/_pn_used
while read -r lab; do
  [ -z "$lab" ] && continue
  if ! grep -qxF "$lab" /tmp/_pn_labels; then
    echo "INVALID LABEL: \`$lab\` is not a \\label in $TEX"
    fail=1
  fi
done < /tmp/_pn_used

# --- 1b. whole-docstring label validity -------------------------------------
# Every backticked `kind:name` token anywhere in the library, not only on annotation lines.
# `dd:` is this repo's own design-decision glossary (defined once, in LogicalInduction.lean)
# and `tex:NNNN` is a line citation into the paper source; everything else must resolve to a
# real `\label`.
grep -oE 'dd:[a-zA-Z0-9_-]+' LogicalInduction.lean | sort -u > /tmp/_pn_dd
grep -rhoE '`[a-z]+:[a-zA-Z0-9_-]+`' --include='*.lean' "$LIB" \
  | tr -d '`' | sort -u > /tmp/_pn_prose
while read -r tok; do
  [ -z "$tok" ] && continue
  case "$tok" in
    tex:[0-9]*) continue ;;
    dd:*)
      if ! grep -qxF "$tok" /tmp/_pn_dd; then
        echo "INVALID LABEL: \`$tok\` is not defined in the LogicalInduction.lean dd: glossary"
        fail=1
      fi
      continue ;;
  esac
  if ! grep -qxF "$tok" /tmp/_pn_labels; then
    echo "INVALID LABEL (prose): \`$tok\` is not a \\label in $TEX"
    grep -rn "\`$tok\`" --include='*.lean' "$LIB" | sed 's/^/    /'
    fail=1
  fi
done < /tmp/_pn_prose

# --- 2. inventory coverage --------------------------------------------------
# Short names on the surface. `#assert_axioms_clean` blocks: every ident (the head line
# plus 2-space continuation lines) is an endpoint. `#assert_fields` lines: only the first
# ident (the structure) — the rest are its field names, not surface members themselves.
# Only the `LogicalInduction` section participates in the Garrabrant paper-node convention;
# the `ModalAgents/` section (after `end LogicalInduction`) mirrors a different paper and is
# axiom-checked by AxiomAudit's build, not by this label convention — so stop there.
awk '
  /^end LogicalInduction/ { exit }
  /^#assert_axioms_clean/ { mode="ax"; sub(/^#assert_axioms_clean(_except)?/,""); print; next }
  /^#assert_fields/       { mode="fl"; sub(/^#assert_fields[ \t]+/,"");
                            n=split($0,a,/[ \t]+/); if(n>0)print a[1]; next }
  /^  [A-Za-z]/           { if(mode=="ax") print; next }
  { mode="" }
' "$AUDIT" \
  | grep -oE '[A-Za-z_][A-Za-z0-9_.₀₁₂₃₄₅₆₇₈₉'"'"']*' \
  | sed 's/.*\.//' | sort -u > /tmp/_pn_inv
# Short names that carry a Paper node field (declaration on the line after the field's `-/`).
# The `Paper node` line must bear a real backticked `kind:label` token — a sentence *about*
# annotation is prose, not an annotation, and must not license the declaration that follows.
grep -rlE 'Paper nodes?:.*`[a-z]+:[a-zA-Z0-9_-]+`' --include='*.lean' "$LIB" | while read -r f; do
  awk '/Paper nodes?:.*`[a-z]+:[a-zA-Z0-9_-]+`/{p=1} p&&/-\/$/{f=1;next} f{print;f=0;p=0}' "$f"
done | grep -oE '(structure|def|theorem|lemma|abbrev|class)\s+[A-Za-z_][A-Za-z0-9_.₀₁₂₃₄₅₆₇₈₉'"'"']*' \
  | awk '{print $2}' | sed 's/.*\.//' | sort -u > /tmp/_pn_have

# Inventoried members that carry no annotation ON PURPOSE, each with the reason.  These
# REFUTE a paper claim rather than render one, so a `Paper node:` line would misfile them as
# a rendering of the very statement they disprove (`thm:ifp`, `notes/paper-errata.md` PE1).
# They stay inventoried because they must stay axiom-clean; the curated `thm:ifp` endpoint is
# `not_overgeneral_ifp`, which is annotated.  Same discipline as
# `check_endpoint_coverage.py`'s excuse table: an exemption is named and justified, never
# implicit.
cat > /tmp/_pn_exempt <<'EOF'
exists_advice_perturbation
exists_advice_perturbation_ofTheory
not_overgeneral_ifp_ofTheory
not_overgeneral_ifp_of_advice
EOF

while read -r nm; do
  [ -z "$nm" ] && continue
  if grep -qxF "$nm" /tmp/_pn_exempt; then continue; fi
  if ! grep -qxF "$nm" /tmp/_pn_have; then
    echo "MISSING FIELD: inventory member '$nm' has no Paper node annotation"
    fail=1
  fi
done < /tmp/_pn_inv

# The exemption list must not rot: an exempted name that is no longer inventoried, or that
# has since acquired an annotation, is a stale excuse and fails the run.
while read -r nm; do
  [ -z "$nm" ] && continue
  if ! grep -qxF "$nm" /tmp/_pn_inv; then
    echo "STALE EXEMPTION: '$nm' is exempted from the annotation rule but is not inventoried"
    fail=1
  elif grep -qxF "$nm" /tmp/_pn_have; then
    echo "STALE EXEMPTION: '$nm' is exempted from the annotation rule but now carries one"
    fail=1
  fi
done < /tmp/_pn_exempt

# --- 3. reverse coverage: every annotated label has an inventory endpoint ----------
# Checks 1-2 above verify inventory -> paper (listed endpoints cite real, annotated
# labels). This verifies paper -> inventory (every annotated label has a listed endpoint).
if ! python3 scripts/check_endpoint_coverage.py; then
  fail=1
fi

if [ "$fail" -eq 0 ]; then
  echo "paper-node check: OK ($(wc -l < /tmp/_pn_used | tr -d ' ') distinct labels, all valid; inventory covered both directions)"
else
  reported=1
  echo "paper-node check: FAIL — see the violations above"
fi
exit $fail
