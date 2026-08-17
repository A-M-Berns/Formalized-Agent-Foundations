#!/bin/zsh
# Reproduce the PFR entropy vendoring experiment.
#
# Vendors the import closure of PFR's Shannon-entropy library from PFR commit 01c9b66
# (2026-06-27) — the LAST PFR commit on toolchain v4.31.0, which is this repo's toolchain —
# into vendor-experiment/, applies the two porting patches, and compiles the whole closure
# against this repo's already-built Mathlib oleans.
#
# Expected result: 25/25 modules compile, ~40s. See SPIKE-REPORT.md.
#
# The vendored source is NOT committed (third-party, Apache-2.0); this script regenerates it.
set -e

W=${0:a:h}/..                       # worktree root
W=${W:a}
R=/Users/anson/AgentFoundations     # parent checkout, for built oleans
TMP=${TMPDIR:-/tmp}/pfr-vendor
PFR_REV=01c9b666945eaf73b3f7d8b20ffe003f8640e630

echo "== 1. fetching PFR @ $PFR_REV =="
if [[ ! -d $TMP/pfr ]]; then
  mkdir -p $TMP
  git clone --quiet https://github.com/teorth/pfr.git $TMP/pfr
fi
rm -rf $TMP/src
git -C $TMP/pfr worktree prune
git -C $TMP/pfr worktree add --quiet --detach $TMP/src $PFR_REV
echo "   toolchain: $(cat $TMP/src/lean-toolchain)   (ours: $(cat $R/lean-toolchain))"

echo "== 2. computing import closure and copying =="
SRC=$TMP/src DST=$W/vendor-experiment python3 $W/Condensation/vendor-closure.py

echo "== 3. applying the two porting patches =="
W=$W python3 - <<'PY'
import os
W = os.environ['W']
# Patch 1: drop the `positivity` extension for `measureMutualInfo`.
p = f'{W}/vendor-experiment/PFR/ForMathlib/Entropy/Measure.lean'
s = open(p).read()
i = s.find('namespace Mathlib.Meta.Positivity')
assert i > 0, 'patch 1 anchor not found'
open(p, 'w').write(s[:i] + """-- VENDOR PATCH 1: the `positivity` extension for `measureMutualInfo` is removed.
-- `PositivityExt.eval` changed its `pa?` argument from `Option _` to `Q(PartialOrder $a)`
-- between PFR's Mathlib pin and ours.  Tactic plumbing, not mathematics: the underlying
-- `measureMutualInfo_nonneg` above is untouched and nothing downstream needs `positivity`
-- to know about `Im[mu]`.
""")
# Patch 2: `MeasurableEquiv.map_symm` is stated applied to a measure in our Mathlib.
p = f'{W}/vendor-experiment/PFR/ForMathlib/Entropy/Kernel/Basic.lean'
s = open(p).read()
old = """  convert entropy_comap_equiv κ (.punitProd) (μ := μ)
  · rfl
  rw [← MeasurableEquiv.map_symm]
  congr"""
new = """  convert entropy_comap_equiv κ (.punitProd) (μ := μ)
  · rfl
  -- VENDOR PATCH 2: `MeasurableEquiv.map_symm` is stated applied to a measure in our
  -- Mathlib, so this goal (an equality of the *functions* `Measure.map`/`Measure.comap`)
  -- must be `funext`-ed before the rewrite can fire.
  funext ν
  rw [← MeasurableEquiv.map_symm]
  rfl"""
assert old in s, 'patch 2 anchor not found'
open(p, 'w').write(s.replace(old, new))
print('   both patches applied')
PY

echo "== 4. compiling the closure against this repo's Mathlib =="
P=""
for d in $R/.lake/packages/*/.lake/build/lib/lean; do P="$P:$d"; done
export LEAN_PATH="${P#:}:$W/vendor-experiment/.build"
rm -rf $W/vendor-experiment/.build; mkdir -p $W/vendor-experiment/.build
: > $W/vendor-experiment/.build-log.txt
ok=0; fail=0
while read m; do
  [[ -z $m ]] && continue
  src=$W/vendor-experiment/${m//./\/}.lean
  olean=$W/vendor-experiment/.build/${m//./\/}.olean
  mkdir -p $(dirname $olean)
  echo "=== $m ===" >> $W/vendor-experiment/.build-log.txt
  if lean "$src" -o "$olean" >> $W/vendor-experiment/.build-log.txt 2>&1; then
    ok=$((ok+1)); echo "   OK    $m"
  else
    fail=$((fail+1)); echo "   FAIL  $m"
  fi
done < $W/vendor-experiment/ORDER.txt
echo
echo "compiled OK: $ok    failed: $fail"
echo
echo "Now: $W/Condensation/vendor-build.sh Condensation/VendorSmokeTest.lean"
