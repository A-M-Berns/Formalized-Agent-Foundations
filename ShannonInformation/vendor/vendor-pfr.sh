#!/bin/zsh
# Re-vendor the PFR Shannon-information closure into `PFR/` from the pinned upstream
# commit, then apply any recorded compatibility patches (currently none: the tree is
# byte-identical to upstream).
#
#   ShannonInformation/vendor/vendor-pfr.sh            # re-vendor + patch
#   ShannonInformation/vendor/vendor-pfr.sh --verify   # re-vendor into a temp dir and
#                                                      # diff against the committed tree
#
# The vendored source IS committed (so the repository is self-contained and the
# kernel-checked dependency cannot vanish if upstream moves).  This script exists to make
# that tree reproducible and auditable, not to fetch it at build time.
#
# See ShannonInformation/vendor/PROVENANCE.md for the full record.
set -e

ROOT=${0:a:h}/../..
ROOT=${ROOT:a}
PFR_REPO=https://github.com/teorth/pfr.git
PFR_REV=65691129be2d8ca3e164c0822d95a456b88ee259
TMP=${TMPDIR:-/tmp}/faf-pfr-vendor

VERIFY=0
[[ "$1" == "--verify" ]] && VERIFY=1

echo "== 1. upstream checkout: teorth/pfr @ $PFR_REV =="
mkdir -p $TMP
# a half-made clone (interrupted run) is discarded rather than trusted
[[ -d $TMP/pfr/.git ]] || { rm -rf $TMP/pfr; git clone --quiet $PFR_REPO $TMP/pfr; }
git -C $TMP/pfr fetch --quiet origin
rm -rf $TMP/src
git -C $TMP/pfr worktree prune
git -C $TMP/pfr worktree add --quiet --detach $TMP/src $PFR_REV
echo "   upstream toolchain: $(cat $TMP/src/lean-toolchain)"
echo "   FAF toolchain:      $(cat $ROOT/lean-toolchain)"

if [[ $VERIFY == 1 ]]; then
  DEST=$TMP/verify
  rm -rf $DEST; mkdir -p $DEST/ShannonInformation/vendor
else
  DEST=$ROOT
fi

echo "== 2. import closure =="
SRC=$TMP/src DST=$DEST python3 $ROOT/ShannonInformation/vendor/closure.py

echo "== 3. compatibility patches =="
patches=($ROOT/ShannonInformation/vendor/patches/*.patch(N))
if (( ${#patches} )); then
  for p in $patches; do
    echo "   applying ${p:t}"
    ( cd $DEST && git apply --unsafe-paths --directory=. "$p" )
  done
else
  echo "   none recorded — the vendored tree is upstream verbatim"
fi

if [[ $VERIFY == 1 ]]; then
  echo "== 4. diffing regenerated tree against the committed one =="
  # `closure.py` copies module paths and nothing else, so any non-Lean file in the vendored
  # tree would itself be unexplained.
  stray=$(find $ROOT/PFR -type f ! -name '*.lean')
  if [[ -n "$stray" ]]; then
    echo "   UNEXPECTED non-Lean files in the vendored tree:"
    echo "$stray"
    exit 1
  fi
  if diff -r -q $DEST/PFR $ROOT/PFR > $TMP/verify.diff 2>&1; then
    echo "   IDENTICAL — the committed vendored tree is exactly upstream@$PFR_REV + patches"
  else
    echo "   DIFFERENCES FOUND:"
    cat $TMP/verify.diff
    exit 1
  fi
  diff -q $DEST/ShannonInformation/vendor/CLOSURE.txt \
          $ROOT/ShannonInformation/vendor/CLOSURE.txt \
    && echo "   CLOSURE.txt matches"
else
  echo "== done =="
  echo "   build with:  lake build PFR ShannonInformation"
fi
