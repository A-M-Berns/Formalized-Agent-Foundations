#!/bin/zsh
# Re-vendor the PFR Shannon-information closure into `PFR/` from the pinned upstream
# commit, then apply the recorded compatibility patches.
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
PFR_REV=01c9b666945eaf73b3f7d8b20ffe003f8640e630
TMP=${TMPDIR:-/tmp}/faf-pfr-vendor

VERIFY=0
[[ "$1" == "--verify" ]] && VERIFY=1

echo "== 1. upstream checkout: teorth/pfr @ $PFR_REV =="
mkdir -p $TMP
[[ -d $TMP/pfr ]] || git clone --quiet $PFR_REPO $TMP/pfr
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
for p in $ROOT/ShannonInformation/vendor/patches/*.patch; do
  echo "   applying ${p:t}"
  ( cd $DEST && git apply --unsafe-paths --directory=. "$p" )
done

if [[ $VERIFY == 1 ]]; then
  echo "== 4. diffing regenerated tree against the committed one =="
  # `PFR/README.md` is FAF-authored (a "do not edit, here is the provenance" marker placed
  # where a browser of the vendored tree will actually see it), so it is excluded from the
  # comparison.  To make sure that exclusion cannot mask real drift, first assert it is the
  # ONLY non-`.lean` file in the tree — `closure.py` copies module paths and nothing else,
  # so any other non-Lean file would itself be unexplained.
  stray=$(find $ROOT/PFR -type f ! -name '*.lean' ! -name 'README.md')
  if [[ -n "$stray" ]]; then
    echo "   UNEXPECTED non-Lean files in the vendored tree:"
    echo "$stray"
    exit 1
  fi
  echo "   (PFR/README.md is FAF-authored and excluded; no other non-Lean file present)"
  if diff -r -q -x README.md $DEST/PFR $ROOT/PFR > $TMP/verify.diff 2>&1; then
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
