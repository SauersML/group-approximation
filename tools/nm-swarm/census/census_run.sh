#!/usr/bin/env bash
# census_run.sh [<local map tsv>]      (lane census; runs everything ON MSI)
# Export origin/main from the MSI mirror into a fresh work dir, optionally replace the
# overlay map by <local map tsv>, run the census passes, copy cc-out/ back to
# $NM/census/out-<tag>/.  Prints the tag and the pass exit codes.
set -uo pipefail
NM=/private/tmp/claude-501/-Users-user-nonsofic-existence/77122910-de5a-4e59-a488-7cea550292c5/scratchpad/nm
REPO=/Users/user/nonsofic_existence
MSI=/Users/user/msi-node/msi; SOCK=/tmp/msi-login.sock; ALIAS=__MSI_LOGIN__
RSH="ssh -S $SOCK -o HostKeyAlias=$ALIAS -o LogLevel=ERROR"
MAPF=${1:-}
cd "$REPO" || exit 2
git fetch -q origin main || exit 1
SHA=$(git rev-parse origin/main)
TAG=$(date +%m%d-%H%M%S)
W=/projects/standard/__MSI_GROUP__/__MSI_USER__/nm/census-work/${SHA:0:12}-$TAG
OUT=$NM/census/out-$TAG; mkdir -p "$OUT"
echo "census run tag=$TAG base=${SHA:0:9} map=${MAPF:-origin}"
"$MSI" true >/dev/null 2>&1 || "$MSI" up >/dev/null 2>&1 || { echo "msi down"; exit 4; }
"$MSI" "set -u; P=/projects/standard/__MSI_GROUP__/__MSI_USER__; mkdir -p $W/cc-out && git -C \$P/nm/mirror.git fetch -q origin 2>/dev/null; git -C \$P/nm/mirror.git archive $SHA non_mf_groups_exist.tex metadata scripts GroupApproximation GroupApproximation.lean | tar -x -C $W && echo EXPORTED; echo SENTINEL=\$?" || exit 4
if [ -n "$MAPF" ]; then
  rsync -lc -e "$RSH" "$MAPF" "$ALIAS:$W/metadata/NON_MF_SENTENCE_MAP.tsv" || exit 4
fi
if [ -n "${BASELINE:-}" ]; then
  rsync -lc -e "$RSH" "$BASELINE" "$ALIAS:$W/metadata/NON_MF_CENSUS_CONDITIONAL_BASELINE.txt" || exit 4
fi
rsync -lc -e "$RSH" "$NM/census/worklist.py" "$ALIAS:$W/cc-out/worklist.py" || exit 4
"$MSI" "cd $W || exit 2; PY=/projects/standard/__MSI_GROUP__/__MSI_USER__/params-venv/bin/python3; rm -rf scripts/__pycache__; \
  \$PY scripts/sentence_census.py --badges-need-rows --json > cc-out/records.json 2> cc-out/json.err; echo JSON=\$?; \
  \$PY scripts/sentence_census.py --badges-need-rows --summary > cc-out/summary.txt 2>&1; echo SUMMARY=\$?; \
  \$PY scripts/sentence_census.py --badges-need-rows > cc-out/write.txt 2>&1; echo WRITE=\$?; \
  cp metadata/NON_MF_SENTENCE_CENSUS.tsv metadata/NON_MF_SENTENCE_CENSUS.md cc-out/ 2>/dev/null; \
  \$PY cc-out/worklist.py metadata/NON_MF_SENTENCE_CENSUS.tsv cc-out/WORKLIST.md $TAG > cc-out/worklist.txt 2>&1; echo WORKLIST=\$?; \
  \$PY scripts/sentence_census.py --badges-need-rows --list-unassigned > cc-out/unassigned.txt 2>&1; echo LISTUN=\$?; \
  \$PY scripts/sentence_census.py --check --require-complete --badges-need-rows > cc-out/check.txt 2>&1; echo CHECK=\$?; \
  \$PY scripts/sentence_census.py --verify-decls --badges-need-rows > cc-out/verify-decls.txt 2>&1; echo VERIFY_DECLS=\$?; \
  \$PY scripts/sentence_census.py --verify-unconditional --badges-need-rows > cc-out/verify-unconditional.txt 2>&1; echo VERIFY_UNCOND=\$?; \
  echo SENTINEL=done"
rsync -rlc -e "$RSH" "$ALIAS:$W/cc-out/" "$OUT/" || exit 4
echo "outputs: $OUT"; ls "$OUT"; cat "$OUT/summary.txt" | head -40
