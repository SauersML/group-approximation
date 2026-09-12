#!/usr/bin/env bash
# census_merge.sh      (census merge 2026-09-11; runs everything ON MSI acn112 via the msi wrapper, never SLURM)
# Keep one live census work dir on MSI, synced to origin/main by git delta (full archive only for
# non_mf_groups_exist.tex, metadata, scripts). Merge $NM/rows/*.tsv into the sentence map with
# merge_rows.py, then run the census passes on the merged map: write, worklist, check, verify-decls,
# verify-unconditional.
#   BASELINE=<file>  replaces the conditional baseline before the passes.
#   Compiled evidence = every lane green record + $NM/census/clone-evidence.txt (clone oleans newer
#   than sources of the same bytes).
# Copies cc-out/ back to $NM/census/merge-<tag>/.
set -uo pipefail
NM=/private/tmp/claude-501/-Users-user-nonsofic-existence/77122910-de5a-4e59-a488-7cea550292c5/scratchpad/nm
REPO=/Users/user/nonsofic_existence
MSI=/Users/user/msi-node/msi; SOCK=/tmp/msi-login.sock; ALIAS=__MSI_LOGIN__
RSH="ssh -S $SOCK -o HostKeyAlias=$ALIAS -o LogLevel=ERROR"
P=/projects/standard/__MSI_GROUP__/__MSI_USER__
cd "$REPO" || exit 2
git fetch -q origin main || exit 1
SHA=$(git rev-parse origin/main)
TAG=$(date +%m%d-%H%M%S)
L=$P/nm/census-work/merge-live
PREV=$P/nm/census-work/35c6f5056b0c-merge-0911-213729
PREVSHA=$(git rev-parse 35c6f5056)
OUT=$NM/census/merge-$TAG; IN=$OUT/in; mkdir -p "$IN/rows"
echo "census merge tag=$TAG base=${SHA:0:9}"
ls -tr "$NM"/rows/*.tsv | while read -r f; do cp "$f" "$IN/rows/"; basename "$f"; done > "$IN/rows.order"
{ grep -hE '^[0-9a-f]{32}  GroupApproximation/' "$NM"/lanes/*.green.*; cat "$NM/census/clone-evidence.txt" 2>/dev/null; } | sort -u > "$IN/green-md5.txt"
cut -f4 "$NM"/rows/*.tsv | grep -oE '\b[0-9a-f]{7,40}\b' | sort -u | while read -r t; do
  full=$(git rev-parse --verify -q "$t^{commit}" 2>/dev/null) && git merge-base --is-ancestor "$full" "$SHA" && echo "$t $full"
done > "$IN/landed-shas.txt"
cp "$NM/census/merge_rows.py" "$NM/census/worklist.py" "$NM/census/overrides.tsv" "$IN/"
[ -n "${BASELINE:-}" ] && cp "$BASELINE" "$IN/baseline.txt"
echo "inputs: $(wc -l < "$IN/rows.order") row files, $(wc -l < "$IN/green-md5.txt") evidence lines, $(wc -l < "$IN/landed-shas.txt") landed shas"
"$MSI" true >/dev/null 2>&1 || "$MSI" up >/dev/null 2>&1 || { echo "msi down"; exit 4; }
"$MSI" "set -u; M=$P/nm/mirror.git; git -C \$M fetch -q origin 2>/dev/null; \
  if [ ! -d $L ]; then mv $PREV $L && echo $PREVSHA > $L/.base; fi; OLD=\$(cat $L/.base); \
  rm -rf $L/cc-out $L/cc-in $L/metadata $L/scripts; mkdir -p $L/cc-out $L/cc-in; \
  git -C \$M archive $SHA non_mf_groups_exist.tex metadata scripts | tar -x -C $L || exit 3; \
  git -C \$M diff --name-only --no-renames \$OLD $SHA -- GroupApproximation GroupApproximation.lean > $L/cc-out/delta.txt; \
  : > $L/cc-out/delta-present.txt; while IFS= read -r p; do if git -C \$M cat-file -e $SHA:\"\$p\" 2>/dev/null; then echo \"\$p\" >> $L/cc-out/delta-present.txt; else rm -f \"$L/\$p\"; fi; done < $L/cc-out/delta.txt; \
  if [ -s $L/cc-out/delta-present.txt ]; then tr '\n' '\0' < $L/cc-out/delta-present.txt | xargs -0 git -C \$M archive $SHA | tar -x -C $L || exit 3; fi; \
  echo $SHA > $L/.base; echo SYNCED \$(wc -l < $L/cc-out/delta.txt) changed paths" || exit 4
rsync -rlc -e "$RSH" "$IN/" "$ALIAS:$L/cc-in/" || exit 4
"$MSI" "cd $L || exit 2; PY=$P/params-venv/bin/python3; rm -rf scripts/__pycache__; \
  cp metadata/NON_MF_SENTENCE_MAP.tsv cc-out/map-origin.tsv; \
  \$PY scripts/sentence_census.py --badges-need-rows --json > cc-out/records.json 2> cc-out/json.err; echo JSON=\$?; \
  CLONES=$P/cc_clones \$PY cc-in/merge_rows.py cc-out/records.json cc-out/map-origin.tsv cc-in/green-md5.txt cc-in/landed-shas.txt $L \
    cc-out/map-merged.tsv cc-out/merge-report.tsv cc-out/existing-audit.tsv ${SHA:0:9} cc-in/overrides.tsv \$(sed 's|^|cc-in/rows/|' cc-in/rows.order) > cc-out/merge.txt 2>&1; echo MERGE=\$?; \
  test -s cc-out/map-merged.tsv || { echo NO-MERGED-MAP; exit 3; }; \
  cp cc-out/map-merged.tsv metadata/NON_MF_SENTENCE_MAP.tsv; \
  if [ -f cc-in/baseline.txt ]; then cp cc-in/baseline.txt metadata/NON_MF_CENSUS_CONDITIONAL_BASELINE.txt; fi; \
  \$PY scripts/sentence_census.py --badges-need-rows > cc-out/write.txt 2>&1; echo WRITE=\$?; \
  cp metadata/NON_MF_SENTENCE_CENSUS.tsv metadata/NON_MF_SENTENCE_CENSUS.md metadata/NON_MF_CENSUS_CONDITIONAL_BASELINE.txt cc-out/ 2>/dev/null; \
  \$PY cc-in/worklist.py metadata/NON_MF_SENTENCE_CENSUS.tsv cc-out/WORKLIST.md $TAG > cc-out/worklist.txt 2>&1; echo WORKLIST=\$?; \
  \$PY scripts/sentence_census.py --check --require-complete --badges-need-rows > cc-out/check.txt 2>&1; echo CHECK=\$?; \
  \$PY scripts/sentence_census.py --verify-decls --badges-need-rows > cc-out/verify-decls.txt 2>&1; echo VERIFY_DECLS=\$?; \
  \$PY scripts/sentence_census.py --verify-unconditional --badges-need-rows > cc-out/verify-unconditional.txt 2>&1; echo VERIFY_UNCOND=\$?; \
  echo SENTINEL=done"
rsync -rlc -e "$RSH" "$ALIAS:$L/cc-out/" "$OUT/" || exit 4
echo "outputs: $OUT"; cat "$OUT/merge.txt"; head -12 "$OUT/check.txt"; tail -8 "$OUT/verify-unconditional.txt"
