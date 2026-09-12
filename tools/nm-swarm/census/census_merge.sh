#!/usr/bin/env bash
# census_merge.sh [--no-land]     (census merge; runs every pass ON MSI acn112 via the msi wrapper, never SLURM)
#
# One step of the census merge, landed (COMMON_RULES rule 21: land at every merge step):
#  1. export origin/main into ONE live census work dir on MSI (git delta for GroupApproximation);
#  2. rows = origin's metadata/nm-census-rows/*.tsv (the lead keeps every lane's raw rows in the repo),
#     falling back to $NM/rows/*.tsv while that directory is absent;
#  3. merge_rows.py over origin's map (unions per sentence, compiled-evidence downgrades and restorations,
#     overrides.tsv); regenerate the census; register.py keeps the conditional register in step (stale lines
#     commented out, new findings registered with a justification, UNCLASSIFIED findings stop the landing);
#  4. check / verify-decls / verify-unconditional / worklist;
#  5. install map, register and census tsv/md into the shared tree and land them with NM_BASE=<export sha>
#     (only when MERGE, WRITE, REGISTER, VERIFY_DECLS and VERIFY_UNCOND are 0, and only if the tree's copies equal
#     origin at the export sha, so no peer's unlanded edit is overwritten).
# Outputs: $NM/census/merge-<tag>/; worklist also at $NM/WORKLIST.md.
set -uo pipefail
NM=/private/tmp/claude-501/-Users-user-nonsofic-existence/77122910-de5a-4e59-a488-7cea550292c5/scratchpad/nm
REPO=/Users/user/nonsofic_existence
MSI=/Users/user/msi-node/msi; SOCK=/tmp/msi-login.sock; ALIAS=__MSI_LOGIN__
RSH="ssh -S $SOCK -o HostKeyAlias=$ALIAS -o LogLevel=ERROR"
P=/projects/standard/__MSI_GROUP__/__MSI_USER__
FILES="metadata/NON_MF_SENTENCE_MAP.tsv metadata/NON_MF_CENSUS_CONDITIONAL_BASELINE.txt metadata/NON_MF_SENTENCE_CENSUS.tsv metadata/NON_MF_SENTENCE_CENSUS.md"
cd "$REPO" || exit 2
git fetch -q origin main || exit 1
SHA=$(git rev-parse origin/main)
TAG=$(date +%m%d-%H%M%S)
L=$P/nm/census-work/merge-live
OUT=$NM/census/merge-$TAG; IN=$OUT/in; mkdir -p "$IN/rows"
echo "census merge tag=$TAG base=${SHA:0:9}"
# Per lane: origin's metadata/nm-census-rows/<lane>.tsv when the lead has landed it, else $NM/rows/<lane>.tsv.
: > "$IN/rows.order"; NREPO=0; NSCR=0
for f in $(git ls-tree --name-only "$SHA" -- metadata/nm-census-rows/ | grep '\.tsv$' | sort); do
  git show "$SHA:$f" > "$IN/rows/$(basename "$f")"; basename "$f" >> "$IN/rows.order"; NREPO=$((NREPO+1))
done
for f in $(ls "$NM"/rows/*.tsv 2>/dev/null | sort); do
  b=$(basename "$f"); [ -e "$IN/rows/$b" ] && continue
  cp "$f" "$IN/rows/$b"; echo "$b" >> "$IN/rows.order"; NSCR=$((NSCR+1))
done
ROWSRC="metadata/nm-census-rows for $NREPO lanes, scratchpad rows for $NSCR"
{ grep -hE '^[0-9a-f]{32}  GroupApproximation/' "$NM"/lanes/*.green.*; cat "$NM/census/clone-evidence.txt" 2>/dev/null; } | sort -u > "$IN/green-md5.txt"
cut -f4 "$IN"/rows/*.tsv | grep -oE '\b[0-9a-f]{7,40}\b' | sort -u | while read -r t; do
  full=$(git rev-parse --verify -q "$t^{commit}" 2>/dev/null) && git merge-base --is-ancestor "$full" "$SHA" && echo "$t $full"
done > "$IN/landed-shas.txt"
cp "$NM/census/merge_rows.py" "$NM/census/register.py" "$NM/census/worklist.py" "$NM/census/overrides.tsv" "$IN/"
echo "inputs: rows from $ROWSRC ($(wc -l < "$IN/rows.order") files), $(wc -l < "$IN/green-md5.txt") evidence lines, $(wc -l < "$IN/landed-shas.txt") landed shas"
"$MSI" true >/dev/null 2>&1 || "$MSI" up >/dev/null 2>&1 || { echo "msi down"; exit 4; }
"$MSI" "set -u; M=$P/nm/mirror.git; git -C \$M fetch -q origin 2>/dev/null; OLD=\$(cat $L/.base); \
  rm -rf $L/cc-out $L/cc-in $L/metadata $L/scripts; mkdir -p $L/cc-out $L/cc-in; \
  git -C \$M archive $SHA non_mf_groups_exist.tex metadata scripts | tar -x -C $L || exit 3; \
  git -C \$M diff --name-only --no-renames \$OLD $SHA -- GroupApproximation GroupApproximation.lean > $L/cc-out/delta.txt; \
  : > $L/cc-out/delta-present.txt; while IFS= read -r p; do if git -C \$M cat-file -e $SHA:\"\$p\" 2>/dev/null; then echo \"\$p\" >> $L/cc-out/delta-present.txt; else rm -f \"$L/\$p\"; fi; done < $L/cc-out/delta.txt; \
  if [ -s $L/cc-out/delta-present.txt ]; then tr '\n' '\0' < $L/cc-out/delta-present.txt | xargs -0 git -C \$M archive $SHA | tar -x -C $L || exit 3; fi; \
  echo $SHA > $L/.base; echo SYNCED \$(wc -l < $L/cc-out/delta.txt) changed paths" || exit 4
rsync -rlc -e "$RSH" "$IN/" "$ALIAS:$L/cc-in/" || exit 4
"$MSI" "cd $L || exit 2; PY=$P/params-venv/bin/python3; rm -rf scripts/__pycache__; S=scripts/sentence_census.py; \
  cp metadata/NON_MF_SENTENCE_MAP.tsv cc-out/map-origin.tsv; cp metadata/NON_MF_CENSUS_CONDITIONAL_BASELINE.txt cc-out/register-origin.txt; \
  \$PY \$S --badges-need-rows --json > cc-out/records.json 2> cc-out/json.err; echo JSON=\$?; \
  CLONES=$P/cc_clones \$PY cc-in/merge_rows.py cc-out/records.json cc-out/map-origin.tsv cc-in/green-md5.txt cc-in/landed-shas.txt $L \
    cc-out/map-merged.tsv cc-out/merge-report.tsv cc-out/existing-audit.tsv ${SHA:0:9} cc-in/overrides.tsv \$(sed 's|^|cc-in/rows/|' cc-in/rows.order) > cc-out/merge.txt 2>&1; echo MERGE=\$?; \
  test -s cc-out/map-merged.tsv || { echo NO-MERGED-MAP; exit 3; }; \
  cp cc-out/map-merged.tsv metadata/NON_MF_SENTENCE_MAP.tsv; \
  \$PY \$S --badges-need-rows > cc-out/write.txt 2>&1; echo WRITE=\$?; \
  \$PY \$S --verify-unconditional --badges-need-rows > cc-out/verify-unconditional-pre.txt 2>&1; \
  \$PY cc-in/register.py cc-out/verify-unconditional-pre.txt cc-out/register-origin.txt metadata/NON_MF_CENSUS_CONDITIONAL_BASELINE.txt ${SHA:0:9} > cc-out/register.txt 2>&1; echo REGISTER=\$?; \
  cp metadata/NON_MF_SENTENCE_CENSUS.tsv metadata/NON_MF_SENTENCE_CENSUS.md metadata/NON_MF_CENSUS_CONDITIONAL_BASELINE.txt cc-out/; \
  \$PY cc-in/worklist.py metadata/NON_MF_SENTENCE_CENSUS.tsv cc-out/WORKLIST.md $TAG > cc-out/worklist.txt 2>&1; echo WORKLIST=\$?; \
  \$PY \$S --check --require-complete --badges-need-rows > cc-out/check.txt 2>&1; echo CHECK=\$?; \
  \$PY \$S --verify-decls --badges-need-rows > cc-out/verify-decls.txt 2>&1; echo VERIFY_DECLS=\$?; \
  \$PY \$S --verify-unconditional --badges-need-rows > cc-out/verify-unconditional.txt 2>&1; echo VERIFY_UNCOND=\$?; \
  echo SENTINEL=done" | tee "$OUT/codes.txt"
rsync -rlc -e "$RSH" "$ALIAS:$L/cc-out/" "$OUT/" || exit 4
echo "outputs: $OUT"; cat "$OUT/merge.txt" "$OUT/register.txt"; head -12 "$OUT/check.txt"; tail -3 "$OUT/verify-unconditional.txt"
cp "$OUT/WORKLIST.md" "$NM/WORKLIST.md"
[ "${1:-}" = "--no-land" ] && { echo "--no-land: nothing installed"; exit 0; }
for c in MERGE WRITE REGISTER VERIFY_DECLS VERIFY_UNCOND; do
  grep -qx "$c=0" "$OUT/codes.txt" || { echo "NOT LANDING: $c is not 0"; exit 5; }
done
for f in $FILES; do
  [ "$(md5 -q "$f")" = "$(git show "$SHA:$f" | md5 -q)" ] || { echo "NOT LANDING: $f in the shared tree differs from origin at ${SHA:0:9} (an unlanded edit?)"; exit 6; }
done
cp "$OUT/map-merged.tsv" metadata/NON_MF_SENTENCE_MAP.tsv
cp "$OUT/NON_MF_CENSUS_CONDITIONAL_BASELINE.txt" metadata/NON_MF_CENSUS_CONDITIONAL_BASELINE.txt
cp "$OUT/NON_MF_SENTENCE_CENSUS.tsv" metadata/NON_MF_SENTENCE_CENSUS.tsv
cp "$OUT/NON_MF_SENTENCE_CENSUS.md" metadata/NON_MF_SENTENCE_CENSUS.md
CHANGED=0; for f in $FILES; do [ "$(md5 -q "$f")" = "$(git show "$SHA:$f" | md5 -q)" ] || CHANGED=1; done
[ $CHANGED -eq 1 ] || { echo "NOTHING TO LAND: the merge reproduces origin"; exit 0; }
COUNTS=$(grep -E '^[a-z]+ +[0-9]+$|^total' "$OUT/check.txt" | awk '{printf "%s%s %s", (NR>1?", ":""), $2, $1}')
MSGF=$NM/msgs/census-merge-$TAG.txt
{ echo "Re-merge the non-MF census rows at ${SHA:0:9}"; echo;
  echo "Merged the lanes' raw rows ($ROWSRC, $(wc -l < "$IN/rows.order") files) into the sentence map over origin ${SHA:0:9} and"
  echo "regenerated the census. $(cat "$OUT/merge.txt" | head -1)"
  echo "Register: $(head -1 "$OUT/register.txt"). --verify-decls: $(head -1 "$OUT/verify-decls.txt")."
  echo "--verify-unconditional: $(tail -1 "$OUT/verify-unconditional.txt")."
  echo "Census: $COUNTS. --check --require-complete stays red on partial and unassigned rows, the true state."; } > "$MSGF"
NM_BASE=$SHA bash "$NM/nmland.sh" go-lemma42 "$MSGF" $FILES 2>&1 | tee "$OUT/land.txt"
RC=${PIPESTATUS[0]}
git fetch -q origin main
NEWSHA=$(grep -oE '^LANDED [0-9a-f]{40}' "$OUT/land.txt" | tail -1 | awk '{print $2}')
if [ $RC -eq 0 ] && git merge-base --is-ancestor "$NEWSHA" origin/main 2>/dev/null; then echo "VERIFIED ON ORIGIN: $NEWSHA"; else echo "LANDING NOT VERIFIED (rc=$RC)"; exit 7; fi
