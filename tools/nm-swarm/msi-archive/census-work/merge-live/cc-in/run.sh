# run.sh <live dir> <projects dir> <sha9> <tag>     (detached on the node; stdout is cc-out/codes.txt)
L=$1; P=$2; SHA9=$3; TAG=$4
cd "$L" || { echo NO-LIVE-DIR; echo SENTINEL=done; exit 2; }
PY=$P/params-venv/bin/python3; S=scripts/sentence_census.py; rm -rf scripts/__pycache__
cp metadata/NON_MF_SENTENCE_MAP.tsv cc-out/map-origin.tsv; cp metadata/NON_MF_CENSUS_CONDITIONAL_BASELINE.txt cc-out/register-origin.txt
$PY $S --badges-need-rows --json > cc-out/records.json 2> cc-out/json.err; echo JSON=$?
ROWS_TEX=cc-in/tex-rows.tex CLONES=$P/cc_clones $PY cc-in/merge_rows.py cc-out/records.json cc-out/map-origin.tsv cc-in/green-md5.txt cc-in/landed-shas.txt "$L" \
  cc-out/map-merged.tsv cc-out/merge-report.tsv cc-out/existing-audit.tsv "$SHA9" cc-in/overrides.tsv $(sed 's|^|cc-in/rows/|' cc-in/rows.order) > cc-out/merge.txt 2>&1; echo MERGE=$?
if [ ! -s cc-out/map-merged.tsv ]; then echo NO-MERGED-MAP; echo SENTINEL=done; exit 3; fi
cp cc-out/map-merged.tsv metadata/NON_MF_SENTENCE_MAP.tsv
$PY $S --badges-need-rows > cc-out/write.txt 2>&1; echo WRITE=$?
$PY $S --verify-unconditional --badges-need-rows > cc-out/verify-unconditional-pre.txt 2>&1
$PY cc-in/register.py cc-out/verify-unconditional-pre.txt cc-out/register-origin.txt metadata/NON_MF_CENSUS_CONDITIONAL_BASELINE.txt "$SHA9" > cc-out/register.txt 2>&1; echo REGISTER=$?
cp metadata/NON_MF_SENTENCE_CENSUS.tsv metadata/NON_MF_SENTENCE_CENSUS.md metadata/NON_MF_CENSUS_CONDITIONAL_BASELINE.txt cc-out/
$PY cc-in/worklist.py metadata/NON_MF_SENTENCE_CENSUS.tsv cc-out/WORKLIST.md "$TAG" cc-in/tex-rows.tex non_mf_groups_exist.tex > cc-out/worklist.txt 2>&1; echo WORKLIST=$?
$PY $S --check --require-complete --badges-need-rows > cc-out/check.txt 2>&1; echo CHECK=$?
$PY $S --verify-decls --badges-need-rows > cc-out/verify-decls.txt 2>&1; echo VERIFY_DECLS=$?
$PY $S --verify-unconditional --badges-need-rows > cc-out/verify-unconditional.txt 2>&1; echo VERIFY_UNCOND=$?
# Every finding with its detail, accepted ones included: the verifier prints details only for findings the register
# lacks, and a justification must describe the finding it licenses.  Informational; never gates the landing.
: > cc-out/empty-register.txt
$PY $S --verify-unconditional --badges-need-rows --conditional-baseline cc-out/empty-register.txt > cc-out/verify-unconditional-all.txt 2>&1; echo VERIFY_ALL=$?
echo SENTINEL=done
