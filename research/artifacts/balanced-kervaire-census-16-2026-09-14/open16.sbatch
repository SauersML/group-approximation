#!/bin/bash -l
#SBATCH -J bc16-open
#SBATCH -p agsmall
#SBATCH -t 12:00:00
#SBATCH --mem=32G
#SBATCH -c 1
#SBATCH -o /scratch.global/sauer354/hl-balanced-census-16/logs/open16.%j.log
# Follow-up on the L = 16, 17 classes the first pass left OPEN:
#   GAP bal.g Classify with 20000000 cosets, index <= 12, and 16 more simple targets;
#   tc_verify.py with 5000000 cosets as the second enumerator;
#   certificate export (certs.g + the same targets) and letter-by-letter verification.
cd /scratch.global/sauer354/hl-balanced-census-16 || exit 1
GAP=/scratch.global/sauer354/solve-kl-counterexample-search/gap-4.13.1/gap
md5sum bal.g certs.g open16_targets.g tc_verify.py verify_certs.py joinlines.py
cat results16/part_* | awk '$5 == "OPEN"' | sort -n -k1,1 > open16_in.txt
echo "OPEN classes: $(wc -l < open16_in.txt)"
md5sum open16_in.txt
rm -f open16_out.txt open16_tc.txt open16_certs_out.txt
cat > run_open16.g <<'EOF'
Read("bal.g");;
Read("open16_targets.g");;
RunBal("open16_in.txt", "open16_out.txt", 20000000, 12);;
QUIT;
EOF
timeout 25000 $GAP -q -o 30g run_open16.g < /dev/null
echo "=== GAP follow-up verdicts"; awk '{ print $5 }' open16_out.txt | sort | uniq -c
awk '$5 != "TRIVIAL"' open16_out.txt
echo "=== second enumerator"
timeout 10000 /usr/bin/python3.12 tc_verify.py open16_in.txt open16_tc.txt 5000000
awk '{ print $4 }' open16_tc.txt | sort | uniq -c
echo "=== certificates"
cat > run_open16_certs.g <<'EOF'
SizeScreen([4096, 24]);;
Read("certs.g");;
Read("open16_targets.g");;
RunCerts("open16_out.txt", "open16_certs_out.txt", 20000000, 12);;
QUIT;
EOF
timeout 7000 $GAP -q -o 30g run_open16_certs.g < /dev/null
/usr/bin/python3.12 joinlines.py open16_certs_out.txt open16_certs_joined.txt
echo "nontrivial verdicts: $(awk '$5 ~ /^(FINITE|QUOTIENT|SIMPLE)/' open16_out.txt | wc -l)"
echo "certificate lines: $(wc -l < open16_certs_joined.txt), FAIL lines: $(grep -c FAIL open16_certs_joined.txt)"
/usr/bin/python3.12 verify_certs.py open16_certs_joined.txt
echo "verify exit $?"
md5sum open16_out.txt open16_tc.txt open16_certs_joined.txt
echo DONE
