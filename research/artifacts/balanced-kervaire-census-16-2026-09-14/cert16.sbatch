#!/bin/bash -l
#SBATCH -J bc16-certs
#SBATCH -p agsmall
#SBATCH -t 04:00:00
#SBATCH --mem=16G
#SBATCH -c 1
#SBATCH -o /scratch.global/sauer354/hl-balanced-census-16/logs/cert16.%j.log
# After both enumerators: merge, join GAP with tc_verify.py by class id, then export the
# finite-quotient certificates (certs.g, unchanged) and check them letter by letter (verify_certs.py).
cd /scratch.global/sauer354/hl-balanced-census-16 || exit 1
md5sum join16.py joinlines.py certs.g bal.g verify_certs.py census_L1617.txt
for p in chunks16/part_*; do b=$(basename "$p"); echo "$b in=$(wc -l < "$p") gap=$(wc -l < results16/$b 2>/dev/null) tc=$(wc -l < tc16/$b 2>/dev/null)"; done
cat results16/part_* | sort -n -k1,1 > results16_all.txt
cat tc16/part_* | sort -n -k1,1 > tc16_all.txt
echo "=== GAP verdicts"; awk '{ print $5 }' results16_all.txt | sort | uniq -c
echo "=== tc verdicts"; awk '{ print $4 }' tc16_all.txt | sort | uniq -c
echo "=== join"
/usr/bin/python3.12 join16.py census_L1617.txt results16_all.txt tc16_all.txt
echo "=== certificates"
rm -f certs16_out.txt
cat > certs_run16.g <<'EOF'
SizeScreen([4096, 24]);;
Read("certs.g");;
RunCerts("results16_all.txt", "certs16_out.txt", 200000, 8);;
QUIT;
EOF
timeout 13000 /scratch.global/sauer354/solve-kl-counterexample-search/gap-4.13.1/gap -q -o 10g certs_run16.g < /dev/null
/usr/bin/python3.12 joinlines.py certs16_out.txt certs16_joined.txt
echo "nontrivial verdicts: $(awk '$5 ~ /^(FINITE|QUOTIENT|SIMPLE)/' results16_all.txt | wc -l)"
echo "certificate lines: $(wc -l < certs16_joined.txt), FAIL lines: $(grep -c FAIL certs16_joined.txt)"
/usr/bin/python3.12 verify_certs.py certs16_joined.txt
echo "verify exit $?"
md5sum results16_all.txt tc16_all.txt certs16_joined.txt
echo DONE
