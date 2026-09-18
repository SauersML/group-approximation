R=results2.jsonl
for g in B3 H3 A3; do nice -n 10 timeout 1200 python3 search2.py $g 2,2,2,2 2 4 $R 4 5; done
