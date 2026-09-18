R=results.jsonl
for g in A2 A3 B3 H3; do nice -n 10 timeout 1200 python3 search2.py $g 2,2,2,2 2 4 $R; done
nice -n 10 timeout 1200 python3 search2.py B4 1,1,1,1 1 3 $R
nice -n 10 timeout 1200 python3 search2.py H4 1,1,1,1 1 3 $R
