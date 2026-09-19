#!/bin/bash
# edge-distinct single-swap search (any start vertex, any ends) on onecyl(1,2,3,20,tw), lengths <= 16
cd "$(dirname "$0")"
for tw in 0 1 2 3 4 5; do
  python3 -c "
from h2 import onecyl; b,c=onecyl(1,2,3,20,$tw); print(len(b)); print(*b); print(*c)" > in_tw$tw.txt
  echo "tw=$tw $(nice -n 10 timeout 1200 ./chain2 0 ${1:-16} < in_tw$tw.txt | head -1)"
  rm -f in_tw$tw.txt
done
