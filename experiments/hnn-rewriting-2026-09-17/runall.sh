#!/bin/sh
# Certificate search runs; each run single-threaded, bounded rules.
cd "$(dirname "$0")"
mkdir -p out
for spec in "basilicaHNN aAtT wreath" "basilicaHNN AatT wreath" "basilicaHNN tTaA wreath" "basilicaHNN aAtT shortlex" \
            "grigorchukHNN aAbBcCdDtT wreath" "grigorchukHNN tTaAbBcCdD wreath" "grigorchukHNN aAbBcCdDtT shortlex" \
            ; do
  set -- $spec
  f=out/$1-$2-$3.txt
  python3 pres.py $1 $2 $3 3000 30 | nice -n 10 timeout 300 ./kb > $f 2> $f.log
  echo "$spec: $(head -1 $f) $(tail -1 $f.log)"
done
