#!/bin/sh
# Relative (O) test on the w19 j=1 law-8 order-12 Cayley level, s <= 5
# overfold seeds, split over 4 processes by the first seed of P.
cd "$(dirname "$0")"
for p in 0 1 2 3; do
  nice -n 5 ./rel inst12j1_law8.txt 5 0 fast $p 4 > law8_s5_p$p.txt &
done
wait
