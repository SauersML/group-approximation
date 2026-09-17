#!/bin/sh
run() { echo "== $*"; nice -n 10 timeout 1200 python3 newton.py "$@" 2>&1 | grep -E "CONVERGED|args|STATS"; }
run 5 2 A2 12 21 1,0 1,0 r r
run 5 2 A2 12 22 1,2 1,3 r r
run 5 3 A2 12 23 1,1,0 1,4,0 r r
run 5 3 A2 12 24 1,2,0 1,3,0 r r
run 5 3 A2 12 25 1,0,0 2,0,0 r r
run 5 4 A2 10 26 1,1,0,0 1,4,0,0 r r
run 5 4 A2 10 27 1,2,3,0 1,1,4,0 r r
run 5 5 A2 8 28 1,1,0,0,0 1,4,0,0,0 r r
run 7 3 A2 8 29 1,1,0 1,6,0 r r
run 7 4 A2 8 30 1,2,0,0 1,3,0,0 r r
