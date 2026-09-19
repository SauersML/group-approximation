#!/bin/bash
# 4012, a2b1c1: Wentges-smoothed phase 1 with warm centre (round-3 master dual) on the unpruned round-3 columns;
# later rounds reload the columns with reduced cost <= RCEPS at the final master dual (rcprune.py)
cd "$(dirname "$0")"
TL=${TL:-700} CG_ALPHA=${A:-0.3} WARM=1 RCEPS=${RCEPS:-0.4} CG_CENTER=${C0:-v2_a2b1c1_4012_3.json} PREV=${P0:-v2_a2b1c1_4012_3.json} K0=${K:-5} exec ./vchain4.sh 4012 '{"a": "ab", "b": "bbac", "c": "abb"}' 2 a2b1c1 6
