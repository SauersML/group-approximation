#!/bin/sh
# Palindrome-type transvection census a.phi(a) for rho_k, k in the given list.
# usage: run_pal.sh BIN HALFL OUT k1 k2 ...
BIN=$1; H=$2; OUT=$3; shift 3
for k in "$@"; do
  "$BIN" "$k" "$H" 0 0 4 12 pal | grep -E "SUMMARY|PAIR|NOPAIR|HIT k=[0-9-]* (UNI|REL|TOR|NEG)" | head -60 >> "$OUT"
done
echo DONE >> "$OUT"
