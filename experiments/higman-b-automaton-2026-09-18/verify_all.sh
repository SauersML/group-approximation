#!/bin/sh
# Recompute the levels of Bbar_e with levels_ck.py in a fresh directory ($2) up to the first stable
# level, verify every level exactly with verify.py against the previous one, and compare the last
# tables with ck<e>/L<K>.npz (the files rel.py and qbexport.py read).
# usage: sh verify_all.sh e workdir
e=$1; W=$2; H=$(cd "$(dirname "$0")" && pwd)
rm -rf "$W/ck$e"; mkdir -p "$W"; cd "$W" || exit 1
last=0
for k in 1 2 3 4 5; do
  python3 "$H/levels_ck.py" $e $k 100000 | tail -1
  [ -f ck$e/L$k.npz ] || break
  cp ck$e/L$k.npz ck$e/v$k.npz; last=$k
  if [ $k = 1 ]; then python3 "$H/verify.py" $e 1 ck$e/v1.npz; else python3 "$H/verify.py" $e $k ck$e/v$k.npz ck$e/v$((k-1)).npz; fi
done
python3 -c "
import numpy as np, os
f='$H/ck$e/L$last.npz'
if os.path.exists(f):
    a=np.load('ck$e/v$last.npz'); b=np.load(f)
    print('e=$e: fresh level-$last tables equal ck$e/L$last.npz:', all(np.array_equal(a[x],b[x]) for x in ('Rb','Rd','rows')))"
rm -rf "$W/ck$e"
