#!/bin/sh
# Reproduces hidden15.out: the hidden degree-15 relations of Gamma^A2_5 in eigen-coordinates.
# Usage: sh run_hidden15.sh WORKDIR 2>/dev/null  (stderr is per-degree progress; single-threaded, about 5 minutes)
set -e
H=$(cd "$(dirname "$0")" && pwd); W=${1:-/tmp/hidden15}; mkdir -p "$W"; cd "$W"
g++ -O2 -o hsb "$H/hidden_sb.cpp"; g++ -O2 -DPP=3 -o hsb3 "$H/hidden_sb.cpp"
python3 "$H/kassel_lift.py" kas.vec
echo "### 1. graded reference J+Z5 (initial forms of the nine relators plus (XY-YX)^5 per edge)"
./hsb 15 3 3 3 1 JZ | grep -E 'hilb|H\('
echo "### 2. lowest forms of all torus-eigencomponents of the relators (LOWONLY)"
LOWONLY=1 ./hsb 15 15 15 15 0 low | grep -E 'hilb|H\('
echo "### 3. group mode: all relators with all tails, eigen-coordinates; hidden = lead normal for J+Z5"
./hsb 15 15 15 15 0 G kas.vec JZ.leads | grep -E 'hilb|H\(|jumps|hidden|^test'
echo "### 4. K, C1, C2, K' and the three hidden elements, reduced modulo J+Z5; linear relations"
python3 - <<'EOF'
L = open('kas.vec').read().split('\n'); n = int(L[0]); i = 1; V = []
for _ in range(n):
    m = int(L[i]); i += 1; V.append(L[i:i + m]); i += m
Hd = open('G.hidden').read().split('\n'); i = 0
while i < len(Hd) and Hd[i].strip():
    nm, m = Hd[i].split(); m = int(m); i += 1; V.append(Hd[i:i + m]); i += m
with open('kh.vec', 'w') as f:
    f.write('%d\n' % len(V))
    for v in V: f.write('%d\n' % len(v)); f.write('\n'.join(v) + '\n')
EOF
./hsb 15 3 3 3 1 JZb kh.vec | grep -E '^test' | sed 's/hidden uses://'
python3 "$H/nfsolve.py" JZb.nf K,C1,C2,Kp,h1,h2,h3
echo "### 5. provenance chain of the hidden elements (basis elements 0-35)"
awk '{printf "#%d %s\n", NR-1, $0}' G.leads | sed -n '1,36p'
echo "### 6. edge-selective tails (cap 3 = initial form only; Z5 added), degree 15"
for t in "15 3 3" "3 15 3" "3 3 15" "15 15 3" "15 3 15" "3 15 15" "13 13 13"; do
  set -- $t; echo "Tab=$1 Tbc=$2 Tac=$3"; ./hsb 15 $1 $2 $3 1 sel kas.vec JZ.leads | grep -E 'hilb|H\(|^test' | sed 's/hidden uses:.*//'
done
echo "### 7. single-edge tails at degree 11: the vertex obstructions"
for t in "11 3 3" "3 11 3" "3 3 11" "11 11 3" "11 11 11"; do
  set -- $t; echo "Tab=$1 Tbc=$2 Tac=$3"; ./hsb 11 $1 $2 $3 1 e11 - JZ.leads | grep -E 'jumps|hidden'
done
echo "### 8. calibration p=3 (outside the claim): group vs J+Z3"
./hsb3 13 3 3 3 1 p3J | grep -E 'hilb|H\('
./hsb3 13 13 13 13 0 p3G | grep -E 'hilb|H\('
