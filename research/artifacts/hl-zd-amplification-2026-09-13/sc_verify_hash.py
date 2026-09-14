#!/usr/bin/env python3
"""Second, hash-based C'(1/6) certificate for the seed-3 presentation.

For every length L, index all length-L subwords of the cyclic words r_i and
r_i^-1 by their starting position (relator index, orientation, offset).  A
word occurring at two distinct positions is a piece of length L.  C'(1/6)
requires, for every piece occurrence inside relator i, L < |r_i| / 6.  Two
positions of the same cyclic word coincide as elements of the symmetrized set
only if the relator is a proper power, which is checked separately.
Reads the relator strings from verify3.txt (output of sc_verify.py).
"""
import json, sys
from collections import defaultdict

INV = {"x": "X", "X": "x", "y": "Y", "Y": "y"}

def inverse(w):
    return "".join(INV[a] for a in reversed(w))

def main():
    rep = json.load(open(sys.argv[1]))
    rels = rep["relators"]
    words = []
    for i, r in enumerate(rels):
        n = len(r)
        assert all(not (n % d == 0 and r == r[d:] + r[:d]) for d in range(1, n)), "proper power"
        for o, s in enumerate((r, inverse(r))):
            words.append((i, o, s))
    maxlen = max(len(r) for r in rels)
    worst = {}  # relator index -> longest piece length occurring in it
    L = 1
    while L <= maxlen:
        occ = defaultdict(list)
        for i, o, s in words:
            n = len(s)
            ss = s + s
            for k in range(n):
                if L <= n:
                    occ[ss[k:k + L]].append((i, o, k))
        found = False
        for w, pos in occ.items():
            if len(set(pos)) >= 2:
                found = True
                for (i, o, k) in pos:
                    worst[i] = max(worst.get(i, 0), L)
        if not found:
            break
        L += 1
    out = {
        "lengths": [len(r) for r in rels],
        "longest_piece_in_relator": {str(i): worst.get(i, 0) for i in range(len(rels))},
        "ratios": {str(i): worst.get(i, 0) / len(rels[i]) for i in range(len(rels))},
        "C_prime_one_sixth": all(6 * worst.get(i, 0) < len(rels[i]) for i in range(len(rels))),
        "first_length_with_no_piece": L,
    }
    print(json.dumps(out, indent=1))

if __name__ == "__main__":
    main()
