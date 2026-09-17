"""Degree-width tables for monomial doubling in Thompson's F.

Input: files of lines "D L <json>" produced by width_degree_grid.sh (exact min-cut values of
Lambda_S(D, L) = min |S Y| / |Y| over nonempty Y in M_(D, L)).

Checks
  (W)  proved: Lambda_S(D, L) = Lambda_S(L-1, L) for every D >= L-1
       (research/thompson-f-monomial-doubling-width-bounds-degree-proof.md).
  (U)  proved: Lambda_S(D, L) >= Lambda_S(min(D, L-1)) with Lambda_S(n) the main-branch exact table.
  (Sharp) empirical: Lambda_S(D, L) = Lambda_S(min(D, L - r)), r = largest letter of S.

usage: python3 width_degree_law.py x2|s24|s35 file ...
"""
import json
import sys
from fractions import Fraction as Fr

# Exact unrestricted values Lambda_S(n), n = 1..12, research/artifacts/thompson-f-monomial-doubling-2026-09-13.md
MAIN = {
    'x2': [2.25, 2.0, 1.8235, 1.7290, 1.6696, 1.6184, 1.5821, 1.5550, 1.5297, 1.5099, 1.4931, 1.4782],
    's24': [3.5, 3.0, 2.6471, 2.4579, 2.3392, 2.2368, 2.1641, 2.1100, 2.0595, 2.0198, 1.9831, 1.9476],
    's35': [5.6, 4.5, 3.9571, 3.6147, 3.3725, 3.1966, 3.0654, 2.9526, 2.8612, 2.7869, 2.7226, 2.6676],
}
R = {'x2': 2, 's24': 2, 's35': 3}


def main():
    name = sys.argv[1]
    r = R[name]
    rows = {}
    for path in sys.argv[2:]:
        for line in open(path):
            p = line.split(' ', 2)
            if len(p) < 3:
                continue
            j = json.loads(p[2])
            rows[(int(p[0]), int(p[1]))] = Fr(j['min_ratio_num'], j['min_ratio_den'])
    Ds = sorted({d for d, _ in rows})
    Ls = sorted({l for _, l in rows})
    print('rows D, columns L =', Ls)
    for D in Ds:
        print('%2d ' % D + ' '.join('%7.4f' % float(rows[(D, L)]) if (D, L) in rows else '   -   ' for L in Ls))
    bad_w = bad_u = 0
    sharp_bad = []
    sharp_ok = 0
    for (D, L), v in sorted(rows.items()):
        if L >= 2 and D >= L - 1 and (L - 1, L) in rows and rows[(L - 1, L)] != v:
            bad_w += 1
            print('W violation', D, L)
        k = min(D, L - 1)
        if 1 <= k <= 12 and float(v) < MAIN[name][k - 1] - 1e-4:
            bad_u += 1
            print('U violation', D, L)
        n = min(D, L - r)
        if n >= 1 and n <= 12:
            if abs(float(v) - MAIN[name][n - 1]) < 1e-4:
                sharp_ok += 1
            else:
                sharp_bad.append((D, L, float(v), MAIN[name][n - 1]))
    print('W violations', bad_w, '| U violations', bad_u)
    print('sharp law matches', sharp_ok, 'mismatches', len(sharp_bad))
    for b in sharp_bad:
        print('  mismatch D=%d L=%d value %.4f law %.4f' % b)


if __name__ == '__main__':
    main()
