"""Genuine Case 1 tuples with a zero-winding pair loop (the only source of split ejection patterns).

alpha_1 (mode 1) or alpha_2 (mode 2) runs over the freely reduced F-words of length 4 with zero exponent sum in
every letter; the other alpha over F-words of length <= LA; beta_1, beta_3 over words of length <= LB in the
N-letters with non-trivial action on F (fg.EFF).  Relation (*) tested exactly with fg.py.  Output: jsonl in the
record format of joint.py (a1, b1, a2, b3), to be fed to ejection.py.
Run: python3 zsearch.py MODE LA LB out.jsonl"""
import sys, json, itertools, time
from fg import *

FN = [g[0] for g in FGEN]


def zero(w):
    return all(sum(s for n, s in w if n == x) == 0 for x in FN)


def main(mode, LA, LB, out):
    Z4 = [w for w in words(FN, 4) if len(w) == 4 and zero(w)]
    SA = words(FN, LA)
    B = words(EFF, LB)
    BA = [(w, nword(w), nword_inv(w)) for w in B]
    pairs = [(a, b) for a in Z4 for b in SA] if mode == 1 else [(a, b) for a in SA for b in Z4]
    print('Z4', len(Z4), 'pairs', len(pairs), 'betas', len(B), flush=True)
    fo = open(out, 'w'); n = 0; t = time.time()
    for a1, a2 in pairs:
        A1, A2, A12 = fword(a1), fword(a2), fword(a1 + a2)
        lhs = {}
        for w3, b3, b3i in BA:
            lhs.setdefault(comp(b3i, comp(A12, b3)), []).append(w3)
        for w1, b1, b1i in BA:
            k = comp(A1, comp(b1, comp(A2, b1i)))
            for w3 in lhs.get(k, []):
                if w1 == tuple((x, -s) for x, s in reversed(w3)):
                    continue      # beta_1 beta_3 = 1 in the free word sense; checked properly below
                fo.write(json.dumps({'a1': spec(a1), 'b1': spec(w1), 'a2': spec(a2), 'b3': spec(w3)}) + '\n')
                n += 1
    fo.close()
    print('tuples', n, round(time.time() - t), 's', flush=True)


if __name__ == '__main__':
    main(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4])
