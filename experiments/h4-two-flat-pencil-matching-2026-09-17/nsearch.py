"""Non-trivial Case 1 tuples: does any solution of (*) lie outside the commuting family?

(*)  beta_3^-1 (alpha_1 alpha_2) beta_3 = alpha_1 beta_1 alpha_2 beta_1^-1,  alpha_i in F, beta_i in N.
Commuting (trivial) family: beta_1 alpha_2 = alpha_2 beta_1 and beta_3 (alpha_1 alpha_2) = (alpha_1 alpha_2) beta_3;
every such tuple has the genuine pure centre u = 1.  This scan solves (*) in the Artin action on F_7 of all three
I_2(5) shadows at once (a necessary condition for (*) in P) with alpha_i over F-words of length <= LA and beta_i
over words of length <= LB in the 9 N-letters acting non-trivially in some shadow, and prints every solution that
is NOT in the commuting family at the shadow level, with the exact Garside verdict on (*).
Run: python3 nsearch.py LA LB"""
import sys, time
from collections import Counter
from zsearch3 import FN, EFF3, act3, inv, c3
from fg import words, spec
from ejection import elt, genuine


def main(LA, LB):
    SA = [()] + words(FN, LA)
    B = [()] + words(EFF3, LB)
    BA = [(w, act3(w), act3(inv(w))) for w in B]
    FA = {a: act3(a) for a in SA}
    st = Counter(); t = time.time()
    for a1 in SA:
        for a2 in SA:
            A1, A2 = FA[a1], FA[a2]
            A12 = c3(A1, A2)
            if all(x == tuple((k,) for k in range(1, 8)) for x in A12):
                continue                                   # alpha_1 alpha_2 = 1
            lhs = {}
            for w3, b3, b3i in BA:
                lhs.setdefault(c3(b3i, c3(A12, b3)), []).append((w3, c3(b3i, c3(A12, b3)) == A12))
            for w1, b1, b1i in BA:
                conj = c3(b1, c3(A2, b1i))
                k = c3(A1, conj)
                for w3, fix3 in lhs.get(k, []):
                    if w1 == inv(w3):
                        continue
                    st['shadow solutions'] += 1
                    if conj == A2 and fix3:
                        st['commuting'] += 1; continue
                    g = genuine(*(elt(spec(x)) for x in (a1, w1, a2, w3)))
                    st['non-commuting, genuine' if g else 'non-commuting, not genuine'] += 1
                    print('NC', g, spec(a1), '|', spec(w1), '|', spec(a2), '|', spec(w3), flush=True)
    print(dict(st), round(time.time() - t), 's', flush=True)


if __name__ == '__main__':
    main(int(sys.argv[1]), int(sys.argv[2]))
