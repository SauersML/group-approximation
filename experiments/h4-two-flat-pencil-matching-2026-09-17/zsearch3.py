"""Split-pattern candidates, filtered in all three shadows at once.

A split (V_a, V_b) ejection pattern needs a pair loop of winding 0 at p_{a+1} that ejects p_{a+1} (winding lemma).
Here alpha_1 (mode 1) or alpha_2 (mode 2) runs over the zero-winding length-4 commutators [p_i^{+-1}, p_j^{+-1}]
in every order, the other alpha over F-words of length <= LA, and beta_1, beta_3 over words of length <= LB in the
N-letters that act non-trivially in some shadow.  The relation (*) is tested in the Artin action on F_7 in each of
V_0, V_1, V_2 (a necessary condition); survivors go to ejection.py, which applies the exact Garside test.
Run: python3 zsearch3.py MODE LA LB out.jsonl"""
import sys, json, time
from fg import FGEN, NGEN, aut, comp, ID, words, spec

FN = [g[0] for g in FGEN]
EFF3 = [g[0] for g in NGEN if any(g[2][a] for a in range(3))]
A = [{g[0]: (aut(g[2][a]), aut([-x for x in reversed(g[2][a])])) for g in FGEN + NGEN} for a in range(3)]


def act(spec_, a):
    phi = ID
    for n, s in spec_:
        phi = comp(phi, A[a][n][0 if s == 1 else 1])
    return phi


def act3(w):
    return tuple(act(w, a) for a in range(3))


def inv(w):
    return tuple((n, -s) for n, s in reversed(w))


def c3(p, q):
    return tuple(comp(p[a], q[a]) for a in range(3))


def zero(w):
    return all(sum(s for n, s in w if n == x) == 0 for x in FN)


def main(mode, LA, LB, out):
    Z4 = [w for w in words(FN, 4) if len(w) == 4 and zero(w)]
    SA = words(FN, LA)
    B = [()] + words(EFF3, LB)
    BA = [(w, act3(w), act3(inv(w))) for w in B]
    pairs = [(a, b) for a in Z4 for b in SA] if mode == 1 else [(a, b) for a in SA for b in Z4]
    print('Z4', len(Z4), 'pairs', len(pairs), 'betas', len(B), 'EFF3', EFF3, flush=True)
    fo = open(out, 'w'); n = 0; t = time.time()
    for a1, a2 in pairs:
        A1, A2, A12 = act3(a1), act3(a2), act3(a1 + a2)
        lhs = {}
        for w3, b3, b3i in BA:
            lhs.setdefault(c3(b3i, c3(A12, b3)), []).append(w3)
        for w1, b1, b1i in BA:
            k = c3(A1, c3(b1, c3(A2, b1i)))
            for w3 in lhs.get(k, []):
                if w1 == inv(w3):
                    continue
                fo.write(json.dumps({'a1': spec(a1), 'b1': spec(w1), 'a2': spec(a2), 'b3': spec(w3)}) + '\n')
                n += 1
    fo.close()
    print('tuples', n, round(time.time() - t), 's', flush=True)


if __name__ == '__main__':
    main(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4])
