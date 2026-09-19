"""Are the hexagon vertices of genuine Case 1 tuples genuine pure centres?

For the tuple (alpha_1, beta_1, alpha_2, beta_3) the three hexagon vertices u_P (u_01 = 1, u_12 = alpha_1 beta_1,
u_20 = beta_3^-1) are pure centres iff the conjugates
    c_01 = beta_1 alpha_2 beta_1^-1,   c_12 = beta_1^-1 alpha_1 beta_1,   c_20 = beta_3 alpha_1 beta_3^-1
lie in F (u_P A_Y is then adjacent to the third x-vertex; the other two adjacencies hold by construction).
In the shadow V_a the vertex rho_a(u_P) is a centre iff rho_a(c_P) lies in F_Y^(a) (criterion (*) of w10).
Test here: look up rho_0(c_P) among the rho_0-images of the F-words of length <= LF (rho_0 is injective on F), and
confirm a hit f by the exact Garside test nf(c_P) == nf(f) in the H_4 Artin group.
Run: python3 purecent.py records.jsonl [LF]"""
import sys, json
from collections import Counter
from fg import FGEN, aut, words as fwords
from joint import nf, inv
from ejection import elt

FN = [g[0] for g in FGEN]


def main(path, LF=5):
    table = {}
    for w in [()] + fwords(FN, LF):
        e = elt(' '.join(n + ('' if s == 1 else "'") for n, s in w))
        table.setdefault(aut(e[2][0]), e)
    st = Counter()
    for line in open(path):
        r = json.loads(line)
        if r.get('genuine') is False:
            continue
        a1, b1, a2, b3 = (elt(r[k]) for k in ('a1', 'b1', 'a2', 'b3'))
        C = {'01': b1[1] + a2[1] + inv(b1[1]), '12': inv(b1[1]) + a1[1] + b1[1], '20': b3[1] + a1[1] + inv(b3[1])}
        Ci = {'01': b1[2][0] + a2[2][0] + inv(b1[2][0]), '12': inv(b1[2][0]) + a1[2][0] + b1[2][0],
              '20': b3[2][0] + a1[2][0] + inv(b3[2][0])}
        pure = []
        for P in ('01', '12', '20'):
            f = table.get(aut(Ci[P]))
            if f is not None and nf(C[P]) == nf(f[1]):
                pure.append(P + '=' + (f[0] or '1'))
        st['pure centre' if pure else 'NO hexagon-vertex pure centre'] += 1
        if not pure:
            print('NOPURE', r['a1'], '|', r['b1'], '|', r['a2'], '|', r['b3'], flush=True)
        st[tuple(p[:2] for p in pure)] += 1
    for k, v in sorted(st.items(), key=str):
        print(' ', k, v)


if __name__ == '__main__':
    main(sys.argv[1], int(sys.argv[2]) if len(sys.argv) > 2 else 5)
