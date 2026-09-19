"""Which hexagon vertices are centres, per shadow, against the ejecting pairs O_a.

For each genuine record and each shadow V_a: the pairs P whose vertex y_P = rho_a(u_P) delta_0
(u_12 = 1, u_23 = alpha_1 beta_1, u_31 = beta_3^-1) is disjoint from all three x-arcs (curver), next to O_a
(pairs whose d_1-region misses p_{a+1}, empty if p_{a+1} is in the triple region).  Tests:
  (V) every P in O_a gives a centre y_P in V_a;   (J) a vertex y_P is a centre in every shadow (joint for all).
Run: PYTHONPATH=<curver>:<realalg> python3 vcent.py records.jsonl  (records of joint.py or ejection.py)"""
import os, sys, json
from collections import Counter
from joint import HERE
sys.path.insert(0, os.path.join(HERE, '..', '..', 'lib'))
import a6
from centres import parse, cat, xinv


def vertex_centres(rec):
    a1, b1, a2, b3 = (parse(rec[k]) for k in ('a1', 'b1', 'a2', 'b3'))
    gx = [([], [[], [], []]), a1, cat(a1, b1, a2)]
    U = {'01': ([], [[], [], []]), '12': cat(a1, b1), '20': xinv(b3)}
    out = {}
    for a in range(3):
        xs = [a6.xarc(g[1][a]) for g in gx]
        out[a] = sorted(P for P, u in U.items() if all(a6.adj(a6.spider(u[1][a]), x) for x in xs))
    return out


def main(path):
    st = Counter()
    for line in open(path):
        rec = json.loads(line)
        if rec.get('genuine') is False:
            continue
        if 'O' in rec:
            O = {int(a): v for a, v in rec['O'].items()}
        else:
            O = {a: ([P for P in ('01', '12', '20') if a + 3 not in rec['V%d' % a][P]]
                     if a + 3 not in rec['V%d' % a]['all'] else []) for a in range(3)}
        vc = vertex_centres(rec)
        V = all(set(O[a] or []) <= set(vc[a]) for a in range(3))
        J = bool(set(vc[0]) & set(vc[1]) & set(vc[2]))
        key = ('V' if V else 'notV', 'J' if J else 'notJ',
               tuple((a, tuple(O[a] or []), tuple(vc[a])) for a in range(3)))
        st[key[:2]] += 1
        if not V or not J:
            print('CASE', key, rec['a1'], '|', rec['b1'], '|', rec['a2'], '|', rec['b3'], flush=True)
    for k, v in sorted(st.items()):
        print(' ', k, v)


if __name__ == '__main__':
    main(sys.argv[1])
