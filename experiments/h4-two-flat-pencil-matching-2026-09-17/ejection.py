"""Ejection pattern of Case 1 records (a1, b1, a2, b3 specs) in the three I_2(5) shadows, as in joint.py.

The x-arcs s_7, rho_a(alpha_1)s_7, rho_a(alpha_1 beta_1 alpha_2)s_7 are placed in each shadow V_a (arcs.py) and
p_{a+1} (arcs.py puncture a+3) is ejected in V_a iff a+3 is not in R_a(x_1 u x_2 u x_3); O_a = pairs ejecting it.
Records also carry the Garside verdict of (*) and of beta_1 beta_3 != 1 (field 'genuine'), and the winding vectors
of the pair loops (exponent sums; pure braids act trivially on H_1 of the punctured disc, so they add).
Run: PYTHONPATH=<curver>:<realalg> python3 ejection.py in.jsonl out.jsonl"""
import sys, json
from collections import Counter
from joint import FGEN, NGEN, inv, regions, nf, GART

BY = {g[0]: g for g in FGEN + NGEN}
FN = [g[0] for g in FGEN]


def elt(s):
    h, im = [], [[], [], []]
    for t in s.split():
        g = BY[t.rstrip("'")]; e = -1 if t.endswith("'") else 1
        h += g[1] if e == 1 else inv(g[1])
        for a in range(3):
            im[a] += g[2][a] if e == 1 else inv(g[2][a])
    return (s, h, im)


def wind(s):
    c = Counter()
    for t in s.split():
        c[t.rstrip("'")] += -1 if t.endswith("'") else 1
    return [c[n] for n in ('p1', 'p2', 'p3')]


def genuine(a1, b1, a2, b3):
    L = nf(inv(b3[1]) + a1[1] + a2[1] + b3[1]); R = nf(a1[1] + b1[1] + a2[1] + inv(b1[1]))
    return L == R and nf(b1[1] + b3[1]) != GART.one


def classify(rec):
    a1, b1, a2, b3 = (elt(rec[k]) for k in ('a1', 'b1', 'a2', 'b3'))
    rec['genuine'] = genuine(a1, b1, a2, b3)
    if not rec['genuine']:
        return rec
    w1, w2 = wind(rec['a1']), wind(rec['a2'])
    rec['wind'] = {'01': w1, '12': w2, '20': [-(x + y) for x, y in zip(w1, w2)]}
    O = {}
    for a in range(3):
        R = regions(a, a1, b1, a2)
        if R is None:
            O[a] = None; continue
        rec['V%d' % a] = {('%d%d' % p if p != 'all' else 'all'): sorted(r) for p, r in R.items()}
        c = a + 3
        O[a] = [('%d%d' % p) for p in ((0, 1), (1, 2), (2, 0)) if c not in R[p]] if c not in R['all'] else []
    rec['O'] = O
    pat = {}
    for a, b in ((0, 1), (0, 2), (1, 2)):
        if O[a] and O[b]:
            pat['%d%d' % (a, b)] = 'common' if set(O[a]) & set(O[b]) else 'split'
    rec['pairs'] = pat
    return rec


def main(inp, out):
    st = Counter(); fo = open(out, 'w')
    for line in open(inp):
        rec = classify(json.loads(line))
        if not rec['genuine']:
            st['not genuine'] += 1; continue
        if any(v is None for v in rec['O'].values()):
            st['undetermined'] += 1
        st['ejected V' + ''.join(str(a) for a in range(3) if rec['O'][a])] += 1
        for a, O in rec['O'].items():
            if O:
                st[('V%d' % a, 'O-size', len(O), 'zero-winding' if rec['wind']['01'][a] == rec['wind']['12'][a] == 0 else 'wind')] += 1
        for ab, kd in rec['pairs'].items():
            st[('V' + ab, kd)] += 1
            if kd == 'split':
                print('SPLIT', json.dumps(rec), flush=True)
        fo.write(json.dumps(rec) + '\n'); fo.flush()
    for k, v in sorted(st.items(), key=str):
        print(' ', k, v)


if __name__ == '__main__':
    main(sys.argv[1], sys.argv[2])
