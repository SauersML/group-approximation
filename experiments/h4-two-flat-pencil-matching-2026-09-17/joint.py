"""Genuine Case 1 tuples and their ejection pattern in two I_2(5) shadows at once.

Tuples (alpha_1, alpha_2; beta_1, beta_3): alpha words in the 3 F-meridians, beta words in the 12 non-Z
meridians of A_x (gens.py), with the Case 1 relation  beta_3^-1 (alpha_1 alpha_2) beta_3 = alpha_1 beta_1 alpha_2 beta_1^-1
checked EXACTLY in the H_4 Artin group (w4-042's Garside engine, garside.py of
experiments/h4-artin-complex-6cycles-2026-09-17): hash join on left normal forms.  Nondegenerate: alpha_1 alpha_2 != 1
(F is free on the three meridians) and beta_1 beta_3 != 1 (Garside).
For every genuine tuple and shadow V_a (a = 0, 1, 2), the x-arcs rho_a(g_i)(s_7), g = 1, alpha_1, alpha_1 beta_1 alpha_2,
are placed with arcs.py (ARCS_N = 7) and the d_1-region punctures of each pair and of the triple are recorded.
Cluster point of V_a = p_{a+1}; arcs.py puncture of p_k is k + 2 in every shadow (strands q q q p1 p2 p3 t).
Run: PYTHONPATH=<curver>:<realalg> python3 joint.py LF LN [out.jsonl]"""
import os, sys, itertools, json, pickle, time
os.environ.setdefault('ARCS_N', '7')
HERE = os.path.dirname(os.path.abspath(__file__))
LIB = os.path.join(HERE, '..', '..', 'lib')
sys.path.insert(0, LIB)
sys.setrecursionlimit(20000)
from garside import Coxeter, Artin

GART = Artin(Coxeter(4, {(0, 1): 3, (1, 2): 3, (2, 3): 5}))
CACHE = os.path.join(HERE, 'gens_cache.pkl')


def inv(w):
    return [-g for g in reversed(w)]


def load_gens():
    """[(name, h4 word, [img_V0, img_V1, img_V2])] for F and for N (curver-convention 7-strand words)."""
    if os.path.exists(CACHE):
        with open(CACHE, 'rb') as f:
            return pickle.load(f)
    import gens
    from mono import name
    out = []
    for dct in (gens.FY, gens.NZ):
        L = []
        for k, w in sorted(dct.items(), key=lambda kv: (len(kv[1]), kv[0])):
            L.append((name(k), w, [gens.free_reduce(gens.rho(a, w)) for a in range(3)]))
        out.append(L)
    with open(CACHE, 'wb') as f:
        pickle.dump(out, f)
    return out


FGEN, NGEN = load_gens()


def words(G, L):
    """freely reduced words of length 1..L in G: (spec, h4 word, [imgs])"""
    let = [(i, 1) for i in range(len(G))] + [(i, -1) for i in range(len(G))]
    out = []
    for n in range(1, L + 1):
        for w in itertools.product(let, repeat=n):
            if any(w[k][0] == w[k + 1][0] and w[k][1] == -w[k + 1][1] for k in range(n - 1)):
                continue
            h, im = [], [[], [], []]
            for i, s in w:
                h += G[i][1] if s == 1 else inv(G[i][1])
                for a in range(3):
                    im[a] += G[i][2][a] if s == 1 else inv(G[i][2][a])
            out.append((w, h, im))
    return out


def nf(word):
    return GART.word(word)


def tuples(LF, LN):
    FA, NB = words(FGEN, LF), words(NGEN, LN)
    t = time.time()
    lhs = {}
    for i1, i2 in itertools.product(range(len(FA)), repeat=2):
        a12 = FA[i1][1] + FA[i2][1]
        for k3, b3 in enumerate(NB):
            lhs.setdefault((i1, i2, nf(inv(b3[1]) + a12 + b3[1])), []).append(k3)
    print('lhs', len(lhs), 'keys', round(time.time() - t), 's', flush=True)
    for i1, k1, i2 in itertools.product(range(len(FA)), range(len(NB)), range(len(FA))):
        b1 = NB[k1][1]
        key = (i1, i2, nf(FA[i1][1] + b1 + FA[i2][1] + inv(b1)))
        for k3 in lhs.get(key, []):
            if FA[i1][0] == tuple((i, -s) for i, s in reversed(FA[i2][0])):
                continue          # alpha_1 alpha_2 = 1
            if nf(b1 + NB[k3][1]) == GART.one:
                continue          # beta_1 beta_3 = 1
            yield FA[i1], NB[k1], FA[i2], NB[k3]


import arcs as AR
from search import outer

PAIRS = ((0, 1), (1, 2), (2, 0))


def regions(a, a1, b1, a2):
    """d_1-region punctures of the pairs and of the triple in shadow V_a (None if undetermined)."""
    gx = [[], a1[2][a], a1[2][a] + b1[2][a] + a2[2][a]]
    items = [(g, AR.xarc(g)) for g in gx]
    if any(it[1].end != ('P', 6) for it in items):
        return None
    R = {p: outer([items[p[0]], items[p[1]]]) for p in PAIRS}
    R['all'] = outer(items)
    if any(r is None for r in R.values()):
        return None
    return R


def spec(w, names):
    return ' '.join(names[i] + ('' if s == 1 else "'") for i, s in w)


def main(LF=1, LN=1, out=None):
    FN = [g[0] for g in FGEN]; NN = [g[0] for g in NGEN]
    fo = open(out, 'w') if out else None
    from collections import Counter
    st = Counter()
    for a1, b1, a2, b3 in tuples(LF, LN):
        st['tuples'] += 1
        rec = {'a1': spec(a1[0], FN), 'b1': spec(b1[0], NN), 'a2': spec(a2[0], FN), 'b3': spec(b3[0], NN)}
        ej = []
        for a in range(3):
            R = regions(a, a1, b1, a2)
            if R is None:
                ej.append(None); continue
            pc = a + 3
            rec['V%d' % a] = {('%d%d' % p if p != 'all' else 'all'): sorted(r) for p, r in R.items()}
            ej.append(pc not in R['all'])
        rec['ejected'] = ej
        st[tuple(ej)] += 1
        for a, b in ((0, 1), (0, 2), (1, 2)):
            if ej[a] and ej[b]:
                Ra, Rb = rec['V%d' % a], rec['V%d' % b]
                c, d = a + 3, b + 3
                com = [P for P in ('01', '12', '20') if not {c, d} & set(Ra[P]) and not {c, d} & set(Rb[P])]
                oa = [P for P in ('01', '12', '20') if c not in Ra[P]]
                ob = [P for P in ('01', '12', '20') if d not in Rb[P]]
                kind = 'common' if com else ('overlap' if set(oa) & set(ob) else 'split')
                rec.setdefault('pairs', {})['%d%d' % (a, b)] = [kind, oa, ob]
                st[('V%dV%d' % (a, b), kind)] += 1
                if kind != 'common':
                    print('NONCOMMON', a, b, rec, flush=True)
        same = all(rec.get('V%d' % a) == rec.get('V0') for a in range(3))
        st['same-regions' if same else 'diff-regions'] += 1
        if fo:
            fo.write(json.dumps(rec) + '\n'); fo.flush()
    for k, v in sorted(st.items(), key=str):
        print(' ', k, v)


if __name__ == '__main__':
    a = sys.argv[1:]
    main(int(a[0]), int(a[1]), a[2] if len(a) > 2 else None)
