"""deep versus law for general nested pairs A <= B <= F(a,b).

Calibration test for fpbs-mal-overfold-merges-never-help: does the exchange
deep(Q) = law(Q) hold for chains other than L_{j+1} = phi(L_j) <= L_j?

Words: lowercase letter = generator, uppercase = inverse ("baBB" = b a b^-1 b^-1).
Gamma_A(Q), Gamma_B(Q): Stallings folds of Q with A- resp. B-generator loops.
m: Gamma_A(Q) -> Gamma_B(Q) canonical.  Seeds: pairs of distinct vertices of
Gamma_A(Q) over the same point of Q (deep); lawful seeds: pairs with equal
m-image (law).  deep/law = least number of seeds whose fold closure contains
ker(m).  Exact by BFS over distinct partitions, capped at maxk.

Usage: python3 chains.py NAME n trials seed maxk
       NAME in CHAINS below; n = |Q|; transitive random Q.
"""
import random
import sys
sys.path.insert(0, __file__.rsplit('/', 2)[0] + '/fpbs-depth-overfolding-2026-09-17')
from foldlib import Graph, gamma, closure, contains_kernel, reduce  # noqa: E402


def W(s):
    return reduce([(c.lower(), 1 if c.islower() else -1) for c in s])


# name: (A generators, B generators, comment)
CHAINS = {
    # the Gamma_mal chain itself, j = 1 (sanity: must give deep = law)
    'mal1': (['a', 'baBBabbABbbAB'], ['a', 'baBB'], 'phi(L_1) < L_1'),
    # B = L_1 = <a,t>, t = baBB; A = <a, w(a,t)> for various w
    'Lt_tatT': (['a', 'baBBabbAB'], ['a', 'baBB'], 'A=<a, t a t^-1>'),
    'Lt_tt': (['a', 'baBBbaBB'], ['a', 'baBB'], 'A=<a,t^2> (not malnormal)'),
    'Lt_tatt': (['a', 'baBBabaBBbaBB'], ['a', 'baBB'], 'A=<a, t a t t>'),
    'Lt_ttaT': (['a', 'baBBbaBBabbAB'], ['a', 'baBB'], 'A=<a, t t a t^-1>'),
    # B not containing a: B = <ab, ba>-type malnormal rank 2
    'Bab_x': (['abba', 'baab'], ['ab', 'ba'], 'A=<xy,yx> in B=<x=ab,y=ba>'),
    # finite-index B (rank 3), A = <a, b a b^-1 ...>
    'fi_a2': (['aa', 'b'], ['aa', 'b', 'abA'], 'A=<a^2,b> < B=<a^2,b,aba^-1> index-2'),
}


def psi_chain(u, j):
    """psi(a)=a, psi(b)=u; returns (A gens, B gens) = (<a,psi^{j+1}(b)>, <a,psi^j(b)>)."""
    img = {'a': 'a', 'A': 'A', 'b': u, 'B': ''.join(
        c.swapcase() for c in reversed(u))}

    def ap(w):
        out = ''.join(img[c] for c in w)
        return ''.join(('%s' % l if e == 1 else l.upper()) for (l, e) in W(out))
    w = 'b'
    for _ in range(j):
        w = ap(w)
    return ['a', ap(w)], ['a', w]


for _u in ['baBB', 'baBaB', 'bbaBBB', 'baabBB', 'bAbaBB', 'baBaaB']:
    for _j in (1, 2):
        _A, _B = psi_chain(_u, _j)
        CHAINS['psi_%s_j%d' % (_u, _j)] = (_A, _B, 'psi(b)=%s, level %d' % (_u, _j))


def transitive(PA, PB):
    n = len(PA)
    seen = {0}
    st = [0]
    IA = [0] * n
    IB = [0] * n
    for i in range(n):
        IA[PA[i]] = i
        IB[PB[i]] = i
    while st:
        p = st.pop()
        for q in (PA[p], PB[p], IA[p], IB[p]):
            if q not in seen:
                seen.add(q)
                st.append(q)
    return len(seen) == n


def pair_graphs(PA, PB, Agens, Bgens):
    n = len(PA)
    GB = Graph(gamma(PA, PB, [W(s) for s in Bgens]), n, PA, PB)
    GA = Graph(gamma(PA, PB, [W(s) for s in Agens]), n, PA, PB)
    m = [None] * GA.V
    for v in range(GA.V):
        p, w = GA.word[v]
        m[v] = GB.read(p, w)
        assert m[v] is not None, 'A not inside B?'
    return GB, GA, m


def canon(cls):
    first = {}
    return tuple(first.setdefault(c, len(first)) for c in cls)


def seeds_of(G, m):
    """Deduplicated single seeds: (pair, lawful?) keyed by single closure."""
    byp = {}
    for v in range(G.V):
        byp.setdefault(G.over[v], []).append(v)
    single = {}
    for vs in byp.values():
        for i in range(len(vs)):
            for k in range(i + 1, len(vs)):
                u, v = vs[i], vs[k]
                cls = closure(G, [(u, v)])
                key = canon(cls)
                lw = m[u] == m[v]
                if key not in single:
                    single[key] = [(u, v), lw]
                elif lw and not single[key][1]:
                    single[key] = [(u, v), True]
    return single


def search(G, seeds, goal, maxk):
    level = {canon(list(range(G.V))): []}
    if goal(list(range(G.V))):
        return 0, []
    for k in range(1, maxk + 1):
        nxt = {}
        for part, chosen in level.items():
            for s in seeds:
                cls = closure(G, chosen + [s])
                c = canon(cls)
                if c in nxt or c == part:
                    continue
                if goal(cls):
                    return k, chosen + [s]
                nxt[c] = chosen + [s]
        level = nxt
        if not level:
            return None, None
    return None, None


def analyse(PA, PB, Agens, Bgens, maxk):
    GB, GA, m = pair_graphs(PA, PB, Agens, Bgens)
    single = seeds_of(GA, m)
    law_seeds = [v[0] for v in single.values() if v[1]]
    all_seeds = [v[0] for v in single.values()]

    def goal(cls):
        return contains_kernel(GA, cls, m)
    dk, dw = search(GA, all_seeds, goal, maxk)
    lk, _ = search(GA, law_seeds, goal, maxk)
    return dk, lk, dw, GA.V, GB.V, len(all_seeds), len(law_seeds)


def main():
    name, n, trials, seed, maxk = sys.argv[1], int(sys.argv[2]), \
        int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
    Agens, Bgens, comment = CHAINS[name]
    rng = random.Random(seed)
    hist = {}
    done = 0
    print('chain', name, '(%s)' % comment, 'A', Agens, 'B', Bgens)
    while done < trials:
        PA = list(range(n)); rng.shuffle(PA)
        PB = list(range(n)); rng.shuffle(PB)
        if not transitive(PA, PB):
            continue
        done += 1
        dk, lk, dw, va, vb, ns, nl = analyse(PA, PB, Agens, Bgens, maxk)
        key = (dk, lk)
        hist[key] = hist.get(key, 0) + 1
        if dk is not None and (lk is None or dk < lk):
            print('GAP deep', dk, 'law', lk if lk is not None else '>%d' % maxk,
                  'PA', PA, 'PB', PB, '|GA|', va, '|GB|', vb, 'witness', dw)
            sys.stdout.flush()
    print('n', n, 'trials', trials, 'seed', seed, 'maxk', maxk,
          'hist (deep,law):', sorted(hist.items(), key=str))


if __name__ == '__main__':
    main()
