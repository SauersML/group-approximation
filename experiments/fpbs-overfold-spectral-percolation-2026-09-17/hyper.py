"""Deep promotion at depth j as multi-type 2-of-3 bootstrap percolation.

Atoms   = (x, i): x in Q, i a pair type (off-diagonal component of the pair
          graph C_{j+1} x_R C_{j+1}; all are finite trees by malnormality).
          Atom (x, i) is the set of same-fibre pairs {(x.g, root_i.g)}.
Hyperedges = (q, k): q in Q, k a triangle type (component of the graph of
          unordered triples of distinct vertices of C_{j+1}).  The triangle
          {c, d, e} at q has its three pairs in three atoms; fold closure is
          exactly: an atom set closed under "two atoms of a hyperedge active
          => third active" (transitivity inside fibres; propagation along
          edges is built into atoms).
Goal    = all atoms of the lawful type.

Uses the pullback model of experiments/fpbs-overfold-breaker-2026-09-17/pb.py.
"""
import os
import sys
import random
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'fpbs-overfold-breaker-2026-09-17'))
from pb import model, Level  # noqa: E402

INV = [1, 0, 3, 2]   # key index of the inverse letter


def pair_index(C):
    """type[(c,d)] and word[(c,d)] (key list from the type root)."""
    nb = C[0]
    V = len(nb)
    typ, word, roots, law = {}, {}, [], []
    for c in range(V):
        for d in range(c + 1, V):
            if (c, d) in typ:
                continue
            t = len(roots)
            roots.append((c, d))
            typ[(c, d)] = t
            word[(c, d)] = []
            st = [(c, d)]
            while st:
                x, y = st.pop()
                for i in range(4):
                    u, v = nb[x][i], nb[y][i]
                    if u >= 0 and v >= 0:
                        key = (u, v) if u < v else (v, u)
                        if key not in typ:
                            typ[key] = t
                            word[key] = word[(x, y)] + [i]
                            st.append(key)
    return typ, word, roots


def triangle_types(C):
    """Components of the unordered distinct-triple graph; returns list of
    (root triple, n_vertices, n_edges)."""
    nb = C[0]
    V = len(nb)
    seen = set()
    out = []
    for c in range(V):
        for d in range(c + 1, V):
            for e in range(d + 1, V):
                if (c, d, e) in seen:
                    continue
                seen.add((c, d, e))
                st = [(c, d, e)]
                nv, ne = 1, 0
                while st:
                    x = st.pop()
                    for i in range(4):
                        y = [nb[z][i] for z in x]
                        if min(y) >= 0:
                            ne += 1
                            key = tuple(sorted(y))
                            if key not in seen:
                                seen.add(key)
                                nv += 1
                                st.append(key)
                out.append(((c, d, e), nv, ne))  # ne counts each edge twice
    return out


def build(j):
    Cs, Cb, io, _ = model(j)
    typ, word, roots = pair_index(Cs)
    lawful = [io[c] == io[d] for (c, d) in roots]
    tris = triangle_types(Cs)
    hyp = []   # per triangle type: three (type, inverse-word) entries
    for (c, d, e), nv, ne in tris:
        assert ne == 2 * (nv - 1), 'triangle component not a tree'
        ent = []
        for p in ((c, d), (d, e), (c, e)):
            w = word[p]
            ent.append((typ[p], [INV[i] for i in reversed(w)]))
        hyp.append(ent)
    return dict(R=len(roots), lawful=lawful, hyp=hyp, roots=roots,
                typ=typ, word=word, Cs=Cs, io=io)


def act_tables(PA, PB):
    n = len(PA)
    IA, IB = [0] * n, [0] * n
    for i in range(n):
        IA[PA[i]] = i
        IB[PB[i]] = i
    return [PA, IA, PB, IB]


def instantiate(M, PA, PB):
    """Hyperedges on a level: list of atom-id triples, atom id = x*R + i."""
    act = act_tables(PA, PB)
    n, R = len(PA), M['R']
    H = []
    for ent in M['hyp']:
        for q in range(n):
            tr = []
            for (i, w) in ent:
                x = q
                for k in w:
                    x = act[k][x]
                tr.append(x * R + i)
            H.append(tuple(tr))
    return H


def closure(nat, H, seeds):
    inc = [[] for _ in range(nat)]
    for h, tr in enumerate(H):
        for a in tr:
            inc[a].append(h)
    on = bytearray(nat)
    st = []
    for s in seeds:
        if not on[s]:
            on[s] = 1
            st.append(s)
    while st:
        a = st.pop()
        for h in inc[a]:
            x, y, z = H[h]
            c = on[x] + on[y] + on[z]
            if c == 2:
                for u in (x, y, z):
                    if not on[u]:
                        on[u] = 1
                        st.append(u)
    return on


def random_level(n, rng):
    PA = list(range(n))
    PB = list(range(n))
    rng.shuffle(PA)
    rng.shuffle(PB)
    return PA, PB


def validate(j, n, trials, seed=1):
    """Compare hypergraph closure with the true fold closure (pb.Level)."""
    rng = random.Random(seed)
    M = build(j)
    R = M['R']
    bad = 0
    for _ in range(trials):
        PA, PB = random_level(n, rng)
        H = instantiate(M, PA, PB)
        Lv = Level(PA, PB, j)
        k = rng.randint(1, max(1, n // 2))
        atoms = [(rng.randrange(n), rng.randrange(R)) for _ in range(k)]
        on = closure(n * R, H, [x * R + i for x, i in atoms])
        Vc = Lv.Vc
        pairs = []
        for x, i in atoms:
            c, d = M['roots'][i]
            pairs.append((x * Vc + c, x * Vc + d))
        cls = Lv.closure(pairs)
        # every same-fibre pair: identified in fold closure iff its atom on
        for q in range(n):
            for (c, d), t in M['typ'].items():
                w = M['word'][(c, d)]
                x = q
                act = act_tables(PA, PB)
                for kk in reversed(w):
                    x = act[INV[kk]][x]
                a = on[x * R + t]
                b = cls[q * Vc + c] == cls[q * Vc + d]
                if bool(a) != bool(b):
                    bad += 1
    return bad


if __name__ == '__main__':
    for j in (0, 1, 2):
        M = build(j)
        comp = {}
        for ent in M['hyp']:
            key = ''.join('L' if M['lawful'][i] else 'O' for i, _ in ent)
            key = ''.join(sorted(key))
            comp[key] = comp.get(key, 0) + 1
        print('j', j, 'pair types', M['R'], 'lawful', sum(M['lawful']),
              'triangle types', len(M['hyp']), comp)
    for j, n in ((0, 7), (1, 6), (1, 9), (2, 5)):
        print('validate j', j, 'n', n, 'mismatches', validate(j, n, 20))
