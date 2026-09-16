# Sanity check for research/fpbs-twisted-cyclic-by-free-nonunimodular-proof.md.
# Run: timeout 600 python3 twisted_lift_check.py   (single-threaded, a few seconds)
#
# Gamma = Z x|_chi F_n, product (m,g)(m',g') = (m + chi(g) m', g g'), chi: F_n -> {+1,-1}
# nontrivial on the free basis.  S = {(d,s) : d in D_s} u {(v,1) : v in V} and inverses,
# with arbitrary (also rigid) decoration sets D_s.
#
# Part 1  From the group law only: the X-edges over the tree edge {g,gs} are exactly
#         (p,m)-(q,m+d), d in D_s, where p = g if chi(g)=+1 and p = gs otherwise.
# Part 2  Build a ball of the covering tree Y of the four-vertex edge-indexed graph A, check
#         that its local types match the chi-structure of T = Cay(F_n,B), build an
#         isomorphism iota ball by ball, draw random p-preserving automorphisms of Y (moving
#         the root to a vertex three steps away over the same vertex of A), transport them to
#         T, and check that (g,m) -> (phi g, m) maps every X-edge of the ball to an X-edge,
#         with NO height potential.
# Part 3  Stabilizer counts |Stab_{y0} y1| and |Stab_{y1} y0| by counting lifts of an A-path
#         (extension lemma), expected 1 and 2; the product of near/far indices along the path,
#         expected 1/2.
# Control For chi trivial (F_n x Z) and the rigid set D_a = {0,1,3}, no translate of D_a equals
#         -D_a, so the swap of the two a-edges at a vertex has no lift with a height potential;
#         the last case transports the same automorphisms to the F_2 x Z group law and must
#         report bad edges.
# Output of the run on 2026-09-16: part1 0 bad, iota 0 defects, counts 1 and 2, lift check
# 0 bad in all six twisted cases (n = 2, 3; rigid decorations included); control: no shift,
# 248 bad of 1272 edges.
import random
from collections import defaultdict

random.seed(20260916)

def inv(x): return x.swapcase()
def reduce_mul(w, x): return w[:-1] if w and w[-1] == inv(x) else w + x

def letters(n): return [chr(ord('a') + i) for i in range(n)]

def ball(n, R):
    L = letters(n) + [c.upper() for c in letters(n)]
    words, frontier = [''], ['']
    for _ in range(R):
        frontier = [w + x for w in frontier for x in L if not (w and w[-1] == inv(x))]
        words += frontier
    return words

def chi_word(chi, w):
    s = 1
    for x in w:
        s *= chi[x.lower()]
    return s

# ---------- group law of Z x|_chi F_n ----------
def mul(chi, a, b):
    (m, g), (mm, gg) = a, b
    w = g
    for x in gg:
        w = reduce_mul(w, x)
    return (m + chi_word(chi, g) * mm, w)

def ginv(chi, a):
    m, g = a
    gi = ''.join(inv(x) for x in reversed(g))
    return (-chi_word(chi, g) * m, gi)

def gen_set(chi, D, V):
    S = set()
    for s, Ds in D.items():
        for d in Ds:
            S.add((d, s))
            S.add(ginv(chi, (d, s)))
    for v in V:
        S.add((v, ''))
        S.add((-v, ''))
    return S

def change_set(chi, S, g, x):
    """Heights m' with (m', g x) adjacent to (0, g) in Cay(Gamma,S)."""
    target = reduce_mul(g, x)
    out = set()
    for gen in S:
        m2, w2 = mul(chi, (0, g), gen)
        if w2 == target:
            out.add(m2)
    return frozenset(out)

def part1(n, chi, D, V, R=4):
    S = gen_set(chi, D, V)
    bad = 0
    for g in ball(n, R):
        for x in letters(n) + [c.upper() for c in letters(n)]:
            s = x.lower()
            h = g if x == s else reduce_mul(g, x)       # edge {h, h s}
            p = h if chi_word(chi, h) == 1 else reduce_mul(h, s)
            pred = frozenset(D[s]) if p == g else frozenset(-d for d in D[s])
            if change_set(chi, S, g, x) != pred:
                bad += 1
        if change_set(chi, S, g, '') != frozenset(set(V) | {-v for v in V}):
            bad += 1
    return bad

# ---------- edge-indexed graph A and covering tree Y ----------
PLUS = {'u', 'w'}

def build_A(n, chi):
    B = letters(n)
    s0 = next(s for s in B if chi[s] == -1)
    E = []   # (letter, end0, end1, i0, i1, directed)
    E += [(s0, 'u', 'x', 2, 1, False), (s0, 'x', 'w', 1, 1, False), (s0, 'w', 'y', 1, 2, False)]
    for r in B:
        if r == s0:
            continue
        if chi[r] == -1:
            E += [(r, 'u', 'x', 1, 1, False), (r, 'x', 'w', 1, 1, False),
                  (r, 'w', 'y', 1, 1, False), (r, 'y', 'u', 1, 1, False)]
        else:
            E += [(r, 'u', 'w', 1, 1, True), (r, 'w', 'u', 1, 1, True),
                  (r, 'x', 'y', 1, 1, True), (r, 'y', 'x', 1, 1, True)]
    return s0, E

def check_A_sums(n, chi, E):
    bad = 0
    for a in 'uwxy':
        for r in letters(n):
            ends = [(e[3] if e[1] == a else 0) + (e[4] if e[2] == a else 0)
                    for e in E if e[0] == r]
            if chi[r] == -1:
                if sum(ends) != 2:
                    bad += 1
            else:
                outs = sum(e[3] for e in E if e[0] == r and e[1] == a)
                ins = sum(e[4] for e in E if e[0] == r and e[2] == a)
                if (outs, ins) != (1, 1):
                    bad += 1
    return bad

def build_Y(E, RY):
    pv, depth, adj = ['u'], [0], [[]]    # adj[z] = list of (nbr, edge id, end of z)
    frontier = [0]
    for _ in range(RY):
        nxt = []
        for z in frontier:
            entering = adj[z][0][1:] if z != 0 else None
            for eid, e in enumerate(E):
                for j in (0, 1):
                    if e[1 + j] != pv[z]:
                        continue
                    cnt = e[3 + j] - (1 if entering == (eid, j) else 0)
                    for _ in range(cnt):
                        c = len(pv)
                        pv.append(e[2 - j]); depth.append(depth[z] + 1)
                        adj.append([(z, eid, 1 - j)])
                        adj[z].append((c, eid, j))
                        nxt.append(c)
        frontier = nxt
    return pv, depth, adj

def y_type(E, chi, eid, j):
    r, directed = E[eid][0], E[eid][5]
    if chi[r] == -1:
        return (r, None)
    return (r, 'out' if j == 0 else 'in')

def t_type(chi, g, x):
    s = x.lower()
    if chi[s] == -1:
        return (s, None)
    h = g if x == s else reduce_mul(g, x)
    out_of_h = chi_word(chi, h) == 1
    out_of_g = out_of_h if h == g else not out_of_h
    return (s, 'out' if out_of_g else 'in')

def build_iota(n, chi, E, pv, depth, adj, RY):
    iota = {0: ''}
    bad = 0
    order = sorted(range(len(pv)), key=lambda z: depth[z])
    L = letters(n) + [c.upper() for c in letters(n)]
    for z in order:
        if depth[z] >= RY:
            continue
        g = iota[z]
        if (chi_word(chi, g) == 1) != (pv[z] in PLUS):
            bad += 1
        yed = [(nb, eid, j) for (nb, eid, j) in adj[z] if depth[nb] > depth[z]]
        ted = [x for x in L if not (g and g[-1] == inv(x))]
        gy, gt = defaultdict(list), defaultdict(list)
        for (nb, eid, j) in yed:
            gy[y_type(E, chi, eid, j)].append(nb)
        for x in ted:
            gt[t_type(chi, g, x)].append(x)
        if {k: len(v) for k, v in gy.items()} != {k: len(v) for k, v in gt.items()}:
            bad += 1
            continue
        for k in gy:
            xs = gt[k][:]
            random.shuffle(xs)
            for nb, x in zip(gy[k], xs):
                iota[nb] = reduce_mul(g, x)
    return iota, bad

def random_aut_Y(pv, depth, adj, root_img, R):
    """Random p-preserving automorphism of Y on the ball of radius R, with phi(0) = root_img."""
    phi = {0: root_img}
    order = sorted(range(len(pv)), key=lambda z: depth[z])
    for z in order:
        if depth[z] > R:
            break
        zi = phi[z]
        src = defaultdict(list)
        for (nb, eid, j) in adj[z]:
            if nb in phi:           # the parent edge (already mapped)
                continue
            src[(eid, j)].append(nb)
        tgt = defaultdict(list)
        for (nb, eid, j) in adj[zi]:
            if z != 0 and nb == phi[adj[z][0][0]]:
                continue
            tgt[(eid, j)].append(nb)
        for k, v in src.items():
            t = tgt[k][:]
            assert len(t) == len(v), (k, len(t), len(v))
            random.shuffle(t)
            for a, b in zip(v, t):
                phi[a] = b
    return phi

def path_lift_count(pv, adj, start, steps):
    """Number of non-backtracking walks from start over the A-edge ends in `steps`
    (list of (edge id, end at the current vertex))."""
    cur = [(start, None)]
    for (eid, j) in steps:
        nxt = []
        for (z, came) in cur:
            for (nb, e2, j2) in adj[z]:
                if (e2, j2) == (eid, j) and nb != came:
                    nxt.append((nb, z))
        cur = nxt
    return len(cur)

def reference_path(n, chi, E, s0):
    B = letters(n)
    t = next(r for r in B if r != s0)
    idx = lambda r, a, b: next(i for i, e in enumerate(E) if e[0] == r and e[1] == a and e[2] == b)
    e1, e2 = idx(s0, 'u', 'x'), idx(s0, 'x', 'w')
    if chi[t] == 1:
        et = idx(t, 'u', 'w')
        fwd = [(et, 0), (e2, 1), (e1, 1)]      # u -t-> w -s0-> x -s0-> u
        back = [(e1, 0), (e2, 0), (et, 1)]
        ratio = (E[et][3] / E[et][4]) * (E[e2][4] / E[e2][3]) * (E[e1][4] / E[e1][3])
    else:
        et = idx(t, 'u', 'x')
        fwd = [(et, 0), (e1, 1)]               # u -t- x -s0- u
        back = [(e1, 0), (et, 1)]
        ratio = (E[et][3] / E[et][4]) * (E[e1][4] / E[e1][3])
    return t, fwd, back, ratio

def walk(adj, start, steps):
    z, came = start, None
    for (eid, j) in steps:
        nb = next(nb for (nb, e2, j2) in adj[z] if (e2, j2) == (eid, j) and nb != came)
        z, came = nb, z
    return z

def run_case(n, chi, D, V, R=4, trials=12, chi_group=None):
    # chi_group != chi is the negative control: the tree structure comes from chi, the group law
    # (hence the Cayley graph whose edges are tested) from chi_group.
    chi_group = chi if chi_group is None else chi_group
    print(f"n={n} chi={chi} D={D} V={V}" + ("" if chi_group == chi else f"  CONTROL group law chi={chi_group}"))
    print("  part1 bad tree edges (group law vs predicted shape):", part1(n, chi, D, V, R))
    s0, E = build_A(n, chi)
    print("  s0 =", s0, " A index-sum defects:", check_A_sums(n, chi, E))
    RY = R + 5
    pv, depth, adj = build_Y(E, RY)
    iota, bad_iota = build_iota(n, chi, E, pv, depth, adj, RY)
    print("  Y ball size", len(pv), " iota type/colour defects:", bad_iota,
          " injective:", len(set(iota.values())) == len(iota))
    t, fwd, back, ratio = reference_path(n, chi, E, s0)
    y1 = walk(adj, 0, fwd)
    print(f"  t = {t}; y1 over {pv[y1]}, depth {depth[y1]}")
    print("  |Stab_y0 y1| =", path_lift_count(pv, adj, 0, fwd),
          " |Stab_y1 y0| =", path_lift_count(pv, adj, y1, back),
          " near/far index product along the path (predicts the quotient) =", ratio)
    S = gen_set(chi_group, D, V)
    L = letters(n) + [c.upper() for c in letters(n)]
    inv_iota = {g: z for z, g in iota.items()}
    total_bad, total_edges = 0, 0
    for trial in range(trials):
        root_img = 0 if trial % 2 == 0 else y1
        phi = random_aut_Y(pv, depth, adj, root_img, R + 1)
        for g in ball(n, R):
            hg = iota[phi[inv_iota[g]]]
            for x in L:
                gx = reduce_mul(g, x)
                hgx = iota[phi[inv_iota[gx]]]
                y = next((yy for yy in L if reduce_mul(hg, yy) == hgx), None)
                total_edges += 1
                if y is None or change_set(chi_group, S, g, x) != change_set(chi_group, S, hg, y):
                    total_bad += 1
    print(f"  lift check: {total_bad} bad of {total_edges} oriented tree edges "
          f"(zero height potential, {trials} random automorphisms)")

def control(D_a=(0, 1, 3)):
    Da = set(D_a)
    shifts = [c for c in range(-20, 21) if {d + c for d in Da} == {-d for d in Da}]
    print("control F_2 x Z: shifts c with D_a + c = -D_a:", shifts)
    chi = {'a': 1, 'b': 1}
    S = gen_set(chi, {'a': D_a, 'b': (0, 1, 4)}, (1,))
    print("  change sets at 1 along a and A:", sorted(change_set(chi, S, '', 'a')),
          sorted(change_set(chi, S, '', 'A')))

if __name__ == '__main__':
    rig = {'a': (0, 1, 3), 'b': (0, 1, 4)}
    run_case(2, {'a': -1, 'b': 1}, rig, (1,))
    run_case(2, {'a': 1, 'b': -1}, rig, (1,))
    run_case(2, {'a': -1, 'b': -1}, rig, (1,))
    run_case(2, {'a': -1, 'b': -1}, {'a': (0, 2, 7), 'b': (1, 6, 8)}, ())
    run_case(3, {'a': -1, 'b': 1, 'c': 1}, {'a': (0, 1, 3), 'b': (0, 1, 4), 'c': (0, 2, 3, 7)}, (1, 2), R=3, trials=6)
    run_case(3, {'a': 1, 'b': -1, 'c': -1}, {'a': (0, 1, 3), 'b': (0, 1, 4), 'c': (0, 2, 3, 7)}, (1,), R=3, trials=6)
    control()
    run_case(2, {'a': -1, 'b': 1}, rig, (1,), R=3, trials=6, chi_group={'a': 1, 'b': 1})
