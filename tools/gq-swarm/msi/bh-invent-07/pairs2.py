#!/usr/bin/env python3
"""bh-invent-07, search 2: sizes of exotic two-sided minimal common upper bounds of two edge splits.

Uses pairs.py (same directory).  For a pair of atoms (a, b) and a known small bound set KB:
  sample split trees rooted at a (or b), resolve the other plane by the cut rule, keep common upper bounds
  not >=_E any element of KB, minimize with randomized cherry-removal order (several orders), canonicalize
  up to the coordinate symmetries preserving {a, b}, and record size, root graph, and the non-tree regions.
Calibration: the square / flop suspensions minimal with two-atom root graph; the 13-piece pinwheel bound of
  search 1 re-verified minimal and not above the square (planted positive).
"""
import sys, time, random, itertools, json
import pairs as P

T0 = time.time()
TL = float(sys.argv[1]) if len(sys.argv) > 1 else 840.0
rnd = random.Random(20260919)
P.rnd = rnd


def out(tag, obj):
    print(json.dumps({tag: obj, "t": round(time.time() - T0, 1)}), flush=True)


def left():
    return TL - (time.time() - T0)


def gc():
    if len(P.TM) > 1500000:
        P.TM.clear()
    if len(P.DM) > 3000000:
        P.DM.clear()


def perm_cell(C, s):
    return P.cell([tuple(v[s[k]] for k in range(len(v))) for v in C])


def canon(Th, syms):
    best = None
    for s in syms:
        key = tuple(sorted(perm_cell(C, s) for C in Th))
        if best is None or key < best:
            best = key
    return best


def minimize_r(U, A, B, D0):
    cur = frozenset(U)
    while True:
        lc = P.lower_covers(cur, D0)
        rnd.shuffle(lc)
        nxt = None
        for Up in lc:
            if P.common_ub(Up, A, B):
                nxt = Up
                break
        if nxt is None:
            return cur
        cur = nxt


def regions_nontree(Th, KB):
    """for each known bound, the number of its pieces on which Th restricts to a non-tree"""
    res = []
    for K in KB:
        bad = 0
        for p in K:
            S = frozenset(q for q in Th if P.sub(q, p))
            if not S or not P.is_tree(p, S):
                bad += 1
        res.append(bad)
    return res


def run_pair(name, n, a, b, KB, syms, budget, kmax, cap, orders=3, planted=None):
    D0 = P.delta(n)
    A, B = P.atom(n, *a), P.atom(n, *b)
    cal = {}
    for i, K in enumerate(KB):
        cal["KB%d" % i] = {"tree": P.is_tree(D0, K), "ub": P.common_ub(K, A, B),
                           "minimal": not any(P.common_ub(Up, A, B) for Up in P.lower_covers(K, D0)),
                           "root_graph": P.root_graph(K, n, D0)}
    if planted is not None:
        cal["planted"] = {"tree": P.is_tree(D0, planted), "ub": P.common_ub(planted, A, B),
                          "above_KB": [P.geq(planted, K) for K in KB],
                          "minimal": not any(P.common_ub(Up, A, B) for Up in P.lower_covers(planted, D0)),
                          "root_graph": P.root_graph(planted, n, D0)}
    out("calib_" + name, cal)
    t_end = time.time() + budget
    tested = ubs = dom = exo = 0
    found = {}
    sizes_U = []
    while time.time() < t_end and left() > 3:
        gc()
        tested += 1
        root, other = (A, b) if rnd.random() < 0.5 else (B, a)
        U0 = P.rand_refine(root, rnd.randint(3, kmax))
        U = P.resolve(U0, other[0], other[1], cap)
        if U is None or not P.common_ub(U, A, B):
            continue
        ubs += 1
        if any(P.geq(U, K) for K in KB):
            dom += 1
            continue
        exo += 1
        sizes_U.append(len(U))
        for _ in range(orders):
            if time.time() > t_end:
                break
            Th = minimize_r(U, A, B, D0)
            key = canon(Th, syms)
            if key not in found:
                found[key] = {"size": len(Th), "count": 0,
                              "root_graph": P.root_graph(Th, n, D0),
                              "nontree_regions": regions_nontree(Th, KB),
                              "example": sorted(Th)}
            found[key]["count"] += 1
    dist = {}
    for v in found.values():
        dist[v["size"]] = dist.get(v["size"], 0) + 1
    out("result_" + name, {"tested": tested, "common_ub": ubs, "dominate_known": dom, "exotic_ub": exo,
                           "exotic_ub_sizes": sorted(set(sizes_U)), "distinct_minimal": len(found),
                           "size_distribution": dist,
                           "minimal": sorted(found.values(), key=lambda v: v["size"])[:12]})


def suspend(K, n_from, n_to):
    extra = [P.unit(n_to, k) for k in range(n_from, n_to)]
    return frozenset(P.cell([tuple(list(v) + [0] * (n_to - n_from)) for v in C] + extra) for C in K)


def main():
    # rank 3 flops (for suspension)
    e = lambda i: P.unit(3, i)
    v01, v02, c = P.add(e(0), e(1)), P.add(e(0), e(2)), (1, 1, 1)
    Fp = frozenset([P.cell([e(0), v01, v02]), P.cell([v01, c, v02]), P.cell([v01, e(1), c]), P.cell([v02, c, e(2)]), P.cell([c, e(1), e(2)])])
    Fm = frozenset([P.cell([e(0), v01, c]), P.cell([e(0), c, v02]), P.cell([v01, e(1), c]), P.cell([v02, c, e(2)]), P.cell([c, e(1), e(2)])])

    def square(n):
        sq = set()
        for h in P.atom(n, 0, 1):
            sq.update(P.kids(h, P.unit(n, 2), P.unit(n, 3)))
        return frozenset(sq)

    s4 = []
    for p01 in ((0, 1), (1, 0)):
        for p23 in ((2, 3), (3, 2)):
            s4.append((p01[0], p01[1], p23[0], p23[1]))
            s4.append((p23[0], p23[1], p01[0], p01[1]))
    s5 = [s + (4,) for s in s4]
    pin = frozenset(tuple(tuple(int(ch) for ch in r) for r in c4) for c4 in [
        ("0001", "0011", "0111", "1111"), ("0001", "0011", "1000", "1100"), ("0001", "0100", "0111", "1100"),
        ("0001", "0111", "1100", "1111"), ("0010", "0011", "0111", "1111"), ("0010", "0011", "1000", "1111"),
        ("0010", "0110", "0111", "1111"), ("0010", "0110", "1110", "1111"), ("0010", "1000", "1110", "1111"),
        ("0100", "0110", "0111", "1100"), ("0110", "0111", "1100", "1111"), ("0110", "1100", "1110", "1111"),
        ("1000", "1100", "1110", "1111")])
    pin = frozenset(P.cell(list(C)) for C in pin)
    run_pair("rank4_disjoint", 4, (0, 1), (2, 3), [square(4)], s4, budget=460, kmax=18, cap=260, orders=3, planted=pin)
    run_pair("rank4_adjacent", 4, (0, 1), (0, 2), [suspend(Fp, 3, 4), suspend(Fm, 3, 4)],
             [(0, 1, 2, 3), (0, 2, 1, 3)], budget=170, kmax=12, cap=200, orders=2)
    run_pair("rank5_disjoint", 5, (0, 1), (2, 3), [square(5)], s5, budget=left() - 15, kmax=9, cap=120, orders=2,
             planted=suspend(pin, 4, 5))
    out("done", True)


if __name__ == "__main__":
    main()
