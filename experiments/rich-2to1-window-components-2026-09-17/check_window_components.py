#!/usr/bin/env python3
"""Brute-force checks for window-certified-richness-is-conserved-modulo-merges.

Part A  (general sources): random binary-CSP windows with hidden variables.
        For every 2-to-1 gadget satisfying source-local completeness (SLC):
        A1 every component of R_(u,u') has at most 2 labels per side;
        A2 per h-value the components are one (2,2) or two (1,1) ones;
        A3 every u-side 2-block of a component is a block of h_u, whatever h;
        and on small wrappers W, for every left labeling L:
        A4 val_W(L) >= val_D(L) >= val_Ut(L) - phi,
        A5 phi <= forced edge mass;
        A6 mixed windows (bijection and 2-block components in one pair) occur.
Part B  (coset sources over finite groups): random coset constraints.
        B1 every projected relation R_(u,u') has all components of one size |N|;
        B2 if |N| = 2 then N = {1,b} with b a central involution and the blocks
           are {y, y b};  if |N| > 2 no SLC gadget exists;
        B3 at a forced right vertex every neighbour's pairing is a central
           involution translation.
Part C  mass bound: under the uniform pairing law, E Q = c C(k,2)/((2k-1)(2k-3))
        and Pr[translation pairing] = c/(2k-1)!! <= c/((2k-1)(2k-3)).
Exit code 0 iff every check passes.
"""
import itertools
import random
from math import comb, prod

random.seed(20260917)
FAIL = []


def check(cond, msg):
    if not cond:
        FAIL.append(msg)


# ---------------------------------------------------------------- utilities
def two_to_one_maps(n):
    """All 2-to-1 maps [n] -> [n/2], up to nothing (all labelled maps)."""
    k = n // 2
    out = []
    for vals in itertools.product(range(k), repeat=n):
        if all(vals.count(c) == 2 for c in range(k)):
            out.append(vals)
    return out


def components(R, n1, n2):
    """Connected components of bipartite relation R on [n1] + [n2]."""
    parent = {}

    def find(x):
        while parent.setdefault(x, x) != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(a, b):
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[ra] = rb

    for a in range(n1):
        find(("u", a))
    for b in range(n2):
        find(("v", b))
    for a, b in R:
        union(("u", a), ("v", b))
    comps = {}
    for x in list(parent):
        comps.setdefault(find(x), set()).add(x)
    res = []
    for c in comps.values():
        cu = frozenset(a for t, a in c if t == "u")
        cv = frozenset(b for t, b in c if t == "v")
        res.append((cu, cv))
    return res


def solve_window(sizes, cons):
    """All satisfying assignments of a CSP: sizes per variable, cons = list of
    (i, j, set of allowed pairs)."""
    sols = []
    for f in itertools.product(*[range(s) for s in sizes]):
        if all((f[i], f[j]) in rel for i, j, rel in cons):
            sols.append(f)
    return sols


# ---------------------------------------------------------------- Part A
MAPS4 = two_to_one_maps(4)

def random_window(s, n, hidden, hid_size, ncons, density):
    """A 2-to-1 source star (hidden right variable c in [n/2] joined to every
    window left variable by a random 2-to-1 map) plus `hidden` further hidden
    variables and `ncons` random extra relations.  The star makes an SLC gadget
    exist (h_u = pi_u); extra relations prune solutions and create mixing."""
    k = n // 2
    sizes = [n] * s + [k] + [hid_size] * hidden
    V = len(sizes)
    cons = []
    maps = MAPS4 if n == 4 else two_to_one_maps(n)
    for u in range(s):
        pi = random.choice(maps)
        cons.append((u, s, {(a, pi[a]) for a in range(n)}))
    for _ in range(ncons):
        i, j = random.sample(range(V), 2)
        rel = {(a, b) for a in range(sizes[i]) for b in range(sizes[j])
               if random.random() < density}
        cons.append((i, j, rel))
    return sizes, cons


def window_data(s, n, sols):
    A = {tuple(f[:s]) for f in sols}
    full = all({f[u] for f in A} == set(range(n)) for u in range(s))
    R = {}
    for u in range(s):
        for v in range(s):
            if u != v:
                R[(u, v)] = {(f[u], f[v]) for f in A}
    return A, full, R


def slc_gadgets(s, n, A, maps):
    out = []
    for hs in itertools.product(maps, repeat=s):
        if all(len({hs[u][f[u]] for u in range(s)}) == 1 for f in A):
            out.append(hs)
    return out


def forced_blocks(s, n, R, u):
    t = set()
    for v in range(s):
        if v == u:
            continue
        for cu, cv in components(R[(u, v)], n, n):
            if len(cu) == 2:
                t.add(cu)
    return t


def part_a():
    n, s = 4, 3
    maps = two_to_one_maps(n)
    mixed_seen = 0
    windows_with_gadgets = 0
    trials = 0
    while windows_with_gadgets < 60 and trials < 4000:
        trials += 1
        sizes, cons = random_window(s, n, hidden=random.choice([0, 1]),
                                    hid_size=random.choice([2, 3, 4]),
                                    ncons=random.choice([1, 2, 3]),
                                    density=random.choice([0.6, 0.75, 0.9]))
        sols = solve_window(sizes, cons)
        if not sols:
            continue
        A, full, R = window_data(s, n, sols)
        if not full:
            continue
        gads = slc_gadgets(s, n, A, maps)
        if not gads:
            continue
        windows_with_gadgets += 1
        for (u, v), rel in R.items():
            comps = components(rel, n, n)
            sizes_c = sorted((len(a), len(b)) for a, b in comps)
            check(all(len(a) <= 2 and len(b) <= 2 for a, b in comps), "A1")
            kinds = {len(a) for a, b in comps}
            if kinds == {1, 2}:
                mixed_seen += 1
            for hs in gads:
                for a, b in comps:
                    vals = {hs[u][x] for x in a} | {hs[v][y] for y in b}
                    check(len(vals) == 1, "A1 value")
                for c in range(n // 2):
                    cc = [(len(a), len(b)) for a, b in comps
                          if hs[u][next(iter(a))] == c]
                    check(sorted(cc) in ([(2, 2)], [(1, 1), (1, 1)]), "A2 %s" % cc)
        for u in range(s):
            t = forced_blocks(s, n, R, u)
            for hs in gads:
                blocks = {frozenset(x for x in range(n) if hs[u][x] == c)
                          for c in range(n // 2)}
                check(t <= blocks, "A3")
    check(windows_with_gadgets >= 60, "A: too few feasible windows")
    check(mixed_seen > 0, "A6: no mixed window found")
    print("Part A: %d feasible full windows, %d mixed pair relations" %
          (windows_with_gadgets, mixed_seen))

    # A4/A5 on small wrappers: U = 4 left vertices, alphabet 4, several z.
    wrappers = 0
    tries = 0
    while wrappers < 25 and tries < 20000:
        tries += 1
        zs = []
        for _ in range(random.choice([2, 3])):
            S = random.sample(range(4), 3)
            for _inner in range(200):
                sizes, cons = random_window(3, n, hidden=random.choice([0, 1]),
                                            hid_size=random.choice([2, 3, 4]),
                                            ncons=random.choice([1, 2, 3]),
                                            density=random.choice([0.6, 0.8, 0.9]))
                sols = solve_window(sizes, cons)
                if not sols:
                    continue
                A, full, R = window_data(3, n, sols)
                if not full:
                    continue
                gads = slc_gadgets(3, n, A, maps)
                if gads:
                    zs.append((S, A, R, random.choice(gads)))
                    break
        if len(zs) < 2:
            continue
        wrappers += 1
        wz = 1.0 / len(zs)
        # forced edge mass and completed unique game
        phi_pairs = 0.0
        forced_edge = 0.0
        comp_perm = []
        for S, A, R, hs in zs:
            for i in range(3):
                t = forced_blocks(3, n, R, i)
                if t:
                    forced_edge += wz / 3
                for j in range(3):
                    if i == j:
                        perm = {a: a for a in range(n)}
                        X_full = True
                    else:
                        comps = components(R[(i, j)], n, n)
                        perm = {}
                        for a, b in comps:
                            if len(a) == 1 and len(b) == 1:
                                perm[next(iter(a))] = next(iter(b))
                        X_full = len(perm) == n
                        free_a = [a for a in range(n) if a not in perm]
                        free_b = [b for b in range(n) if b not in perm.values()]
                        for a, b in zip(free_a, free_b):
                            perm[a] = b
                    if not X_full:
                        phi_pairs += wz / 9
                    comp_perm.append((wz / 9, S[i], S[j], perm,
                                      R.get((i, j), {(a, a) for a in range(n)})))
        check(phi_pairs <= forced_edge + 1e-12, "A5")
        for L in itertools.product(range(n), repeat=4):
            valW = 0.0
            for S, A, R, hs in zs:
                best = max(sum(1 for i in range(3) if hs[i][L[S[i]]] == c)
                           for c in range(n // 2)) / 3
                valW += wz * best
            valD = sum(w for w, a, b, perm, rel in comp_perm
                       if (L[a], L[b]) in rel)
            valU = sum(w for w, a, b, perm, rel in comp_perm
                       if perm[L[a]] == L[b])
            check(valW >= valD - 1e-12, "A4 W>=D")
            check(valD >= valU - phi_pairs - 1e-12, "A4 D>=U-phi")
    check(wrappers >= 25, "A4: too few wrappers")
    print("Part A: floor verified exhaustively on %d wrappers" % wrappers)


# ---------------------------------------------------------------- Part B
def cyclic(m):
    els = list(range(m))
    return els, lambda a, b: (a + b) % m


def direct(g1, g2):
    e1, m1 = g1
    e2, m2 = g2
    els = [(a, b) for a in e1 for b in e2]
    return els, lambda x, y: (m1(x[0], y[0]), m2(x[1], y[1]))


def perm_group(gens):
    idn = tuple(range(len(gens[0])))
    els = {idn}
    frontier = [idn]
    comp = lambda p, q: tuple(p[q[i]] for i in range(len(p)))
    while frontier:
        new = []
        for x in frontier:
            for g in gens:
                y = comp(x, g)
                if y not in els:
                    els.add(y)
                    new.append(y)
        frontier = new
    return sorted(els), comp


def quaternion():
    # elements (sign, unit) with unit in 1,i,j,k
    table = {("1", "1"): (1, "1"), ("1", "i"): (1, "i"), ("1", "j"): (1, "j"),
             ("1", "k"): (1, "k"), ("i", "1"): (1, "i"), ("i", "i"): (-1, "1"),
             ("i", "j"): (1, "k"), ("i", "k"): (-1, "j"), ("j", "1"): (1, "j"),
             ("j", "i"): (-1, "k"), ("j", "j"): (-1, "1"), ("j", "k"): (1, "i"),
             ("k", "1"): (1, "k"), ("k", "i"): (1, "j"), ("k", "j"): (-1, "i"),
             ("k", "k"): (-1, "1")}
    els = [(s, u) for s in (1, -1) for u in "1ijk"]

    def mul(x, y):
        s, u = table[(x[1], y[1])]
        return (x[0] * y[0] * s, u)
    return els, mul


GROUPS = {
    "Z4": cyclic(4),
    "Z2xZ2": direct(cyclic(2), cyclic(2)),
    "Z6": cyclic(6),
    "S3": perm_group([(1, 0, 2), (1, 2, 0)]),
    "D4": perm_group([(1, 2, 3, 0), (0, 3, 2, 1)]),
    "Q8": quaternion(),
    "Z2^3": direct(direct(cyclic(2), cyclic(2)), cyclic(2)),
}


def subgroup_closure(elements, mul, gens, idn):
    S = {idn}
    frontier = [idn]
    while frontier:
        new = []
        for x in frontier:
            for g in gens:
                y = mul(x, g)
                if y not in S:
                    S.add(y)
                    new.append(y)
        frontier = new
    return S


def identity(els, mul):
    for e in els:
        if all(mul(e, x) == x for x in els):
            return e


def part_b():
    stats = {}
    for name, (els, mul) in GROUPS.items():
        n = len(els)
        idx = {e: i for i, e in enumerate(els)}
        idn = identity(els, mul)
        central_inv = [b for b in els if b != idn and mul(b, b) == idn and
                       all(mul(b, x) == mul(x, b) for x in els)]
        prod_els = [(a, b) for a in els for b in els]
        pmul = lambda x, y: (mul(x[0], y[0]), mul(x[1], y[1]))
        pid = (idn, idn)
        count_pairs = 0
        pure = 0
        feasible_windows = 0
        forced_windows = 0
        for trial in range(60):
            s, hidden = 3, 1
            V = s + hidden
            cons = []
            for _ in range(random.choice([2, 3, 4])):
                i, j = random.sample(range(V), 2)
                while True:
                    gens = [random.choice(prod_els) for _ in range(random.choice([1, 2, 3]))]
                    T = subgroup_closure(prod_els, pmul, gens, pid)
                    if len({x for x, y in T}) == n and len({y for x, y in T}) == n:
                        break
                shift = random.choice(prod_els)
                rel = {(idx[x], idx[y]) for (x, y) in (pmul(shift, t) for t in T)}
                cons.append((i, j, rel))
            sols = solve_window([n] * V, cons)
            if not sols:
                continue
            A, full, R = window_data(s, n, sols)
            if not full:
                continue
            forced_pairs = set()
            bij_pairs = set()
            for (u, v), rel in R.items():
                count_pairs += 1
                comps = components(rel, n, n)
                usz = {len(a) for a, b in comps}
                vsz = {len(b) for a, b in comps}
                check(len(usz) == 1 and len(vsz) == 1 and usz == vsz, "B1 %s" % name)
                if usz == vsz and len(usz) == 1:
                    pure += 1
                size = next(iter(usz))
                if size == 2:
                    forced_pairs.add((u, v))
                    for a, b in comps:
                        x, y = [els[i] for i in a]
                        # y = x * b0 for a central involution b0
                        b0 = [c for c in central_inv if mul(x, c) == y]
                        check(len(b0) == 1, "B2 central %s" % name)
                elif size == 1:
                    bij_pairs.add((u, v))
            # feasibility of an SLC gadget: union-find over (u,a) by rows of A
            parent = {}

            def find(x):
                while parent.setdefault(x, x) != x:
                    x = parent[x]
                return x
            for f in A:
                for u in range(1, s):
                    ra, rb = find((0, f[0])), find((u, f[u]))
                    if ra != rb:
                        parent[ra] = rb
            classes = {}
            for u in range(s):
                for a in range(n):
                    classes.setdefault(find((u, a)), []).append(u)
            too_big = any(max(cl.count(u) for u in range(s)) > 2
                          for cl in classes.values())
            any_big_N = any(len({len(a) for a, b in components(rel, n, n)}) == 1 and
                            next(iter({len(a) for a, b in components(rel, n, n)})) > 2
                            for rel in R.values())
            if any_big_N:
                check(too_big, "B2 |N|>2 but classes small %s" % name)
            if not too_big:
                feasible_windows += 1
                forced_windows += bool(forced_pairs)
            if not too_big and forced_pairs:
                # B3: every neighbour's h-classes are central translations
                for u in range(s):
                    blocks = {}
                    for key, cl in classes.items():
                        members = [a for (w, a) in parent_members(parent, find, s, n, key) if w == u]
                        if members:
                            blocks[key] = members
                    for members in blocks.values():
                        check(len(members) == 2, "B3 class size %s" % name)
                        if len(members) == 2:
                            x, y = els[members[0]], els[members[1]]
                            check(any(mul(x, c) == y for c in central_inv), "B3 %s" % name)
        stats[name] = (count_pairs, pure, len(central_inv), feasible_windows, forced_windows)
    for name, (c, p, ci, fw, fo) in stats.items():
        print("Part B %-6s: %3d projected pair relations, %3d pure, %d central involutions, "
              "%d SLC-feasible windows (%d forced type)" % (name, c, p, ci, fw, fo))
        check(c > 0, "B: no windows for %s" % name)


def parent_members(parent, find, s, n, key):
    return [(u, a) for u in range(s) for a in range(n) if find((u, a)) == key]


# ---------------------------------------------------------------- Part C
def all_pairings(items):
    if not items:
        yield []
        return
    a = items[0]
    for i in range(1, len(items)):
        rest = items[1:i] + items[i + 1:]
        for p in all_pairings(rest):
            yield [frozenset((a, items[i]))] + p


def part_c():
    for name in ["Z4", "Z2xZ2", "Z6", "D4", "Q8", "Z2^3", "S3"]:
        els, mul = GROUPS[name]
        n = len(els)
        k = n // 2
        idn = identity(els, mul)
        idx = {e: i for i, e in enumerate(els)}
        cinv = [b for b in els if b != idn and mul(b, b) == idn and
                all(mul(b, x) == mul(x, b) for x in els)]
        blocks_of = {}
        for b in cinv:
            blocks_of[b] = {frozenset((idx[x], idx[mul(x, b)])) for x in els}
        P = list(all_pairings(list(range(n))))
        EQ = 0
        trans = 0
        for p in P:
            ps = set(p)
            q = sum(comb(len(ps & blocks_of[b]), 2) for b in cinv)
            EQ += q
            if any(ps == blocks_of[b] for b in cinv):
                trans += 1
                check(q >= comb(k, 2), "C Q on translation %s" % name)
        EQ /= len(P)
        pred = len(cinv) * comb(k, 2) / ((2 * k - 1) * (2 * k - 3)) if k >= 2 else 0
        check(abs(EQ - pred) < 1e-9, "C E Q %s: %f vs %f" % (name, EQ, pred))
        pr = trans / len(P)
        bound = len(cinv) / ((2 * k - 1) * (2 * k - 3)) if k >= 2 else 1
        check(pr <= bound + 1e-12, "C bound %s" % name)
        print("Part C %-6s: Pr[translation] = %d/%d = %.5f <= Markov bound %.5f; E Q = %.4f"
              % (name, trans, len(P), pr, bound, EQ))


if __name__ == "__main__":
    part_a()
    part_b()
    part_c()
    if FAIL:
        from collections import Counter
        print("FAILURES:", Counter(FAIL).most_common(10))
        raise SystemExit(1)
    print("ALL CHECKS PASS")
