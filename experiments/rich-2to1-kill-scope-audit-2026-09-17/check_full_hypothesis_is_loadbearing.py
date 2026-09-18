#!/usr/bin/env python3
"""Audit artifact for window-certified-richness-is-conserved-modulo-merges.

The claim's theorem assumes, besides source-local certification (SLC),

    (Full)  for every u in S_z the projection of the intended class A_z to u
            is all of Sigma_u.

The claim's prose ("Where the class dies" / "Covered") nevertheless asserts that
the conservation law covers *any* label-keeping transformation whose
completeness proof is window-local, and explicitly lists dummy padding among the
dead attempts that (2) and (3) "make exact".  Dummy padding is a wrapper whose
windows never mention the dummy labels, so it violates (Full).

This script shows that (Full) is load-bearing, not a normalisation:

  CHECK 1  Over every window A on Sigma = [4] admitting an SLC-feasible 2-to-1
           pair, the implication used in the proof of `val_U >= val_Ut - phi_W`
           ("a not in X_(uu') implies F_(uz) nonempty") holds for every (Full)
           window and fails for many non-(Full) ones.  The minimal witness is
           A = {(0,0),(1,1)}.

  CHECK 2  For that window, SLC puts *no* constraint linking the pairings of
           different neighbours beyond the names of the 0- and 1-fibres, so a
           wrapper can realise the uniform law on all (2k-1)!! pairings at every
           left vertex.  Full richness is compatible with non-(Full) windows.

  CHECK 3  For that window every forced partial pairing is empty, so the
           entropy count (3) of the claim returns phi_W = 0, while the quantity
           the proof actually needs, Pr[X_(u_0 u) != Sigma], equals 1.  The
           richness price in (3) is blind to alphabet restriction.

  CHECK 4  An explicit fully rich, SLC-certified, completeness-certified wrapper
           on that window, for which the pointwise chain of the claim's (2)
               val_W(L) >= val_D(L) >= val_U(L) >= val_Ut(L) - phi_W
           fails at the dummy labelling L = 2 by a margin tending to
           1 - 1/(k-1) as the left degree grows.

  CHECK 5  Control: on random (Full) windows the same code reproduces the chain.

Exit code 0 iff every check passes.
"""

import itertools
import random
from fractions import Fraction

random.seed(20260918)
FAIL = []


def check(cond, msg):
    if not cond:
        FAIL.append(msg)


# ------------------------------------------------------------------ pairings
def pairings(pts):
    """All perfect matchings of the tuple `pts`, as frozensets of frozensets."""
    pts = list(pts)
    if not pts:
        yield frozenset()
        return
    a = pts[0]
    for j in range(1, len(pts)):
        b = pts[j]
        rest = pts[1:j] + pts[j + 1:]
        for tail in pairings(rest):
            yield frozenset({frozenset({a, b})}) | tail


def maps_from_pairing(P):
    """Every 2-to-1 map h : Sigma -> [k] whose fibres are the blocks of P."""
    blocks = sorted(P, key=lambda b: min(b))
    k = len(blocks)
    for names in itertools.permutations(range(k)):
        h = {}
        for blk, nm in zip(blocks, names):
            for x in blk:
                h[x] = nm
        yield h


def pairing_of(h, sigma):
    fib = {}
    for a in sigma:
        fib.setdefault(h[a], []).append(a)
    return frozenset(frozenset(v) for v in fib.values())


# ------------------------------------------------- window structure (claim 1)
def components(A, sigma):
    """Connected components of the bipartite graph A on sigma (left) u sigma."""
    parent = {}

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for a in sigma:
        parent[('L', a)] = ('L', a)
        parent[('R', a)] = ('R', a)
    for (a, b) in A:
        ra, rb = find(('L', a)), find(('R', b))
        if ra != rb:
            parent[ra] = rb
    comps = {}
    for (a, b) in A:
        comps.setdefault(find(('L', a)), (set(), set()))
        comps[find(('L', a))][0].add(a)
        comps[find(('L', a))][1].add(b)
    return list(comps.values())


def window_data(A, sigma):
    comps = components(A, sigma)
    X = {min(L) for (L, R) in comps if len(L) == 1 and len(R) == 1}
    F = set()
    for a, b in itertools.combinations(sigma, 2):
        shared = {y for (x, y) in A if x == a} & {y for (x, y) in A if x == b}
        if shared:
            F.add(frozenset({a, b}))
    full_left = {a for (a, b) in A} == set(sigma)
    full_right = {b for (a, b) in A} == set(sigma)
    return comps, X, F, (full_left and full_right)


# ------------------------------------------------------------------- CHECK 1
def check1():
    sigma = list(range(4))
    all_maps = [h for P in pairings(sigma) for h in maps_from_pairing(P)]
    pairs = list(itertools.product(all_maps, repeat=2))
    stats = {'full_ok': 0, 'full_bad': 0, 'nonfull_ok': 0, 'nonfull_bad': 0}
    minimal_witness = None
    cells = list(itertools.product(sigma, sigma))
    for r in range(1, len(cells) + 1):
        for A in itertools.combinations(cells, r):
            A = set(A)
            feasible = any(all(hu[a] == hv[b] for (a, b) in A) for hu, hv in pairs)
            if not feasible:
                continue
            comps, X, F, full = window_data(A, sigma)
            implication = all(F for a in sigma if a not in X)
            key = ('full_' if full else 'nonfull_') + ('ok' if implication else 'bad')
            stats[key] += 1
            if not full and not implication and minimal_witness is None:
                minimal_witness = sorted(A)
    check(stats['full_bad'] == 0,
          "CHECK 1: a (Full) window broke the implication a not in X => F nonempty")
    check(stats['nonfull_bad'] > 0,
          "CHECK 1: no non-(Full) window broke the implication")
    print(f"CHECK 1  windows on Sigma=[4] admitting an SLC-feasible 2-to-1 pair:")
    print(f"         (Full)      : {stats['full_ok']} keep the implication, "
          f"{stats['full_bad']} break it")
    print(f"         not (Full)  : {stats['nonfull_ok']} keep the implication, "
          f"{stats['nonfull_bad']} break it")
    print(f"         smallest breaking window A_z = {minimal_witness}")
    # the witness used below is the smallest one that is also a *functional*
    # source constraint (a partial equality), namely equality on the core {0,1}.
    return {(0, 0), (1, 1)}


# ------------------------------------------------------------------- CHECK 2
def check2(kmax=5):
    """A_z = {(0,0),(1,1)}: SLC only names the 0- and 1-fibres, so the pairing
    at a neighbour is unconstrained beyond the block/non-block type, and the
    marginal law over right vertices can be exactly uniform."""
    for k in range(2, kmax + 1):
        sigma = list(range(2 * k))
        Ps = list(pairings(sigma))
        reachable = set()
        for P in Ps:
            for h in maps_from_pairing(P):
                # SLC over A_z={(0,0),(1,1)} with h_u = h_{u'} = h is automatic.
                reachable.add(pairing_of(h, sigma))
        check(len(reachable) == len(Ps),
              f"CHECK 2: k={k} only {len(reachable)}/{len(Ps)} pairings SLC-feasible")
        # the two SLC types partition the pairings and have the right masses
        blk = [P for P in Ps if frozenset({0, 1}) in P]
        check(Fraction(len(blk), len(Ps)) == Fraction(1, 2 * k - 1),
              f"CHECK 2: k={k} block-type mass is not 1/(2k-1)")
        print(f"CHECK 2  k={k}: all {len(Ps)} pairings of [{2*k}] are SLC-feasible "
              f"at a non-(Full) window; block type has mass 1/{2*k-1}")


# ------------------------------------------------------------------- CHECK 3
def check3(A, k=2):
    sigma = list(range(2 * k))
    comps, X, F, full = window_data(A, sigma)
    check(not full, "CHECK 3: witness window is (Full)")
    check(F == set(), "CHECK 3: witness window forces a pair")
    check(X == {0, 1} and set(sigma) - X, "CHECK 3: X is not a proper subset")
    print(f"CHECK 3  A_z = {sorted(A)}: forced partial pairings N_j(u) = 0 for all "
          f"j >= 1, so bound (3) gives phi_W <= 0;")
    print(f"         but X_(uu') = {sorted(X)} != Sigma, so "
          f"Pr[X_(u_0 u) != Sigma_(u_0)] = 1.  The entropy count prices forced")
    print(f"         pairings only and is blind to a window that omits labels.")


# ------------------------------------------------------------------- CHECK 4
def dummy_law(k):
    """Law of h_(u_i z)(2) at a neighbour, per SLC type, for the wrapper below.

    Block type   ({0,1} is a block of P_i): the {0,1}-fibre is named 0 at every
                 neighbour (SLC); the other k-1 fibres are named by a uniform
                 bijection onto {1..k-1}.
    Nonblock type: fibre(0) -> 0 and fibre(1) -> 1 (SLC); the other k-2 fibres
                 are named by a uniform bijection onto {2..k-1}.
    Both are computed by exact enumeration over pairings and namings.
    """
    sigma = list(range(2 * k))
    laws = {}
    for typ in ('block', 'nonblock'):
        cnt = {m: 0 for m in range(k)}
        tot = 0
        for P in pairings(sigma):
            is_blk = frozenset({0, 1}) in P
            if (typ == 'block') != is_blk:
                continue
            for h in maps_from_pairing(P):
                if is_blk:
                    if h[0] != 0:
                        continue
                else:
                    if h[0] != 0 or h[1] != 1:
                        continue
                cnt[h[2]] += 1
                tot += 1
        laws[typ] = {m: Fraction(c, tot) for m, c in cnt.items()}
        check(sum(laws[typ].values()) == 1, f"CHECK 4: law for {typ} k={k} not normalised")
    return laws


def exp_max_count(law, d, k):
    """E[max_m #{i <= d : h_i(2) = m}] with the h_i(2) i.i.d. from `law`."""
    states = {tuple([0] * k): Fraction(1)}
    for _ in range(d):
        nxt = {}
        for st, p in states.items():
            for m in range(k):
                if law[m] == 0:
                    continue
                s2 = list(st)
                s2[m] += 1
                s2 = tuple(s2)
                nxt[s2] = nxt.get(s2, Fraction(0)) + p * law[m]
        states = nxt
    return sum(p * max(st) for st, p in states.items())


def check4():
    print("CHECK 4  explicit non-(Full) wrapper: source variables u_1..u_d with")
    print("         alphabet [2k], one window per right vertex certifying")
    print("         'all u_i equal and in {0,1}', i.e. A_z = {(0..0),(1..1)}.")
    print("         beta = 0, phi_W = 0, every left vertex fully rich.")
    print("         L = the dummy labelling u_i -> 2 for every i.")
    print("           k   d   val_W(L)   val_D(L)=val_U(L)   val_Ut(L)-phi_W")
    worst = Fraction(0)
    for k in (2, 3, 4):
        laws = dummy_law(k)
        wblock = Fraction(1, 2 * k - 1)
        for d in (2, 4, 8):
            vW = (wblock * exp_max_count(laws['block'], d, k)
                  + (1 - wblock) * exp_max_count(laws['nonblock'], d, k)) / d
            vD = Fraction(1, d)          # only u_0 = u accepts, R = {(0,0),(1,1)}
            vUt = Fraction(1)            # identity completion accepts L = 2
            phi = Fraction(0)
            check(vW < vUt - phi,
                  f"CHECK 4: k={k} d={d} chain did not fail")
            check(vD < vUt - phi,
                  f"CHECK 4: k={k} d={d} val_U >= val_Ut - phi held")
            worst = max(worst, vUt - phi - vW)
            print(f"           {k}  {d:2d}   {float(vW):.4f}     "
                  f"{float(vD):.4f}              {float(vUt - phi):.4f}")
        lim = max(laws['nonblock'].values())
        lim_blk = max(laws['block'].values())
        limit = wblock * lim_blk + (1 - wblock) * lim
        print(f"           k={k}: lim_(d->inf) val_W(L) = {limit} "
              f"= {float(limit):.4f}, so the gap tends to {float(1 - limit):.4f}")
    check(worst > Fraction(1, 5), "CHECK 4: margin too small to be a real failure")
    print(f"         largest observed violation of val_W >= val_Ut - phi_W: "
          f"{float(worst):.4f}")


# ------------------------------------------------------------------- CHECK 5
def check5(trials=4000):
    """Control: on (Full) windows over Sigma=[4] the implication always holds,
    so the step used in the claim's (2) is available exactly there."""
    sigma = list(range(4))
    all_maps = [h for P in pairings(sigma) for h in maps_from_pairing(P)]
    seen = 0
    for _ in range(trials):
        A = set()
        for a in sigma:
            A.add((a, random.choice(sigma)))
        for _ in range(random.randint(0, 6)):
            A.add((random.choice(sigma), random.choice(sigma)))
        comps, X, F, full = window_data(A, sigma)
        if not full:
            continue
        feas = [(hu, hv) for hu in all_maps for hv in all_maps
                if all(hu[a] == hv[b] for (a, b) in A)]
        if not feas:
            continue
        seen += 1
        check(all(F for a in sigma if a not in X),
              f"CHECK 5: (Full) window {sorted(A)} broke the implication")
        for (L, R) in comps:
            check(len(L) <= 2 and len(R) <= 2,
                  f"CHECK 5: component lemma failed on {sorted(A)}")
    check(seen > 100, "CHECK 5: too few feasible (Full) windows sampled")
    print(f"CHECK 5  control: {seen} random SLC-feasible (Full) windows, "
          f"component lemma and the implication hold on every one")


if __name__ == '__main__':
    witness = check1()
    check2()
    check3(witness, k=2)
    check4()
    check5()
    if FAIL:
        print("\nFAILURES:")
        for f in FAIL:
            print("  -", f)
        raise SystemExit(1)
    print("\nALL CHECKS PASS -- (Full) is load-bearing in "
          "window-certified-richness-is-conserved-modulo-merges")
