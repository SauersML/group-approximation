#!/usr/bin/env python3
"""Configuration-dependent paradoxical transport on F_2, as SAT per radius.

Lane (d) of notes/agent-coordination-playbook-2026-09-17.md, Section 11.

Concrete non-surjective automaton over F_2 = <a, b>:

    tau(x)(g) = x(g) AND NOT x(g a)          on {0,1}^{F_2}.

The pattern P = (1 at 1, 1 at a) is a Garden of Eden pattern of tau
(y(1) = 1 forces x(a) = 0, y(a) = 1 forces x(a) = 1).  Markers are the sites
where P occurs:  M(x) = { g : x(g) = x(g a) = 1 }, a clopen marker set.

A radius-r marker routing is a table s_1, s_2 : {0,1}^{B_r} -> S (S finite)
applied at each marker site g to the pattern k -> x(g k), k in B_r, sending g
to the two targets g s_1, g s_2.  It is a *collision-free 2-to-1 compression
into the markers* if, for every x, the targets are markers, the two targets
of one source differ, and targets of distinct sources are distinct.

Every constraint is local (collisions only between g and g t with
t in S S^{-1}), so the SAT instance below is satisfiable exactly when such a
global rule with window B_r and displacement set S exists.  The mass-transport
theorem (research/marker-routed-paradoxical-transport-must-collide.md) says it
is UNSAT for every radius; the script confirms it for small radii and runs the
three calibrations that show which hypothesis each step uses:

  C1  budget-respecting markers (M = [x(1)=1, x(a)=0], targets = any site):
      SAT, since sup over invariant measures of 2 mu(M) is 1.
  C2  marker 11 with targets = any site: UNSAT, the constant configuration 1
      has mu(M) = 1 and 2 > 1.
  C3  the end-pointer subshift of finite type over F_2 (every site points to
      one neighbour, its parent; the other three neighbours point back):
      markers = targets = all sites, radius 0.  SAT: two of the three
      children.  This SFT carries no invariant probability measure, which is
      the hypothesis the theorem needs.

Usage:  python3 marker_routing_sat.py            (all instances, ~1-3 min)
        python3 marker_routing_sat.py --quick    (skip the radius-2 ball)
Requires python-sat (pip install python-sat).
"""
import itertools
import random
import sys
import time

try:
    from pysat.solvers import Solver
except ImportError:  # pragma: no cover
    sys.exit("python-sat is required: pip install python-sat")

INV = {'a': 'A', 'A': 'a', 'b': 'B', 'B': 'b'}
LETTERS = ('a', 'A', 'b', 'B')


def mul(u, v):
    w = list(u)
    for c in v:
        if w and w[-1] == INV[c]:
            w.pop()
        else:
            w.append(c)
    return tuple(w)


def inv(u):
    return tuple(INV[c] for c in reversed(u))


def ball(r):
    out = [()]
    frontier = [()]
    for _ in range(r):
        nxt = []
        for u in frontier:
            for c in LETTERS:
                if u and u[-1] == INV[c]:
                    continue
                nxt.append(u + (c,))
        out += nxt
        frontier = nxt
    return out


def name(u):
    return ''.join(u) if u else '1'


# ---------------------------------------------------------------------------
# E1: the Garden of Eden pattern of tau
# ---------------------------------------------------------------------------

def check_garden_of_eden():
    A, AA = ('a',), ('a', 'a')
    sites = [(), A, AA]
    pre = 0
    for bits in itertools.product((0, 1), repeat=3):
        x = dict(zip(sites, bits))
        y1 = x[()] & (1 - x[A])
        ya = x[A] & (1 - x[AA])
        if y1 == 1 and ya == 1:
            pre += 1
    return pre == 0


# ---------------------------------------------------------------------------
# generic instance builder
# ---------------------------------------------------------------------------

def build_and_solve(label, alphabet, window, is_marker, S, target_ok, legal=None, m=2):
    """window: list of group elements (contains 1).
    is_marker(get): get(k) returns x(k) for k in window.
    target_ok(get, s): True iff every extension of the pattern makes s a target
    site (must be decided from the window).
    legal(get): optional local legality (subshift of finite type)."""
    t0 = time.time()
    idx = {k: i for i, k in enumerate(window)}
    pats = []
    for w in itertools.product(alphabet, repeat=len(window)):
        get = (lambda w: (lambda k: w[idx[k]]))(w)
        if legal is not None and not legal(get):
            continue
        if not is_marker(get):
            continue
        pats.append(w)
    nvar = [0]

    def new():
        nvar[0] += 1
        return nvar[0]

    clauses = []
    V = {}  # (pattern index, i, s) -> var
    allowed = []
    for pi, w in enumerate(pats):
        get = (lambda w: (lambda k: w[idx[k]]))(w)
        al = [s for s in S if target_ok(get, s)]
        allowed.append(al)
        for i in range(m):
            vs = []
            for s in al:
                v = new()
                V[(pi, i, s)] = v
                vs.append(v)
            clauses.append(vs)  # at least one (empty clause if none)
            for p, q in itertools.combinations(vs, 2):
                clauses.append([-p, -q])
        for i, j in itertools.combinations(range(m), 2):
            for s in al:
                clauses.append([-V[(pi, i, s)], -V[(pi, j, s)]])
    # collisions between source 1 and source t
    Sset = set(S)
    T = sorted({mul(s, inv(sp)) for s in S for sp in S} - {()}, key=lambda u: (len(u), u))
    X = {}
    for t in T:
        tinv = inv(t)
        overlap = [k for k in window if mul(tinv, k) in idx]
        o_src = [idx[k] for k in overlap]
        o_tgt = [idx[mul(tinv, k)] for k in overlap]
        for pi, w in enumerate(pats):
            o1 = tuple(w[j] for j in o_src)
            o2 = tuple(w[j] for j in o_tgt)
            for s in allowed[pi]:
                # as source at 1 with target s: needs s = t s' for some s' in S
                if mul(tinv, s) in Sset:
                    key = (t, o1, s)
                    if key not in X:
                        X[key] = new()
                    for i in range(m):
                        clauses.append([-V[(pi, i, s)], X[key]])
                # as source at t with target t s (in site-1 coordinates)
                ts = mul(t, s)
                if ts in Sset:
                    key = (t, o2, ts)
                    if key not in X:
                        X[key] = new()
                    for i in range(m):
                        clauses.append([-V[(pi, i, s)], -X[key]])
    nv, nc = nvar[0], len(clauses)
    with Solver(name='cadical153', bootstrap_with=clauses) as sv:
        sat = sv.solve()
        model = sv.get_model() if sat else None
    dt = time.time() - t0
    print(f"  {label}: marker patterns={len(pats)} vars={nv} clauses={nc} -> "
          f"{'SAT' if sat else 'UNSAT'}  ({dt:.1f}s)")
    rule = None
    if sat:
        pos = set(l for l in model if l > 0)
        rule = {}
        for (pi, i, s), v in V.items():
            if v in pos:
                rule.setdefault(pats[pi], {})[i] = s
    return sat, rule


# ---------------------------------------------------------------------------
# the literal lane-(d) instance: markers = Garden of Eden pattern 11 of tau
# ---------------------------------------------------------------------------

A = ('a',)


def full_shift_instance(r, m=2):
    window = ball(r)
    wset = set(window)
    S = [s for s in window if mul(s, A) in wset]

    def is_marker(get):
        return get(()) == 1 and get(A) == 1

    def target_ok(get, s):
        return get(s) == 1 and get(mul(s, A)) == 1

    return build_and_solve(f"ball radius {r}, markers 11, targets markers, m={m}", (0, 1),
                           window, is_marker, S, target_ok, m=m)


def line_instance(R):
    """Sub-family: the rule reads only x(a^j), |j| <= R, targets a^j."""
    def ap(j):
        return tuple('a' * j) if j >= 0 else tuple('A' * (-j))
    window = [ap(j) for j in range(-R, R + 1)]
    wset = set(window)
    S = [s for s in window if mul(s, A) in wset]

    def is_marker(get):
        return get(()) == 1 and get(A) == 1

    def target_ok(get, s):
        return get(s) == 1 and get(mul(s, A)) == 1

    return build_and_solve(f"a-line radius {R}, markers 11, targets markers", (0, 1),
                           window, is_marker, S, target_ok)


def calibration_budget(r=1):
    window = ball(r)
    S = list(window)

    def is_marker(get):
        return get(()) == 1 and get(A) == 0

    sat, rule = build_and_solve(f"C1 ball radius {r}, markers 10, targets any site", (0, 1),
                                window, is_marker, S, lambda get, s: True)
    if sat:
        print("  C1 solver rule verified on random configurations:",
              verify_full_shift_rule(rule, window, is_marker, lambda x, g: True))
    return sat, rule


def verify_full_shift_rule(rule, window, is_marker, target_pred, radius=6, trials=30, seed=2):
    """Independent check of a SAT rule: apply it on random binary configurations
    of a large ball and look for a collision among interior sources."""
    rnd = random.Random(seed)
    r = max(len(k) for k in window)
    B = ball(radius)
    for _ in range(trials):
        p1 = rnd.random()
        x = {k: (1 if rnd.random() < p1 else 0) for k in B}
        hits = {}
        for g in ball(radius - r - 2):
            get = lambda k, g=g: x[mul(g, k)]
            if not is_marker(get):
                continue
            w = tuple(get(k) for k in window)
            tg = [mul(g, rule[w][i]) for i in sorted(rule[w])]
            if len(set(tg)) != len(tg):
                return False
            for t in tg:
                if t in hits or not target_pred(x, t):
                    return False
                hits[t] = g
    return True


def calibration_constant(r=1):
    window = ball(r)
    S = list(window)

    def is_marker(get):
        return get(()) == 1 and get(A) == 1

    return build_and_solve(f"C2 ball radius {r}, markers 11, targets any site", (0, 1),
                           window, is_marker, S, lambda get, s: True)


def end_pointer_legal_on(window):
    wset = set(window)
    edges = [(k, c) for k in window for c in LETTERS if mul(k, (c,)) in wset]

    def legal(get):
        for k, c in edges:
            kc = mul(k, (c,))
            if get(k) == c:            # k points to kc: kc must not point back
                if get(kc) == INV[c]:
                    return False
            else:                      # kc is a child of k: it points back
                if get(kc) != INV[c]:
                    return False
        return True
    return legal


def calibration_end_pointer():
    # radius-0 rule; legality checked on B_1 (the rule window is B_1 so that the
    # neighbours' pointers are visible for target certification)
    window = ball(1)
    S = [(c,) for c in LETTERS]
    legal = end_pointer_legal_on(window)
    return build_and_solve("C3 end-pointer SFT, all sites markers, radius 1 window", LETTERS,
                           window, lambda get: True, S,
                           lambda get, s: get(()) != s[0], legal=legal)


def verify_end_pointer_rule(radius=7, trials=20, seed=1):
    """Independent check of the explicit radius-0 rule: children = the first two
    of the three non-parent directions in the order a, A, b, B."""
    rnd = random.Random(seed)
    for _ in range(trials):
        B = ball(radius)
        x = {(): rnd.choice(LETTERS)}
        for k in B[1:]:
            c = k[-1]
            parent = k[:-1]
            if x[parent] == c:        # parent-edge: k is parent's parent
                x[k] = rnd.choice([d for d in LETTERS if d != INV[c]])
            else:                     # k is a child of its word-parent
                x[k] = INV[c]
        hits = {}
        for g in ball(radius - 1):
            kids = [d for d in LETTERS if d != x[g]][:2]
            for d in kids:
                tgt = mul(g, (d,))
                if tgt in hits:
                    return False
                hits[tgt] = g
    return True


def main():
    quick = '--quick' in sys.argv
    print("E1 Garden of Eden: pattern (1,1) on {1,a} has no tau-preimage:", check_garden_of_eden())
    print("E2 literal instances (collision-free 2-to-1 compression into the markers):")
    for R in range(1, 7):
        line_instance(R)
    full_shift_instance(1)
    if not quick:
        full_shift_instance(2)
    print("Sanity (m = 1, injective routing into the markers; the identity works):")
    full_shift_instance(1, m=1)
    print("Calibrations:")
    calibration_budget(1)
    calibration_constant(1)
    sat, rule = calibration_end_pointer()
    print("  C3 explicit radius-0 rule verified on random end-pointer configurations:",
          verify_end_pointer_rule())


if __name__ == '__main__':
    main()
