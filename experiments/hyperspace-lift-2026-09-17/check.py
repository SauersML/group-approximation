#!/usr/bin/env python3
"""Power-set (hyperspace) lift of cellular automata over Z: injectivity census.

For a CA tau on A^Z with local rule f: A^(r+1) -> A on the window {0,...,r},
the lift Phi_tau on P(A)^Z has local rule F(U_0,...,U_r) = f(U_0 x ... x U_r)
(the image set; empty if some U_i is empty).  Alphabet size 2^|A|.

Facts checked here (see research/power-set-lifts-never-give-binary-power-witnesses.md):
  (1) census: among injective rules on A^Z with essential dependence on >= 2
      coordinates, how many have an injective lift, on all subsets (2^|A| symbols,
      never: the empty set is absorbing) and on nonempty subsets (2^|A| - 1 symbols);
  (2) the one-site collapse criterion (readability) against the census;
  (3) the explicit F_2^2 linear counterexample tau(a,b)_i = (a_i, b_i + a_{i+1}).

Injectivity over Z is decided by the pair graph on states (r-tuples):
non-injective iff some off-diagonal pair state lies on a bi-infinite path.
"""
import itertools
import json
import sys


def injective_on_Z(N, r, rule):
    """rule: dict tuple(len r+1) -> symbol.  Returns True iff CA on [N]^Z is injective."""
    states = list(itertools.product(range(N), repeat=r))
    idx = {s: i for i, s in enumerate(states)}
    V = len(states)
    # pair vertex (i, j); edge (u,v) -> (u', v') where u' = u[1:]+(c,), v' = v[1:]+(d,)
    # and rule[u+(c,)] == rule[v+(d,)]
    adj = [[] for _ in range(V * V)]
    radj = [[] for _ in range(V * V)]
    for i, u in enumerate(states):
        for j, v in enumerate(states):
            a = i * V + j
            for c in range(N):
                oc = rule[u + (c,)]
                for d in range(N):
                    if rule[v + (d,)] == oc:
                        b = idx[u[1:] + (c,)] * V + idx[v[1:] + (d,)]
                        adj[a].append(b)
                        radj[b].append(a)
    n = V * V
    # vertices on a bi-infinite path = those with infinite forward and backward walks
    def infinite_walk_set(g, rg):
        # iteratively delete vertices with no out-edge (in g) among alive vertices
        outdeg = [len(set(g[x])) for x in range(n)]
        alive = [True] * n
        # use multiplicities-free counting
        succ = [set(g[x]) for x in range(n)]
        pred = [set(rg[x]) for x in range(n)]
        stack = [x for x in range(n) if outdeg[x] == 0]
        while stack:
            x = stack.pop()
            if not alive[x]:
                continue
            alive[x] = False
            for p in pred[x]:
                if alive[p]:
                    outdeg[p] -= 1
                    if outdeg[p] == 0:
                        stack.append(p)
        return alive
    fwd = infinite_walk_set(adj, radj)
    bwd = infinite_walk_set(radj, adj)
    for i in range(V):
        for j in range(V):
            if i != j and fwd[i * V + j] and bwd[i * V + j]:
                # off-diagonal on bi-infinite path.  Pair state (u,v) off-diagonal means
                # the two configurations differ somewhere in the window.
                return False
    return True


def essential_coords(N, r, rule):
    ess = []
    for p in range(r + 1):
        dep = False
        for y in itertools.product(range(N), repeat=r + 1):
            for c in range(N):
                z = y[:p] + (c,) + y[p + 1:]
                if rule[z] != rule[y]:
                    dep = True
                    break
            if dep:
                break
        if dep:
            ess.append(p)
    return ess


def lift_rule(N, r, rule, nonempty=False):
    """Alphabet of the lift: subsets of [N] (all 2^N of them, or only the 2^N - 1 nonempty
    ones), relabelled 0..M-1.  Returns (M, rule, labels) with labels[i] the bitmask of symbol i."""
    labels = [U for U in range(1 << N) if (U != 0 or not nonempty)]
    pos = {U: i for i, U in enumerate(labels)}
    M = len(labels)
    members = [[a for a in range(N) if (U >> a) & 1] for U in labels]
    lrule = {}
    for Us in itertools.product(range(M), repeat=r + 1):
        out = 0
        for y in itertools.product(*[members[U] for U in Us]):
            out |= 1 << rule[y]
        lrule[Us] = pos[out]
    return M, lrule, labels


def readable(N, r, rule):
    """One-site collapse criterion: for every symbol a there are a coordinate s and an
    output b in the image of f with f^{-1}(b) contained in {y_s = a}.  If it fails, the
    all-A configuration and the one obtained by deleting a at one site have the same lift image
    (over every group), so the lift is not injective."""
    pre = {}
    for y in itertools.product(range(N), repeat=r + 1):
        pre.setdefault(rule[y], []).append(y)
    for a in range(N):
        ok = False
        for s in range(r + 1):
            for b, ys in pre.items():
                if all(y[s] == a for y in ys):
                    ok = True
                    break
            if ok:
                break
        if not ok:
            return False
    return True


def census(N, r):
    keys = list(itertools.product(range(N), repeat=r + 1))
    stats = {"alphabet": N, "window": r + 1, "rules": 0, "injective": 0,
             "injective_multi_coordinate": 0, "readable_multi_coordinate": 0,
             "lift_injective_multi_coordinate": 0, "lift_injective_single_coordinate": 0,
             "nonempty_lift_injective_multi_coordinate": 0,
             "nonempty_lift_injective_single_coordinate": 0,
             "injective_single_coordinate": 0, "lift_injective_examples": []}
    for vals in itertools.product(range(N), repeat=len(keys)):
        stats["rules"] += 1
        rule = dict(zip(keys, vals))
        ess = essential_coords(N, r, rule)
        if len(ess) == 0:
            continue
        if not injective_on_Z(N, r, rule):
            continue
        stats["injective"] += 1
        M, lrule, _ = lift_rule(N, r, rule)
        M1, lrule1, _ = lift_rule(N, r, rule, nonempty=True)
        lift_inj = injective_on_Z(M, r, lrule)
        lift1_inj = injective_on_Z(M1, r, lrule1)
        if len(ess) >= 2:
            stats["injective_multi_coordinate"] += 1
            if readable(N, r, rule):
                stats["readable_multi_coordinate"] += 1
            if lift_inj:
                stats["lift_injective_multi_coordinate"] += 1
            if lift1_inj:
                stats["nonempty_lift_injective_multi_coordinate"] += 1
                if len(stats["lift_injective_examples"]) < 5:
                    stats["lift_injective_examples"].append(vals)
        else:
            stats["injective_single_coordinate"] += 1
            if lift_inj:
                stats["lift_injective_single_coordinate"] += 1
            if lift1_inj:
                stats["nonempty_lift_injective_single_coordinate"] += 1
    return stats


def linear_counterexample():
    """A = F_2^2 encoded as 2a+b.  tau(a,b)_i = (a_i, b_i + a_{i+1}), window {0,1}.
    X_i = {(0,0),(1,1)} for all i, X'_i = A for all i: same lift image (both all-A)."""
    N, r = 4, 1
    rule = {}
    for y0 in range(4):
        for y1 in range(4):
            a0, b0 = y0 >> 1, y0 & 1
            a1 = y1 >> 1
            rule[(y0, y1)] = 2 * a0 + (b0 ^ a1)
    inj = injective_on_Z(N, r, rule)
    M, lrule, labels = lift_rule(N, r, rule, nonempty=True)
    pos = {U: i for i, U in enumerate(labels)}
    U = pos[(1 << 0) | (1 << 3)]  # {(0,0), (1,1)}
    full = pos[0b1111]
    img_U = labels[lrule[(U, U)]]
    img_full = labels[lrule[(full, full)]]
    return {"tau_injective_on_Z": inj, "image_of_diagonal_config": img_U,
            "image_of_full_config": img_full, "collision": img_U == img_full,
            "readable": readable(N, r, rule),
            "nonempty_lift_injective_on_Z": injective_on_Z(M, r, lrule)}


def main():
    out = {}
    out["linear_counterexample"] = linear_counterexample()
    out["census_binary_window3"] = census(2, 2)
    out["census_ternary_window2"] = census(3, 1)
    json.dump(out, sys.stdout, indent=1, default=list)
    print()


if __name__ == "__main__":
    main()
