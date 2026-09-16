#!/usr/bin/env python3
"""Rank-5 minimal-counterexample census for the K(pi,1) conjecture (2026-09-16).

Lane: counterexample / minimal-counterexample analysis, hole
free-of-infinity-artin-groups-satisfy-k-pi-1.

A Coxeter diagram is stored as (n, lab) with vertices 0..n-1 and lab a dict
{(i,j): m} (i<j) holding the edges m >= 3.  Non-edges mean m = 2.  The label
class 7 stands for every finite m >= 7 (see LABEL COLLAPSE in the artifact and
check_label_collapse below); m = infinity never occurs here.

Parts (each prints a section; exit code 1 on any failed self-check):
  A  shape certificate: all 1024 graphs on 5 labelled vertices; iso classes of
     connected triangle-free graphs whose complement has an embedded 4-cycle.
  B  combinatorial spherical/affine classification of every labelled forest on
     <= 5 vertices (labels 3,4,5,6,7) cross-checked against the Gram matrix.
  C  Vinberg predicate for Lanner / quasi-Lanner simplex diagrams; counts in
     rank 4 and 5; rank-5 quasi-Lanner trees compared with the list decoded from
     arXiv:2405.12068 Figure `fig:quasilanner`.
  D  census of all labellings of P5 and the fork with labels {3,4,5,6,7}:
     predicates for the known theorems, residual list.
Deterministic, single-threaded, runs in well under a minute.
"""
import itertools
import sys
import math

import numpy as np

FAIL = []


def check(cond, msg):
    if not cond:
        FAIL.append(msg)
        print("SELF-CHECK FAILED:", msg)


# ---------------------------------------------------------------- graph utils

def edges_of(lab):
    return sorted(lab)


def adj(n, lab, vs=None):
    vs = set(range(n)) if vs is None else set(vs)
    a = {v: set() for v in vs}
    for (i, j) in lab:
        if i in vs and j in vs:
            a[i].add(j)
            a[j].add(i)
    return a


def components(n, lab, vs=None):
    a = adj(n, lab, vs)
    seen, comps = set(), []
    for v in sorted(a):
        if v in seen:
            continue
        stack, comp = [v], []
        seen.add(v)
        while stack:
            x = stack.pop()
            comp.append(x)
            for y in a[x]:
                if y not in seen:
                    seen.add(y)
                    stack.append(y)
        comps.append(sorted(comp))
    return comps


def induced(lab, vs):
    vs = set(vs)
    return {e: m for e, m in lab.items() if e[0] in vs and e[1] in vs}


def has_triangle(n, lab):
    a = adj(n, lab)
    return any(j in a[i] and k in a[i] and k in a[j]
               for i, j, k in itertools.combinations(range(n), 3))


def complement_has_4cycle(n, lab):
    """Embedded 4-cycle in the complement: distinct a,b,c,d with ab,bc,cd,da
    all non-edges of the diagram (m = 2)."""
    e = set(lab)

    def non(x, y):
        return (min(x, y), max(x, y)) not in e
    for quad in itertools.combinations(range(n), 4):
        a0 = quad[0]
        for b, c, d in itertools.permutations(quad[1:]):
            if non(a0, b) and non(b, c) and non(c, d) and non(d, a0):
                return True
    return False


def canon_graph(n, eset):
    best = None
    for p in itertools.permutations(range(n)):
        key = tuple(sorted(tuple(sorted((p[i], p[j]))) for (i, j) in eset))
        if best is None or key < best:
            best = key
    return best


def canon_labelled(n, lab):
    best = None
    for p in itertools.permutations(range(n)):
        key = tuple(sorted((min(p[i], p[j]), max(p[i], p[j]), m)
                           for (i, j), m in lab.items()))
        if best is None or key < best:
            best = key
    return best


# ------------------------------------------------- combinatorial classification

def path_order(vs, a):
    ends = [v for v in vs if len(a[v]) == 1]
    order, prev = [min(ends)], None
    while len(order) < len(vs):
        cur = order[-1]
        nxt = [w for w in a[cur] if w != prev]
        prev = cur
        order.append(nxt[0])
    return order


def lbl(lab, x, y):
    return lab[(min(x, y), max(x, y))]


SPH_PATHS = {
    3: {(3, 3): "A3", (3, 4): "B3", (3, 5): "H3"},
    4: {(3, 3, 3): "A4", (4, 3, 3): "B4", (3, 4, 3): "F4", (5, 3, 3): "H4"},
    5: {(3, 3, 3, 3): "A5", (4, 3, 3, 3): "B5"},
}
AFF_PATHS = {
    3: {(4, 4): "C~2", (3, 6): "G~2"},
    4: {(4, 3, 4): "C~3"},
    5: {(4, 3, 3, 4): "C~4", (3, 4, 3, 3): "F~4"},
}


def ctype(lab, vs):
    """Type of the connected induced subdiagram on vs: 'S:..', 'A:..' or 'O'.
    Complete for connected diagrams with at most 5 vertices and finite labels."""
    vs = sorted(vs)
    k = len(vs)
    sub = induced(lab, vs)
    a = adj(max(vs) + 1, sub, vs)
    assert len(components(max(vs) + 1, sub, vs)) == 1, "ctype needs connected"
    if k == 1:
        return "S:A1"
    if k == 2:
        m = list(sub.values())[0]
        return "S:I2(%s)" % (">=7" if m >= 7 else m)
    ne = len(sub)
    if ne >= k:  # contains a cycle
        if ne == k and all(len(a[v]) == 2 for v in vs) and all(
                m == 3 for m in sub.values()):
            return "A:A~%d" % (k - 1)
        return "O"
    degs = sorted(len(a[v]) for v in vs)
    if degs[-1] <= 2:
        order = path_order(vs, a)
        L = tuple(lbl(sub, order[i], order[i + 1]) for i in range(k - 1))
        for T in (L, L[::-1]):
            if T in SPH_PATHS.get(k, {}):
                return "S:" + SPH_PATHS[k][T]
            if T in AFF_PATHS.get(k, {}):
                return "A:" + AFF_PATHS[k][T]
        return "O"
    if degs[-1] == 3 and k == 4:
        ls = sorted(sub.values())
        if ls == [3, 3, 3]:
            return "S:D4"
        if ls == [3, 3, 4]:
            return "A:B~3"
        return "O"
    if degs[-1] == 3 and k == 5:
        c = [v for v in vs if len(a[v]) == 3][0]
        d = [w for w in a[c] if len(a[w]) == 2][0]
        e = [w for w in a[d] if w != c][0]
        leaves = [w for w in a[c] if w != d]
        short = sorted(lbl(sub, c, w) for w in leaves)
        cd, de = lbl(sub, c, d), lbl(sub, d, e)
        if short == [3, 3] and cd == 3 and de == 3:
            return "S:D5"
        if short == [3, 3] and cd == 3 and de == 4:
            return "A:B~4"
        return "O"
    if degs[-1] == 4 and k == 5:
        return "A:D~4" if all(m == 3 for m in sub.values()) else "O"
    return "O"


def is_spherical(lab, vs):
    return all(ctype(lab, c).startswith("S")
               for c in components(max(vs) + 1, lab, vs))


def gram(lab, vs):
    vs = sorted(vs)
    idx = {v: i for i, v in enumerate(vs)}
    G = np.eye(len(vs))
    for (i, j), m in induced(lab, vs).items():
        G[idx[i], idx[j]] = G[idx[j], idx[i]] = -math.cos(math.pi / m)
    return np.linalg.eigvalsh(G)


def gram_class(lab, vs, tol=1e-9):
    ev = gram(lab, vs)
    neg = int(np.sum(ev < -tol))
    zero = int(np.sum(abs(ev) <= tol))
    return neg, zero, ev


# ---------------------------------------------------------------- Part A

def part_a():
    print("== Part A: shapes on 5 vertices ==")
    n = 5
    pairs = list(itertools.combinations(range(n), 2))
    classes = {}
    tf_conn = {}
    for mask in range(1 << len(pairs)):
        lab = {pairs[i]: 3 for i in range(len(pairs)) if mask >> i & 1}
        if len(components(n, lab)) != 1 or has_triangle(n, lab):
            continue
        key = canon_graph(n, set(lab))
        tf_conn[key] = lab
        if complement_has_4cycle(n, lab):
            classes[key] = lab
    print("connected triangle-free graphs on 5 vertices, iso classes:",
          len(tf_conn))
    for key in sorted(tf_conn, key=lambda k: (len(k), k)):
        print("  edges=%d degseq=%s complement-4-cycle=%s" % (
            len(key), sorted(len(v) for v in adj(n, tf_conn[key]).values()),
            key in classes))
    names = {}
    for key, lab in classes.items():
        degs = sorted(len(v) for v in adj(n, lab).values())
        names[key] = {(1, 1, 2, 2, 2): "P5", (1, 1, 1, 2, 3): "fork",
                      (1, 1, 1, 1, 4): "K_{1,4}"}.get(tuple(degs), "other")
    print("with an embedded 4-cycle in the complement:", sorted(names.values()))
    check(sorted(names.values()) == ["K_{1,4}", "P5", "fork"],
          "shape list is not {P5, fork, K_{1,4}}")
    # every <=4-vertex triangle-free graph whose complement has a 4-cycle lies
    # in a perfect matching of its 4 vertices
    for mask in range(1 << 6):
        p4 = list(itertools.combinations(range(4), 2))
        lab = {p4[i]: 3 for i in range(6) if mask >> i & 1}
        if complement_has_4cycle(4, lab):
            a = adj(4, lab)
            check(all(len(a[v]) <= 1 for v in a),
                  "4-vertex graph with complement 4-cycle is not a matching")
    print("4-vertex graphs with complement 4-cycle are matchings: checked")


# ---------------------------------------------------------------- Part B

def connected_graph_classes(n, max_edges):
    pairs = list(itertools.combinations(range(n), 2))
    reps = {}
    for mask in range(1 << len(pairs)):
        es = [pairs[i] for i in range(len(pairs)) if mask >> i & 1]
        if len(es) > max_edges:
            continue
        lab = {e: 3 for e in es}
        if len(components(n, lab)) != 1:
            continue
        reps.setdefault(canon_graph(n, set(es)), es)
    return list(reps.values())


def part_b():
    print("== Part B: combinatorial type vs Gram matrix ==")
    labels = (3, 4, 5, 6, 7, 8, 12)
    total, bad, margin_s, margin_o = 0, 0, 1.0, 1.0
    counts = {}
    for n, max_edges in ((2, 1), (3, 3), (4, 6), (5, 6)):
        lab_set = labels if n <= 3 else (3, 4, 5, 6, 7)
        for es in connected_graph_classes(n, max_edges):
            for ls in itertools.product(lab_set, repeat=len(es)):
                lab = dict(zip(es, ls))
                vs = list(range(n))
                t = ctype(lab, vs)
                neg, zero, ev = gram_class(lab, vs)
                if t.startswith("S"):
                    ok = neg == 0 and zero == 0
                    margin_s = min(margin_s, float(ev[0]))
                elif t.startswith("A"):
                    ok = neg == 0 and zero == 1
                else:
                    ok = not (neg == 0 and zero <= 1)
                    if neg > 0:
                        margin_o = min(margin_o, float(-ev[0]))
                total += 1
                counts[(n, t[0])] = counts.get((n, t[0]), 0) + 1
                if not ok:
                    bad += 1
                    print("  MISMATCH", n, lab, t, neg, zero, ev)
    print("labelled connected diagrams checked:", total, "mismatches:", bad)
    print("counts (rank, S/A/O):", dict(sorted(counts.items())))
    print("smallest eigenvalue of a spherical Gram matrix: %.3e" % margin_s)
    print("smallest |negative eigenvalue| of a type-O Gram matrix: %.3e"
          % margin_o)
    check(bad == 0, "combinatorial classification disagrees with Gram matrix")
    # no spherical or connected affine diagram on 4 vertices contains a triangle
    for es in connected_graph_classes(4, 6):
        lab = {e: 3 for e in es}
        if has_triangle(4, lab):
            for ls in itertools.product((3, 4, 5, 6, 7), repeat=len(es)):
                t = ctype(dict(zip(es, ls)), range(4))
                check(t == "O", "4-vertex diagram with triangle typed %s" % t)
    print("4-vertex diagrams containing a triangle are neither spherical nor"
          " affine: checked")


# ---------------------------------------------------------------- Part C

def vinberg(lab, n):
    """('compact'|'noncompact'|None).  Simplex criterion: Gram matrix
    nondegenerate with exactly one negative eigenvalue, and each vertex-deleted
    subdiagram spherical (finite vertex) or connected affine (ideal vertex)."""
    vs = list(range(n))
    if len(components(n, lab)) != 1:
        return None
    ideal = False
    for v in vs:
        rest = [w for w in vs if w != v]
        if is_spherical(lab, rest):
            continue
        comps = components(n, lab, rest)
        if len(comps) == 1 and ctype(lab, rest).startswith("A"):
            ideal = True
            continue
        return None
    neg, zero, _ = gram_class(lab, vs)
    if neg != 1 or zero != 0:
        return None
    return "noncompact" if ideal else "compact"


# rank-5 quasi-Lanner diagrams as decoded from the embedded Ipe data of
# arXiv:2405.12068, Figure fig:quasilanner (vertex/edge/label extraction by a
# script in the scratchpad; see notes).  Trees only, in the notation used here:
# P5 labels along the path; fork labels (cx, cy, cd, de); star labels.
FIGURE_QL_TREES = {
    ("P5", (4, 3, 4, 3)),
    ("fork", (3, 4, 3, 3)),
    ("fork", (3, 4, 3, 4)),
    ("fork", (3, 3, 4, 3)),
    ("star", (3, 3, 3, 4)),
}


def part_c():
    print("== Part C: Vinberg predicate, Lanner and quasi-Lanner counts ==")
    found = {}
    for n in (4, 5):
        tally = {"compact": set(), "noncompact": set()}
        for es in connected_graph_classes(n, 10 if n == 4 else 6):
            lab3 = {e: 3 for e in es}
            if n == 5 and has_triangle(n, lab3):
                continue  # excluded by the Part B triangle check
            for ls in itertools.product((3, 4, 5, 6, 7), repeat=len(es)):
                lab = dict(zip(es, ls))
                r = vinberg(lab, n)
                if r:
                    check(7 not in ls, "label >=7 in a rank-%d simplex" % n)
                    tally[r].add(canon_labelled(n, lab))
        print("rank %d: compact %d, noncompact %d" % (
            n, len(tally["compact"]), len(tally["noncompact"])))
        found[n] = tally
    # Humphreys' tables (from memory, unverified here): H^3 9 + 23, H^4 5 + 9
    check(len(found[4]["compact"]) == 9 and len(found[4]["noncompact"]) == 23,
          "rank-4 simplex counts differ from 9 + 23")
    check(len(found[5]["compact"]) == 5 and len(found[5]["noncompact"]) == 9,
          "rank-5 simplex counts differ from 5 + 9")
    return found


# ---------------------------------------------------------------- Part D

SHAPES = {
    # P5: 0-1-2-3-4, labels along the path
    "P5": ([(0, 1), (1, 2), (2, 3), (3, 4)], lambda L: (L[3], L[2], L[1], L[0])),
    # fork: centre 0, short-arm leaves 1, 2, long arm 0-3-4; labels (cx,cy,cd,de)
    "fork": ([(0, 1), (0, 2), (0, 3), (3, 4)], lambda L: (L[1], L[0], L[2], L[3])),
}


def connected_subsets(lab, n, min_size):
    for k in range(min_size, n + 1):
        for vs in itertools.combinations(range(n), k):
            if len(components(n, lab, vs)) == 1:
                yield vs


def locally_reducible(lab, vs):
    """Every connected spherical induced subdiagram has at most 2 vertices."""
    n = max(vs) + 1
    sub = induced(lab, vs)
    for k in range(3, len(vs) + 1):
        for ws in itertools.combinations(sorted(vs), k):
            if len(components(n, sub, ws)) == 1 and ctype(sub, ws)[0] == "S":
                return False
    return True


def is_star(lab, vs):
    sub = induced(lab, vs)
    a = adj(max(vs) + 1, sub, vs)
    if len(vs) <= 2:
        return True
    centres = [v for v in vs if len(a[v]) == len(vs) - 1]
    return len(sub) == len(vs) - 1 and len(centres) == 1


def cut_predicate(lab, n, comp_ok):
    """Tree criterion: some set E of edges with label >= 6 such that every
    component of the diagram minus the open edges E satisfies comp_ok."""
    heavy = [e for e, m in lab.items() if m >= 6]
    for r in range(len(heavy) + 1):
        for E in itertools.combinations(heavy, r):
            rest = {e: m for e, m in lab.items() if e not in E}
            if all(comp_ok(rest, c) for c in components(n, rest)):
                return True
    return False


def prop_reduction(lab, n, allow_c2=True):
    allowed = {"A:A~3", "A:B~3", "A:C~3", "A:C~4"} | (
        {"A:C~2"} if allow_c2 else set())
    for core in itertools.combinations(range(n), 4):
        if len(components(n, lab, core)) != 1:
            continue
        if ctype(lab, core) not in ("A:A~3", "A:B~3", "A:C~3"):
            continue
        ok = True
        for s in core:
            rest = [w for w in range(n) if w != s]
            for c in components(n, lab, rest):
                t = ctype(lab, c)
                if not (t[0] == "S" or t in allowed):
                    ok = False
        if ok:
            return True
    return False


def flags(lab, n=5):
    vs = list(range(n))
    f = {}
    f["sph"] = is_spherical(lab, vs)
    f["aff"] = ctype(lab, vs)[0] == "A"
    f["LR"] = locally_reducible(lab, vs)
    f["thm1.1"] = cut_predicate(
        lab, n, lambda L, c: is_spherical(L, c) or locally_reducible(L, c))
    f["cor:tree"] = cut_predicate(
        lab, n, lambda L, c: is_spherical(L, c) or is_star(L, c))
    v = vinberg(lab, n)
    f["QL"] = v == "noncompact"
    f["lanner"] = v == "compact"
    f["prop:red"] = prop_reduction(lab, n, True)
    f["prop:red-noC2"] = prop_reduction(lab, n, False)
    f["covered"] = any(f[k] for k in
                       ("sph", "aff", "LR", "thm1.1", "cor:tree", "QL",
                        "prop:red"))
    return f


def dimension(lab, n=5):
    best = 0
    for k in range(1, n + 1):
        for vs in itertools.combinations(range(n), k):
            if is_spherical(lab, vs):
                best = max(best, k)
    return best


def deleted_types(lab, n=5):
    out = []
    for v in range(n):
        rest = [w for w in range(n) if w != v]
        ts = [ctype(lab, c) for c in components(n, lab, rest)]
        out.append("+".join(t for t in ts if t != "S:A1") or "S:A1^4")
    return out


STAR_EDGES = [(0, 1), (0, 2), (0, 3), (0, 4)]


def shape_lab(shape, L):
    es = STAR_EDGES if shape == "star" else SHAPES[shape][0]
    return dict(zip(es, L))


def collapse(L):
    return tuple(min(m, 7) for m in L)


FLAG_ORDER = ("sph", "aff", "LR", "thm1.1", "cor:tree", "QL", "prop:red")
KNOWN_LANNER_TREES = {("P5", (3, 3, 3, 5)), ("P5", (4, 3, 3, 5)),
                      ("P5", (5, 3, 3, 5)), ("fork", (3, 3, 3, 5))}


def part_d(found):
    print("== Part D: census of P5 and fork labellings ==")
    residual = []
    for shape, (es, sym) in SHAPES.items():
        reps = [L for L in itertools.product((3, 4, 5, 6, 7), repeat=4)
                if L <= sym(L)]
        tally = {k: 0 for k in FLAG_ORDER + ("prop:red-noC2", "lanner")}
        first = {k: 0 for k in FLAG_ORDER}
        n_res = 0
        for L in reps:
            lab = shape_lab(shape, L)
            check(complement_has_4cycle(5, lab) and not has_triangle(5, lab),
                  "shape %s lost its complement 4-cycle" % shape)
            f = flags(lab)
            for k in tally:
                tally[k] += f[k]
            for k in FLAG_ORDER:
                if f[k]:
                    first[k] += 1
                    break
            check(f["prop:red"] == f["prop:red-noC2"],
                  "C~2 components matter for %s %s" % (shape, L))
            if not f["covered"]:
                n_res += 1
                residual.append((shape, L, f, lab))
        print("%s: %d labellings up to symmetry" % (shape, len(reps)))
        print("  flag counts:", tally)
        print("  first covering flag (in order %s):" % (FLAG_ORDER,), first)
        print("  residual (no flag):", n_res)
    print("residual list (shape, labels, Lanner?, Gram (neg,zero), dim,"
          " vertex-deleted types, flags that hold):")
    lanner_res = set()
    for shape, L, f, lab in residual:
        neg, zero, ev = gram_class(lab, range(5))
        d = dimension(lab)
        check(d == 4, "residual %s %s has dimension %d" % (shape, L, d))
        if f["lanner"]:
            lanner_res.add((shape, L))
        almost = all(t.startswith("S") for t in
                     (ctype(lab, c) for v in range(5)
                      for c in components(5, lab, [w for w in range(5)
                                                   if w != v])))
        print("  %-4s %s lanner=%s gram=(%d,%d) dim=%d almost-spherical=%s"
              " deleted=%s" % (shape, L, f["lanner"], neg, zero, d, almost,
                               deleted_types(lab)))
    print("residual total:", len(residual), " of which Lanner:",
          len(lanner_res))
    fam = [r for r in residual if 7 in r[1]]
    heavy = [r for r in residual if any(m >= 6 for m in r[1])]
    almost = {(r[0], r[1]) for r in residual
              if all(is_spherical(r[3], [w for w in range(5) if w != v])
                     for v in range(5))}
    print("residual classes containing the label class >=7 (each an infinite"
          " family):", len(fam))
    print("residual classes with some label >= 6:", len(heavy))
    print("almost-spherical residual classes:", len(almost))
    check(almost == lanner_res, "almost-spherical residuals are not the Lanner"
          " ones")
    print("cutting every edge of label >= 6 in a residual class (components as"
          " vertex lists with their induced labels):")
    for shape, L, f, lab in heavy:
        rest = {e: m for e, m in lab.items() if m < 6}
        comps = components(5, rest)
        print("  %-4s %s -> %s" % (shape, L, [
            (c, sorted(induced(rest, c).values()), ctype(rest, c))
            for c in comps if len(c) > 1]))
    for shape, L, f, lab in residual:
        print("RESIDUAL %s %s" % (shape, ",".join(
            ">=7" if m == 7 else str(m) for m in L)))
    check(lanner_res == KNOWN_LANNER_TREES,
          "Lanner residual differs from the four compact 4-simplex trees")
    # quasi-Lanner trees from Part C versus the figure decoding
    ql_trees = {k for k in found[5]["noncompact"] if len(k) == 4}
    fig = {canon_labelled(5, shape_lab(s, L)) for s, L in FIGURE_QL_TREES}
    print("rank-5 quasi-Lanner trees found:", len(ql_trees),
          " decoded from figure:", len(fig), " equal:", ql_trees == fig)
    check(ql_trees == fig, "quasi-Lanner trees differ from figure decoding")
    lan_trees = {k for k in found[5]["compact"] if len(k) == 4}
    known = {canon_labelled(5, shape_lab(s, L)) for s, L in KNOWN_LANNER_TREES}
    print("rank-5 compact simplex trees equal the four named trees:",
          lan_trees == known)
    check(lan_trees == known, "compact simplex trees differ")
    return residual


def check_label_collapse():
    print("== Label collapse: labels 7, 8, 12 give identical flags ==")
    n_checked = 0
    for shape, (es, sym) in SHAPES.items():
        cache = {}
        for L in itertools.product((3, 4, 5, 6, 7, 8, 12), repeat=4):
            C = collapse(L)
            if C not in cache:
                cache[C] = flags(shape_lab(shape, C))
            f = flags(shape_lab(shape, L))
            check(f == cache[C], "collapse fails for %s %s" % (shape, L))
            n_checked += 1
    print("labellings checked:", n_checked)


if __name__ == "__main__":
    part_a()
    part_b()
    found = part_c()
    part_d(found)
    check_label_collapse()
    print("== SELF-CHECK FAILURES:", len(FAIL))
    for m in FAIL:
        print("  ", m)
    sys.exit(1 if FAIL else 0)
