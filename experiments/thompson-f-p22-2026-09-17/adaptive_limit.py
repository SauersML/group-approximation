#!/usr/bin/env python3
"""Adaptive-cylinder version of local_limit.py.

Germ space: one-giant n-tuples (critical Boltzmann local limit, see local_limit.py).  A cell is an
n-tuple of partial trees built from LEAF (0), carets (pairs), STAR '*' (arbitrary finite subtree,
mass 2) and one GIANT 'G' (Kesten tree, mass 1); mass = 4^-carets * 2^#STAR.  An a-partition is a
finite refinement tree (refine a STAR into LEAF | (*,*), or G into (G,*) | (*,G)).  Q-cells (k-tuples)
are refined on demand until, for every shape s, split_s(Q-cell) is either undefined on the whole
cell or contained in a single a-cell.  Then

    R(P) = min over unions A of a-cells of 4^d mu_k(S A) / mu_n(A)

by weighted min cut + Dinkelbach (exact rationals).  Refining P lowers R(P); the uniform depth-h
partition reproduces local_limit.py.

Usage: adaptive_limit.py n k depth H          (uniform depth H)
       adaptive_limit.py n k mass t           (refine every cell of mass > 1/t)
       adaptive_limit.py n k mixed H t        (depth H everywhere, then refine cells of mass > 1/t)
"""
import sys, os
from fractions import Fraction
from collections import defaultdict
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import local_limit as ll

STAR, LEAF, GIANT = '*', 0, 'G'


def weight(p):
    return ll.weight(p)


def get(t, path):
    for b in path:
        t = t[b]
    return t


def put(t, path, v):
    if not path:
        return v
    if path[0] == 0:
        return (put(t[0], path[1:], v), t[1])
    return (t[0], put(t[1], path[1:], v))


def refine_children(cell, j, path):
    v = get(cell[j], path)
    if v == STAR:
        kids = [LEAF, (STAR, STAR)]
    elif v == GIANT:
        kids = [(GIANT, STAR), (STAR, GIANT)]
    else:
        raise ValueError("refine on non-star")
    return [cell[:j] + (put(cell[j], path, x),) + cell[j + 1:] for x in kids]


def open_nodes(t, path=()):
    """STAR/G nodes of a partial tree, shallowest first."""
    out = []
    stack = [(t, path)]
    while stack:
        u, p = stack.pop()
        if u in (STAR, GIANT):
            out.append(p)
        elif u != LEAF:
            stack.append((u[1], p + (1,)))
            stack.append((u[0], p + (0,)))
    out.sort(key=lambda p: (len(p), p))
    return out


class Node:
    __slots__ = ("j", "path", "kind", "kids", "cell", "cid")

    def __init__(self, cell):
        self.cell, self.j, self.path, self.kind, self.kids, self.cid = cell, None, None, None, None, None


def crit_from(internal, refine_set):
    """Reproduce a previous partition (internal: cell -> refined node) and refine refine_set further."""
    def crit(cell):
        if cell in internal:
            return internal[cell]
        if cell in refine_set:
            best = None
            for j, tr in enumerate(cell):
                ops = open_nodes(tr)
                if ops and (best is None or len(ops[0]) < len(best[1])):
                    best = (j, ops[0])
            return best
        return None
    return crit


def internal_cells(roots):
    out = {}
    stack = list(roots.values())
    while stack:
        nd = stack.pop()
        if nd.cid is None:
            out[nd.cell] = (nd.j, nd.path)
            stack.extend(nd.kids)
    return out


def build_partition(n, crit):
    """crit(cell) -> (j, path) to refine, or None."""
    roots = {}
    cells = []
    for pos in range(n):
        cell = tuple(GIANT if j == pos else STAR for j in range(n))
        root = Node(cell)
        roots[pos] = root
        stack = [root]
        while stack:
            nd = stack.pop()
            r = crit(nd.cell)
            if r is None:
                nd.cid = len(cells)
                cells.append(nd.cell)
                continue
            j, path = r
            nd.j, nd.path = j, path
            nd.kind = get(nd.cell, (j,) + path) if False else get(nd.cell[j], path)
            nd.kids = [Node(c) for c in refine_children(nd.cell, j, path)]
            stack.extend(nd.kids)
    return roots, cells


def lookup(roots, piece):
    """Return ('cell', cid) or ('refine', j, path)."""
    pos = next(j for j, t in enumerate(piece) if ll.has_giant(t))
    nd = roots[pos]
    while nd.cid is None:
        j, path = nd.j, nd.path
        t = piece[j]
        # walk down path; piece may be coarser above
        for i, b in enumerate(path):
            if t in (STAR, GIANT):
                return ('refine', j, path[:i])
            if t == LEAF:
                raise AssertionError("piece incompatible with partition")
            t = t[b]
        if nd.kind == STAR:
            if t == STAR:
                return ('refine', j, path)
            nd = nd.kids[0] if t == LEAF else nd.kids[1]
        else:
            if t == GIANT:
                return ('refine', j, path)
            nd = nd.kids[0] if ll.has_giant(t[0]) else nd.kids[1]
    return ('cell', nd.cid)


def match(shape, t, qpath, env):
    """Return 'fail', ('refine', qpath) or True; env maps var -> (subtree, qpath)."""
    if isinstance(shape, tuple) and len(shape) == 2 and shape[0] == 'v':
        env[shape[1]] = (t, qpath); return True
    if t == LEAF:
        return 'fail'
    if t in (STAR, GIANT):
        return ('refine', qpath)
    r = match(shape[0], t[0], qpath + (0,), env)
    if r is not True:
        return r
    return match(shape[1], t[1], qpath + (1,), env)


def build_network(n, k, roots, cells):
    shapes = ll.forests(n, k)
    classes = defaultdict(Fraction)
    nq = 0
    for pos in range(k):
        stack = [tuple(GIANT if j == pos else STAR for j in range(k))]
        while stack:
            q = stack.pop()
            sig = set()
            refine = None
            for shape in shapes:
                env = {}
                res = True
                for i in range(k):
                    res = match(shape[i], q[i], (i,), env)
                    if res is not True:
                        break
                if res == 'fail':
                    continue
                if res is not True:
                    refine = res[1]; break
                piece = tuple(env[j][0] for j in range(n))
                lk = lookup(roots, piece)
                if lk[0] == 'cell':
                    sig.add(lk[1])
                else:
                    _, j, path = lk
                    qp = env[j][1]
                    refine = qp + path; break
            if refine is not None:
                i, path = refine[0], refine[1:]
                stack.extend(refine_children(q, i, path))
                continue
            nq += 1
            if sig:
                w = Fraction(1)
                for t in q:
                    w *= weight(t)
                classes[frozenset(sig)] += w
    return classes, nq


def check_transport(n, k, cells, classes):
    d = n - k
    tot_a = sum(weight_cell(c) for c in cells)
    assert tot_a == n * 2 ** (n - 1), tot_a


def weight_cell(c):
    w = Fraction(1)
    for t in c:
        w *= weight(t)
    return w


def crit_depth(H):
    def crit(cell):
        best = None
        for j, t in enumerate(cell):
            for p in open_nodes(t):
                if len(p) < H and (best is None or len(p) < len(best[1])):
                    best = (j, p)
                break
        return best
    return crit


def crit_mass(t, H=0):
    thr = Fraction(1, t)

    def crit(cell):
        best = None
        for j, tr in enumerate(cell):
            ops = open_nodes(tr)
            if ops and (best is None or len(ops[0]) < len(best[1])):
                best = (j, ops[0])
        if best is None:
            return None
        if len(best[1]) < H or weight_cell(cell) > thr:
            return best
        return None
    return crit


def run(n, k, crit, verbose=True):
    roots, cells = build_partition(n, crit)
    classes, nq = build_network(n, k, roots, cells)
    d = n - k
    left = {c: weight_cell(c) for c in cells}
    assert sum(left.values()) == n * 2 ** (n - 1)
    allr = Fraction(4 ** d) * sum(classes.values()) / sum(left.values())
    r, A = ll.optimize({i: left[c] for i, c in enumerate(cells)},
                       {sig: w for sig, w in classes.items()}, d)
    if verbose:
        print(f"S({n}->{k}) a-cells={len(cells)} Q-cells={nq} classes={len(classes)} ratio(all)={allr} "
              f"R={r} ~ {float(r):.6f} chosen={len(A)}")
    run.last = (roots, cells, classes, set(A))
    return r, [cells[i] for i in A], cells


def iterate(n, k, H, rounds, neighbors):
    """Start from depth H; each round refine the excluded cells (and, if neighbors, every chosen cell
    sharing an image class with an excluded cell)."""
    import time
    crit = crit_depth(H)
    for rd in range(rounds):
        t0 = time.time()
        print(f"round {rd}: ", end='', flush=True)
        run(n, k, crit)
        roots, cells, classes, A = run.last
        excl = {i for i in range(len(cells)) if i not in A}
        ref = set(excl)
        if neighbors:
            for sig in classes:
                if sig & excl:
                    ref |= sig
        print(f"  elapsed {time.time() - t0:.1f}s refine {len(ref)}", flush=True)
        crit = crit_from(internal_cells(roots), {cells[i] for i in ref})


if __name__ == "__main__":
    import time
    n, k, mode = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    if mode == 'iterate':
        iterate(n, k, int(sys.argv[4]), int(sys.argv[5]), sys.argv[6] == '1')
        sys.exit(0)
    if mode == 'depth':
        crits = [(f"depth {sys.argv[4]}", crit_depth(int(sys.argv[4])))]
    elif mode == 'mass':
        crits = [(f"mass 1/{t}", crit_mass(int(t))) for t in sys.argv[4].split(',')]
    else:
        crits = [(f"depth {sys.argv[4]} mass 1/{sys.argv[5]}", crit_mass(int(sys.argv[5]), int(sys.argv[4])))]
    for name, crit in crits:
        t0 = time.time()
        print(name, end=': ', flush=True)
        run(n, k, crit)
        print(f"  elapsed {time.time() - t0:.1f}s", flush=True)
