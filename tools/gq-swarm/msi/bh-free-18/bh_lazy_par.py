#!/usr/bin/env python3
"""Parallel driver for bh_lazy.py: expand the lazy fill tree to a frontier, then solve subtrees in a Pool.
Calibration first: the fully specified default fill must give the same verdict as bh_run.cert2.
Usage: python3 bh_lazy_par.py NPROC DEPTH NODECAP
"""
import sys
import time
from multiprocessing import Pool
import binary_hier as B
import bh_run as H
import bh_lazy as L


def children(assign):
    """Return ('leaf', verdict) or ('split', [assignments])."""
    M = L.make(assign)
    for name, sts, mk in H.CHECKS2:
        try:
            leaves, fails, first = B.exhaust(sts, mk(M), stop=True)
        except L.NeedFill as e:
            used_out = {assign[k] for k in assign if k[0] == e.R}
            used_in = {k[1] for k in assign if k[0] == e.R}
            out = []
            if not e.inv:
                for o in B.FILL_OUT:
                    if o not in used_out:
                        a2 = dict(assign); a2[(e.R, e.key)] = o; out.append(a2)
            elif e.key in B.FILL_OUT and e.key not in used_out:
                for key in L.FILL_KEYS[e.R]:
                    if key not in used_in:
                        a2 = dict(assign); a2[(e.R, key)] = e.key; out.append(a2)
            return ("split", out)
        if fails:
            return ("leaf", name)
    return ("leaf", True)


def sub(args):
    assign, cap = args
    stack = [assign]
    nodes = 0
    dead = {}
    sols = []
    while stack and nodes < cap:
        a = stack.pop()
        nodes += 1
        kind, v = children(a)
        if kind == "split":
            stack.extend(v)
        elif v is True:
            sols.append(sorted(a.items()))
        else:
            dead[v] = dead.get(v, 0) + 1
    return nodes, len(stack), dead, sols


if __name__ == "__main__":
    nproc, depth, cap = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    t0 = time.time()
    full = {}
    for R in range(3):
        for i, key in enumerate(L.FILL_KEYS[R]):
            full[(R, key)] = B.FILL_OUT[B.DEFAULT[R][i]]
    print("calibration lazy(default) =", children(full), " cert2(default) =",
          H.cert2(B.DEFAULT).split(" ")[0], flush=True)
    front = [{}]
    dead = {}
    for d in range(depth):
        nxt = []
        for a in front:
            kind, v = children(a)
            if kind == "split":
                nxt.extend(v)
            elif v is True:
                print("SOLUTION", sorted(a.items()), flush=True)
            else:
                dead[v] = dead.get(v, 0) + 1
        front = nxt
        print("depth %d frontier %d dead %s %.0fs" % (d + 1, len(front), dead, time.time() - t0), flush=True)
    tot_nodes = tot_left = 0
    with Pool(nproc) as pool:
        for i, (n, left, dd, sols) in enumerate(pool.imap_unordered(sub, [(a, cap) for a in front])):
            tot_nodes += n
            tot_left += left
            for k, v in dd.items():
                dead[k] = dead.get(k, 0) + v
            for s in sols:
                print("SOLUTION", s, flush=True)
            if i % 10 == 0 or i == len(front) - 1:
                print("  %d/%d nodes=%d unexplored=%d dead=%s %.0fs" % (i + 1, len(front), tot_nodes, tot_left, dead, time.time() - t0), flush=True)
    print("DONE nodes=%d unexplored=%d dead=%s %.0fs" % (tot_nodes, tot_left, dead, time.time() - t0))
