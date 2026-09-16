"""Exact weight-test certificates (WT1)+(WT2) for census words over Thompson's group V.

Star graph (convention of kl-four-same-sign-corner-words-inject): corner i between t^(e_(i-1))
and t^(e_i) with label g_i is an edge t^(-e_(i-1)) -> t^(e_i).  A closed path is cyclically reduced
if no step (j,d) is followed (cyclically) by (j,-d).  Its label is the word read along the path
(inverse letters on backward steps).  It is ADMISSIBLE if the label is trivial in V; to be strict
we call it admissible if the word OR its reversal is trivial (both product conventions).

A weight theta >= 0 passes if (WT1) sum_i (1 - theta_i) >= 2 and (WT2) every admissible cycle has
weight >= 2.  The certificate here uses rational theta >= mu > 0, so (WT2) is checked exactly by
enumerating ALL cyclically reduced closed paths of weight < 2 (length < 2/mu).

Modes:
  profile IN OUT LMAX     necessary condition from admissible cycles of length <= LMAX (theta >= 0)
  certify IN OUT [MODE]   search theta, verify exactly, write WEIGHT lines with theta;
                          MODE = all (default) | pos (all theta >= 1/4) | zero (one zero edge)
"""
import sys
import time
import math
from fractions import Fraction
import numpy as np
from scipy.optimize import linprog
import os
# vgroup.py and certify.py are the census scripts (md5 5a57c59b..., abd5af53...), imported unchanged
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "kl-thompson-v-census"))
import vgroup as V
from certify import parse, E, power_period

INV = {"a": "a", "b": "B", "B": "b", "c": "c", "1": "1"}
ID = V.identity()
_ELEM = {"": ID}


def elem(s):
    x = _ELEM.get(s)
    if x is None:
        x = elem(s[:-1]) * E[s[-1]]
        _ELEM[s] = x
    return x


_TRIV = {}


def trivial(s):
    r = _TRIV.get(s)
    if r is None:
        r = (elem(s) == ID) or (elem(s[::-1]) == ID)
        _TRIV[s] = r
    return r


def star_edges(signs, coeffs):
    n = len(signs)
    out = []
    for i in range(n):
        p, c, g = signs[i - 1], signs[i], coeffs[i]
        src = "-" if p > 0 else "+"
        dst = "+" if c > 0 else "-"
        fwd = "" if g == "1" else g
        bwd = "" if g == "1" else INV[g]
        out.append((src, dst, fwd, bwd))
    return out


def moves(edges):
    mv = {"-": [], "+": []}
    for j, (src, dst, fwd, bwd) in enumerate(edges):
        mv[src].append((j, 1, dst, fwd))
        mv[dst].append((j, -1, src, bwd))
    return mv


def closed_paths_upto(edges, lmax):
    """All cyclically reduced closed paths of length 1..lmax (rotations included)."""
    mv = moves(edges)
    res = []

    def rec(v0, v, path, label):
        if path and v == v0:
            j0, d0 = path[0]
            jl, dl = path[-1]
            if not (j0 == jl and d0 == -dl):
                res.append((tuple(path), label))
        if len(path) == lmax:
            return
        for j, d, w, lab in mv[v]:
            if path and path[-1] == (j, -d):
                continue
            path.append((j, d))
            rec(v0, w, path, label + lab)
            path.pop()

    for v0 in "-+":
        rec(v0, v0, [], "")
    return res


def admissible_rows(edges, lmax):
    n = len(edges)
    rows = set()
    for path, label in closed_paths_upto(edges, lmax):
        if trivial(label):
            cnt = [0] * n
            for j, _ in path:
                cnt[j] += 1
            rows.add(tuple(cnt))
    return rows


def lp_min(n, rows, mu):
    if rows:
        A = -np.array(sorted(rows), dtype=float)
        b = -2.0 * np.ones(len(rows))
    else:
        A, b = None, None
    r = linprog(np.ones(n), A_ub=A, b_ub=b, bounds=[(mu, 2.0)] * n, method="highs")
    if r.status != 0:
        return None
    return r.x


def verify(edges, theta, maxbad=1):
    """theta: list of Fractions >= 0 whose zero set is acyclic in the star graph (at most one zero
    edge, and it is not a loop).  Returns (True, None) if every cyclically reduced closed path of
    weight < 2 has nontrivial label, else (False, row of an admissible cycle of weight < 2).
    Termination: consecutive steps along the same non-loop edge are either a backtrack or impossible,
    so at least every second step has weight >= min positive weight."""
    n = len(edges)
    D = 1
    for x in theta:
        D = D * x.denominator // math.gcd(D, x.denominator)
    W = [int(x * D) for x in theta]
    zeros = [j for j in range(n) if W[j] == 0]
    if min(W) < 0 or len(zeros) > 1 or any(edges[j][0] == edges[j][1] for j in zeros):
        raise ValueError("zero set must be at most one non-loop edge")
    cap = 2 * D
    mv = moves(edges)
    bad = []

    def rec(v0, v, path, label, wt):
        if len(bad) >= maxbad:
            return
        if path and v == v0:
            j0, d0 = path[0]
            jl, dl = path[-1]
            if not (j0 == jl and d0 == -dl) and trivial(label):
                cnt = [0] * n
                for j, _ in path:
                    cnt[j] += 1
                bad.append(tuple(cnt))
                return
        for j, d, w, lab in mv[v]:
            if path and path[-1] == (j, -d):
                continue
            nw = wt + W[j]
            if nw >= cap:
                continue
            path.append((j, d))
            rec(v0, w, path, label + lab, nw)
            path.pop()

    for v0 in "-+":
        rec(v0, v0, [], "", 0)
    if bad:
        return False, bad
    return True, None


def lp_min_bounds(n, rows, bounds):
    if rows:
        A = -np.array(sorted(rows), dtype=float)
        b = -2.0 * np.ones(len(rows))
    else:
        A, b = None, None
    r = linprog(np.ones(n), A_ub=A, b_ub=b, bounds=bounds, method="highs")
    if r.status != 0:
        return None
    return r.x


def certify_word(signs, coeffs, mode="all", lmax0=4, iters=10, budget=2.0):
    """Search order: all weights >= mu for mu in 1/2, 1/3, 1/4; then one zero-weight non-loop edge
    with the others >= mu for mu in 1/2, 1/3.  Every returned theta was verified by verify()."""
    t_start = time.time()
    n = len(signs)
    edges = star_edges(signs, coeffs)
    rows = admissible_rows(edges, lmax0)
    nonloops = [j for j in range(n) if edges[j][0] != edges[j][1]]
    def feasible(mu, j0):
        bounds = [(float(mu), 2.0)] * n
        if j0 is not None:
            bounds[j0] = (0.0, 2.0)
        x = lp_min_bounds(n, rows, bounds)
        return x is not None and sum(x) <= n - 2 + 1e-9

    # necessary conditions (monotone in mu), one LP each; they only prune the search
    if not feasible(0, None):
        return None
    configs = []
    if mode in ("all", "pos") and feasible(Fraction(1, 4), None):
        configs += [(Fraction(1, 2), None), (Fraction(1, 3), None), (Fraction(1, 4), None)]
    if mode in ("all", "zero"):
        for j0 in nonloops:
            if feasible(Fraction(1, 3), j0):
                configs += [(Fraction(1, 2), j0), (Fraction(1, 3), j0)]
    for mu, j0 in configs:
        lo = [mu] * n
        if j0 is not None:
            lo[j0] = Fraction(0)
        rws = set(rows)
        for _ in range(iters):
            if time.time() - t_start > budget:
                return None
            x = lp_min_bounds(n, rws, [(float(l), 2.0) for l in lo])
            if x is None:
                break
            theta = [max(Fraction(v).limit_denominator(24), l) for v, l in zip(x, lo)]
            slack = (n - 2) - sum(theta)
            if slack < 0:
                break
            pos = [j for j in range(n) if j != j0]
            theta = [t + (slack / len(pos) if j != j0 else 0) for j, t in enumerate(theta)]
            if j0 is not None:
                theta[j0] = Fraction(0)
            assert sum(1 - t for t in theta) >= 2 and min(theta) >= 0
            if any(sum(c * t for c, t in zip(r, theta)) < 2 for r in rws):
                break
            ok, bad = verify(edges, theta, maxbad=32)
            if ok:
                return theta
            rws.update(bad)
    return None


def profile(inp, outp, lmax):
    stats = {}
    t0 = time.time()
    with open(inp) as f, open(outp, "w") as out:
        for line in f:
            parts = line.split()
            wid, word = parts[0], parts[1]
            signs, coeffs = parse(word)
            n = len(signs)
            rows = admissible_rows(star_edges(signs, coeffs), lmax)
            x = lp_min(n, rows, 0.0)
            val = None if x is None else float(sum(x))
            tag = "POSSIBLE" if (val is not None and val <= n - 2 + 1e-9) else "IMPOSSIBLE"
            stats[tag] = stats.get(tag, 0) + 1
            out.write("%s %s %s %s\n" % (wid, word, tag, "inf" if val is None else "%.4f" % val))
    print("profile", stats, "s", round(time.time() - t0, 1), flush=True)


def certify_file(inp, outp, mode):
    stats = {}
    t0 = time.time()
    with open(inp) as f, open(outp, "w") as out:
        for line in f:
            parts = line.split()
            wid, word = parts[0], parts[1]
            signs, coeffs = parse(word)
            if power_period(signs, coeffs) is not None:
                tag, extra = "SKIP_POWER", ""
            else:
                th = certify_word(signs, coeffs, mode=mode)
                if th is None:
                    tag, extra = "FRONTIER", ""
                else:
                    tag, extra = "WEIGHT", " theta=" + ",".join(str(t) for t in th)
            stats[tag] = stats.get(tag, 0) + 1
            out.write("%s %s %s%s\n" % (wid, word, tag, extra))
    print("certify", stats, "s", round(time.time() - t0, 1), flush=True)


if __name__ == "__main__":
    mode = sys.argv[1]
    if mode == "profile":
        profile(sys.argv[2], sys.argv[3], int(sys.argv[4]) if len(sys.argv) > 4 else 4)
    else:
        certify_file(sys.argv[2], sys.argv[3], sys.argv[4] if len(sys.argv) > 4 else "all")
