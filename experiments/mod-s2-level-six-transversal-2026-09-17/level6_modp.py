#!/usr/bin/env python3
"""Modular stage for the level-six census (rs_elim.cpp in modular mode).

For each prime p the file written by `rs_elim NSWITCH modp.txt` holds the
image Phi_p(v) of every twist vector v in Z^n / (L + pZ^n) = F_p^(n - rank_p),
where L is the full relator lattice at the switch point (phase one is exact
unit elimination over Z, so Z^n / L = H_1(M'')).  Consequences, all exact:

  * v, v' in different classes mod p  =>  different classes in H_1;
  * W_p = {w : sum w_i Phi_p(k_i) = 0 mod p} contains W, for every p, hence so
    does W_Q = intersection over a set Q of primes;
  * no transversal (0/1 vector, one 1 per block) in W_Q  =>  none in W;
  * theta = sum_p Phi_p u_p / p (mod Z) lies in Ann(W_Q) <= Ann(W), so
    d(W) <= d(W_Q) <= max_i |theta_i - 1/3|_{R/Z} for any integer u.

Usage: python3 level6_modp.py modp.txt input.txt out.json [cosets.pkl]
(input.txt is the rs_elim input, read only for its selection block; without a
selection block all (coset, twist) pairs in c-major order are assumed.)
"""
import json
import os
import pickle
import sys
import time
from fractions import Fraction

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
SMALL = (2, 3, 5, 7, 11, 13)


def read_modp(path):
    """Blocks: 'p rank r', the r non-pivot column ids, then one line of r
    residues per twist vector (r != 3 is asserted, so headers are unambiguous)."""
    out = {}
    lines = [ln.split() for ln in open(path) if ln.strip()]
    i = 0
    while i < len(lines):
        p, rank, r = map(int, lines[i])
        assert r != 3
        cols = [int(x) for x in lines[i + 1]] if r else []
        i += 2 if r else 1
        rows = []
        while i < len(lines) and len(lines[i]) == r and (r or False):
            rows.append(tuple(int(x) for x in lines[i]))
            i += 1
        out[p] = {"rank": rank, "cols": cols, "rows": rows}
    nv = {len(v["rows"]) for v in out.values()}
    assert len(nv) == 1, nv
    return out


def read_selection(path, nv):
    lines = open(path).read().split("\n")
    while lines and not lines[-1].strip():
        lines.pop()
    sel = []
    i = len(lines) - 1
    while i >= 0 and len(lines[i].split()) == 2:
        sel.append(tuple(map(int, lines[i].split())))
        i -= 1
    if i >= 0 and len(lines[i].split()) == 1 and int(lines[i]) == len(sel) == nv:
        return sel[::-1]
    return [(c, t) for c in range(nv // 10) for t in range(10)]


def transversal_milp(Phi, block, primes, forbid=(), time_limit=3600):
    """0/1 x with one 1 per block and x Phi_p = 0 mod p for p in primes."""
    from scipy.optimize import Bounds, LinearConstraint, milp
    m = len(block)
    blocks = sorted(set(block))
    cons_rows, zcols = [], 0
    mats = []
    for p in primes:
        A = np.array(Phi[p], dtype=float)
        keep = [k for k in range(A.shape[1]) if A[:, k].any()]
        mats.append((p, A[:, keep]))
        zcols += len(keep)
    nvar = m + zcols
    Aeq = np.zeros((zcols, nvar))
    off = 0
    for p, A in mats:
        r = A.shape[1]
        Aeq[off:off + r, :m] = A.T
        Aeq[off:off + r, m + off:m + off + r] = -p * np.eye(r)
        off += r
    Blk = np.zeros((len(blocks), nvar))
    for j in range(m):
        Blk[blocks.index(block[j]), j] = 1
    cons = [LinearConstraint(Aeq, 0, 0), LinearConstraint(Blk, 1, 1)]
    for T in forbid:
        row = np.zeros(nvar)
        row[list(T)] = 1
        cons.append(LinearConstraint(row[None, :], -np.inf, len(T) - 1))
    lb = np.zeros(nvar)
    ub = np.concatenate([np.ones(m), np.full(zcols, float(len(blocks)))])
    res = milp(np.zeros(nvar), constraints=cons, integrality=np.ones(nvar),
               bounds=Bounds(lb, ub), options={"time_limit": time_limit})
    if res.x is None:
        return None, int(res.status)
    return [j for j in range(m) if res.x[j] > 0.5], int(res.status)


def check_transversal(T, Phi, block):
    assert sorted(block[j] for j in T) == sorted(set(block))
    return {p: all(sum(Phi[p][j][k] for j in T) % p == 0
                   for k in range(len(Phi[p][0]))) for p in Phi}


def dp_obstruction(Phi, block, p, coords):
    """Exact: is there one class per block with sum of Phi_p restricted to
    coords equal to 0 mod p?  (Reachable-set dynamic programming.)"""
    s = len(coords)
    size = p ** s
    reach = np.zeros(size, dtype=bool)
    reach[0] = True
    w = np.array([p ** i for i in range(s)], dtype=np.int64)
    for b in sorted(set(block)):
        vals = {int(sum((Phi[p][j][coords[i]] % p) * w[i] for i in range(s)))
                for j in range(len(block)) if block[j] == b}
        idx = np.arange(size, dtype=np.int64)
        digits = [(idx // w[i]) % p for i in range(s)]
        new = np.zeros(size, dtype=bool)
        for v in vals:
            vd = [(v // int(w[i])) % p for i in range(s)]
            tgt = sum(((digits[i] + vd[i]) % p) * w[i] for i in range(s))
            new[tgt[reach]] = True
        reach = new
    return bool(reach[0])


def distance_milp(Phi, primes, time_limit=1800):
    """min t over theta = sum_p Phi_p u_p / p + n, |theta_i - 1/3| <= t."""
    from scipy.optimize import Bounds, LinearConstraint, milp
    m = len(next(iter(Phi.values())))
    blocks = []
    for p in primes:
        A = np.array(Phi[p], dtype=float)
        keep = [k for k in range(A.shape[1]) if A[:, k].any()]
        blocks.append((p, keep, A[:, keep] / p))
    nu = sum(len(k) for _, k, _ in blocks)
    nvar = m + m + nu + 1                      # h, n, u, t
    Aeq = np.zeros((m, nvar))
    Aeq[:, :m] = np.eye(m)
    Aeq[:, m:2 * m] = -np.eye(m)
    off = 2 * m
    for p, keep, A in blocks:
        Aeq[:, off:off + len(keep)] = -A
        off += len(keep)
    A1 = np.zeros((m, nvar))
    A1[:, :m] = np.eye(m)
    A1[:, -1] = -1
    A2 = np.zeros((m, nvar))
    A2[:, :m] = -np.eye(m)
    A2[:, -1] = -1
    c = np.zeros(nvar)
    c[-1] = 1
    lb = np.concatenate([np.full(m, 1 / 3 - 0.5), np.full(m, -20.0),
                         np.zeros(nu), [0]])
    ub = np.concatenate([np.full(m, 1 / 3 + 0.5), np.full(m, 20.0),
                         np.concatenate([np.full(len(k), p - 1.0)
                                         for p, k, _ in blocks]), [0.5]])
    integ = np.concatenate([np.zeros(m), np.ones(m + nu), [0]])
    res = milp(c, constraints=[LinearConstraint(Aeq, 0, 0),
                               LinearConstraint(A1, -np.inf, 1 / 3),
                               LinearConstraint(A2, -np.inf, -1 / 3)],
               integrality=integ, bounds=Bounds(lb, ub),
               options={"time_limit": time_limit})
    if res.x is None:
        return None
    u, off = {}, 2 * m
    for p, keep, _ in blocks:
        u[p] = {k: int(round(res.x[off + i])) for i, k in enumerate(keep)}
        off += len(keep)
    # exact evaluation of the certificate theta
    third = Fraction(1, 3)
    worst, theta = Fraction(0), []
    for i in range(m):
        th = sum(Fraction(Phi[p][i][k] * a, p) for p in u
                 for k, a in u[p].items()) % 1
        theta.append(th)
        dev = abs(th - third)
        dev = min(dev, 1 - dev)
        worst = max(worst, dev)
    return worst, theta, u, float(res.fun), int(res.status)


def main(modp, inp, out, pkl=None):
    if pkl == "-":
        pkl = None
    t0 = time.time()
    raw = read_modp(modp)
    primes = list(raw)
    nv = len(raw[primes[0]]["rows"])
    sel = read_selection(inp, nv)
    res = {"primes": primes, "twist_vectors": nv,
           "rank_mod_p": {str(p): raw[p]["rank"] for p in primes},
           "corank_mod_p": {str(p): len(raw[p]["cols"]) for p in primes}}
    print(res, flush=True)
    key = [tuple(x for p in primes for x in raw[p]["rows"][i]) for i in range(nv)]
    keys = sorted(set(key))
    kid = {k: i for i, k in enumerate(keys)}
    vclass = [kid[k] for k in key]
    m = len(keys)
    rep = [None] * m
    for i, c in enumerate(vclass):
        if rep[c] is None:
            rep[c] = i
    block = [None] * m
    for i, c in enumerate(vclass):
        b = sel[i][1]
        assert block[c] in (None, b), "class over two level-two splittings"
        block[c] = b
    per_p = {str(p): len(set(raw[p]["rows"])) for p in primes}
    res.update({"classes": m, "classes_per_prime": per_p,
                "classes_per_splitting": [block.count(b) for b in range(10)]})
    print(f"classes {m} (per prime {per_p}) per splitting "
          f"{res['classes_per_splitting']} [{time.time()-t0:.0f}s]", flush=True)
    if pkl:
        sys.path.insert(0, HERE)
        from level6_lattice import labels6
        objs = pickle.load(open(pkl, "rb"))["objs"]
        L = labels6(objs, sel)
        for conv, lab in L.items():
            cl, ok = {}, True
            for i, c in enumerate(vclass):
                if cl.setdefault(c, lab[i]) != lab[i]:
                    ok = False
            inj = ok and len(set(cl.values())) == m
            res[f"label_{conv}_constant"] = ok
            res[f"label_{conv}_injective"] = inj
            print(f"labels {conv}: constant {ok} injective {inj}", flush=True)
    Phi = {p: [raw[p]["rows"][rep[c]] for c in range(m)] for p in primes}
    # augmentation: is 1 in the span?  aug(W_p) = pZ or Z per prime
    small = [p for p in SMALL if p in Phi]
    forbid, found = [], None
    for it in range(20):
        T, st = transversal_milp(Phi, block, small, forbid)
        print("transversal mod", small, ":", T, "status", st,
              f"[{time.time()-t0:.0f}s]", flush=True)
        if T is None:
            break
        chk = check_transversal(T, Phi, block)
        print("  check all primes", chk, flush=True)
        if all(chk.values()):
            found = T
            break
        forbid.append(T)
    res["transversal_small_primes"] = found
    res["transversal_status"] = st
    res["transversal_rejected_by_large_primes"] = len(forbid)
    json.dump(res, open(out, "w"), indent=1)
    pickle.dump({"Phi": Phi, "block": block, "keys_rep": rep, "sel": sel,
                 "vclass": vclass}, open(out + ".pkl", "wb"))
    dist = distance_milp(Phi, small) if os.environ.get("DMILP") else None
    if dist is not None:
        worst, theta, u, fun, st = dist
        res["d_WQ_upper_certificate"] = str(worst)
        res["d_WQ_milp"] = fun
        res["d_milp_status"] = st
        res["theta_values"] = sorted(set(str(x) for x in theta))
        print("d(W_Q) <=", worst, "milp", fun, "status", st,
              "theta values", res["theta_values"][:12], flush=True)
    json.dump(res, open(out, "w"), indent=1)
    print(f"done [{time.time()-t0:.0f}s]")


if __name__ == "__main__":
    main(*sys.argv[1:])
