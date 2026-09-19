#!/usr/bin/env python3
"""b_1 of M_8 = pi^-1(Gamma(8)) through Shapiro over A = Gamma(4)/Gamma(8).

M_8 is normal in M_4 with quotient A = Gamma(4)/Gamma(8) = sp4(F_2) = F_2^10
(Torelli lies in M_8).  By Shapiro,

    H_1(M_8; Q) = (+)_{chi in A^}  H_1(M_4; Q_chi),

and conjugation by Mod(S_2) permutes the characters through the action of
Sp_4(F_2) on sp4(F_2) (X -> g X g^-1), so dim H_1(M_4; Q_chi) is constant on
orbits.  M_4 = K4 inside Pbar (Birman-Hilden, -I not in Gamma(4)).  For each
orbit representative f, S = ker f has codimension one and the twisted
component chi_f is component k = 1 of characters.twisted for S; its cokernel
is H_1(K4; Z_chi) + Z (relative class).  Odd torsion of H_1(M_8) is the sum
of the odd torsion of the H_1(K4; Z_chi).

    python3 level8_betti.py out.json            (all orbit representatives)
    python3 level8_betti.py out.json orbits     (orbits only)
"""
import itertools
import json
import os
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
os.environ.setdefault("CHAR_RANKS_ONLY", "1")
import between48 as B48  # noqa: E402
import characters as CH  # noqa: E402
import groupring as GR  # noqa: E402


def coords(basis):
    """Solve X = sum c_i b_i over F_2 (b_i flattened 4x4)."""
    B = np.array(basis) % 2          # 10 x 16
    table = {}
    for c in itertools.product((0, 1), repeat=len(basis)):
        v = (np.array(c) @ B) % 2
        table[tuple(v)] = np.array(c)
    return table


def action_matrices(basis):
    table = coords(basis)
    mats = []
    for i in range(1, 6):
        g = B48.sigma_mat(i) % 2
        gi = B48.sigma_mat(-i) % 2
        assert ((g @ gi) % 2 == np.eye(4, dtype=np.int64)).all()
        cols = []
        for b in basis:
            X = np.array(b).reshape(4, 4)
            Y = (g @ X @ gi) % 2
            cols.append(table[tuple(Y.flatten())])
        mats.append(np.array(cols).T % 2)   # coordinates: c -> T c
    return mats


def functional_orbits(mats):
    # f acts on coordinates c by f.c; (g.f)(c) = f(T^-1 c), i.e. f -> f T^-1
    inv = []
    for T in mats:
        # T has finite order over F_2; T^-1 = T^(m-1)
        P, m = T.copy(), 1
        while not (P == np.eye(10, dtype=np.int64)).all():
            P = (P @ T) % 2
            m += 1
        Ti = np.eye(10, dtype=np.int64)
        for _ in range(m - 1):
            Ti = (Ti @ T) % 2
        inv.append(Ti)
    seen, orbits = set(), []
    for bits in itertools.product((0, 1), repeat=10):
        f = tuple(bits)
        if not any(f) or f in seen:
            continue
        orb, stack = {f}, [f]
        while stack:
            x = np.array(stack.pop())
            for Ti in inv:
                y = tuple((x @ Ti) % 2)
                if y not in orb:
                    orb.add(y)
                    stack.append(y)
        seen |= orb
        orbits.append((min(orb), len(orb)))
    return orbits


def kernel_S(basis, f):
    ker = []
    for c in itertools.product((0, 1), repeat=10):
        if not (np.array(f) @ np.array(c)) % 2:
            ker.append(sum(ci * b for ci, b in zip(c, basis)) % 2)
    return [np.array(v) for v in B48.rref2(ker)]


def component(args):
    idx, f = args
    t0 = time.time()
    basis = B48.sp4_f2_basis()
    S = kernel_S(basis, f)
    q, rows, targets, owner = CH.lifts(S)
    assert q == 2
    Hm = GR.wht_matrix(q)
    c = CH.twisted(rows, targets, Hm, 1)
    return idx, {"rank": c["rank"], "n": c["n"],
                 "torsion": {str(t): c["tors"].count(t)
                             for t in set(c["tors"])},
                 "odd": c["odd"], "seconds": round(time.time() - t0, 1)}


if __name__ == "__main__":
    out = sys.argv[1]
    basis = B48.sp4_f2_basis()
    mats = action_matrices(basis)
    orbits = functional_orbits(mats)
    sizes = [s for _, s in orbits]
    print("orbit sizes", sizes, "total", sum(sizes), flush=True)
    res = {"orbits": [{"f": list(map(int, f)), "size": s}
                      for f, s in orbits]}
    if len(sys.argv) > 2 and sys.argv[2] == "orbits":
        json.dump(res, open(out, "w"), indent=1)
        raise SystemExit
    import multiprocessing as mp
    nproc = int(os.environ.get("CHAR_PROCS", "1"))
    jobs = list(enumerate(f for f, _ in orbits))
    with mp.get_context("fork").Pool(nproc) as pool:
        for idx, c in pool.imap_unordered(component, jobs):
            res["orbits"][idx].update(c)
            print(f"orbit {idx} size {sizes[idx]}: coker Z^{c['rank']} "
                  f"(b_1^chi = {c['rank'] - 1}), torsion {c['torsion']}, "
                  f"odd {c['odd']} [{c['seconds']}s]", flush=True)
            json.dump(res, open(out, "w"), indent=1)
    b1 = 54 + sum(o["size"] * (o["rank"] - 1) for o in res["orbits"])
    odd = any(o["odd"] for o in res["orbits"])
    res["b1_M8"] = b1
    res["odd_torsion_M8"] = odd
    print("b_1(M_8) =", b1, "odd torsion:", odd, flush=True)
    json.dump(res, open(out, "w"), indent=1)
    print("saved", out)
