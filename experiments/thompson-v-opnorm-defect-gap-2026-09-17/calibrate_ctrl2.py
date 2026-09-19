"""Calibration of the local search in delta_n.py on a pattern that is KNOWN to contain D = 0.

CTRL2 words (../thompson-v-models/rel_CTRL2.txt) are trivial in PSL(2,17) for the generators a, b, c of
gen_ctrl2.log (right action on the 18 points of P^1(F_17)).  rho(x) = M(x)^T, with M the permutation matrix
e_i -> e_{x(i)}, is a homomorphism for that convention; restricted to the orthogonal complement of the
constants it is the 17-dimensional Steinberg representation St, an exact nontrivial irreducible
representation of G0 with D(St) = 0.

This script (1) checks D(St) = 0, (2) computes the S4- and S3-multiplicity pattern of St, and (3) runs
minimize_batch from delta_n.py on that single pattern from random starts.  If the search does not find a
small D here, its upper bounds for V in the same dimension range carry no evidential weight.

Usage: python3 calibrate_ctrl2.py [--restarts 8] [--iters 600] [--hs_warm 400]
"""
import argparse, json, os, sys, time
import numpy as np
import torch

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import delta_n as dn  # noqa: E402

LOG = os.path.join(dn.MODELS, "gen_ctrl2.log")


def perm_from_log(name):
    for line in open(LOG):
        if line.startswith(name + " ="):
            return tuple(int(x) for x in line.split("=", 1)[1].strip().strip("()").split(","))
    raise KeyError(name)


def group_pairs(gens_irr, gens_rep):
    """All pairs (irr(g), rep(g)) for g in the finite group generated, by BFS on the pair."""
    key = lambda M: tuple(np.round(M, 6).ravel())
    start = (np.eye(gens_irr[0].shape[0]), np.eye(gens_rep[0].shape[0]))
    seen, fr, out = {key(start[1])}, [start], [start]
    while fr:
        nf = []
        for x, y in fr:
            for gi, gr in zip(gens_irr, gens_rep):
                z = (x @ gi, y @ gr)
                kz = key(z[1])
                if kz not in seen:
                    seen.add(kz)
                    nf.append(z)
                    out.append(z)
        fr = nf
    return out


def multiplicities(irreps, rep_gens, order):
    mult = {}
    for name, g in irreps.items():
        pairs = group_pairs(g, rep_gens)
        assert len(pairs) == order, (name, len(pairs))
        m = sum(np.trace(x) * np.trace(y) for x, y in pairs) / order
        assert abs(m - round(m)) < 1e-8
        mult[name] = int(round(m))
    return mult


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--restarts", type=int, default=8)
    ap.add_argument("--iters", type=int, default=600)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--hs_warm", type=int, default=0)
    args = ap.parse_args()
    torch.set_num_threads(1)
    words = dn.load_words("CTRL2")
    P = {x: dn.perm_matrix(perm_from_log(x)).T for x in "abc"}
    Q = dn.orth_complement_of_ones(18)
    St = {x: Q.T @ P[x] @ Q for x in "abc"}
    cd = torch.complex128
    t = {x: torch.tensor(St[x], dtype=cd) for x in "abc"}
    D_exact = dn.defects(words, t["a"], t["b"], t["c"]).max().item()
    S4 = {k: dn.diagonalize_a(v)[0] for k, v in dn.s4_irreps().items()}
    S3 = {k: dn.diagonalize_a(v)[0] for k, v in dn.s3_irreps().items()}
    m4 = multiplicities(S4, [St["a"], St["b"]], 24)
    m3 = multiplicities(S3, [St["a"], St["c"]], 6)
    (A4, B4), k = dn.block_sum(S4, m4)
    (A3, C3), k3 = dn.block_sum(S3, m3)
    assert k == k3 and np.allclose(A4, A3)
    t0 = time.time()
    best = dn.minimize_batch(words, [(A4, B4, C3)], k, args.restarts, args.iters, args.seed,
                             hs_warm=args.hs_warm)
    out = {"D_exact_Steinberg": D_exact, "n": 17, "k": k, "pattern_S4": m4, "pattern_S3": m3,
           "restarts": args.restarts, "iters": args.iters, "hs_warm": args.hs_warm, "local_search_best": float(best[0]),
           "elapsed_s": round(time.time() - t0, 1)}
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
