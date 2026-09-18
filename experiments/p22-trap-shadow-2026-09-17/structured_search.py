#!/usr/bin/env python3
"""Exhaustive Loewy-3 census over a library of structured Levi layers.

Finite-dimensional reps of J = F_2<S,T|TS=1> factor through Laurent
quotients (TS=1 forces ST=1 in finite dimension), so the natural Levi layers
are the EL_2(F_2[s,s^-1]/f) modules
    left  N(s):  as=[[1,s],[0,1]], at=[[1,s^-1],[0,1]], c=[[1,0],[1,1]]
    right M(s):  b1=[[1,1],[0,1]], bs=[[1,0],[s,1]], bt=[[1,0],[s^-1,1]]
together with trivial modules, transposes (duals) and tensor products.
Each layer is X (x) Y with X a left module and Y a right module.  For every
triple of layers (W2, W1, W0) the exact solver of loewy3_search decides
whether a Loewy-3 model with gamma_h != 0 exists.

Usage: structured_search.py MAXDIM [extra]
"""
import itertools
import sys

import numpy as np

import gf2
import loewy3_search as L3
import trap_group as TG


def I(k):
    return np.eye(k, dtype=np.uint8)


def Z(k):
    return np.zeros((k, k), dtype=np.uint8)


def blk(A, B, C, D):
    return np.block([[A, B], [C, D]]).astype(np.uint8)


SCALARS = {
    "1": np.array([[1]], dtype=np.uint8),
    "w": np.array([[0, 1], [1, 1]], dtype=np.uint8),   # x^2+x+1
    "j": np.array([[1, 1], [0, 1]], dtype=np.uint8),   # (x+1)^2
}


def left_nat(s):
    k = s.shape[0]
    si = L3.inverse(s)
    return {"as": blk(I(k), s, Z(k), I(k)), "at": blk(I(k), si, Z(k), I(k)),
            "c": blk(I(k), Z(k), I(k), I(k))}


def right_nat(s):
    k = s.shape[0]
    si = L3.inverse(s)
    return {"b1": blk(I(k), I(k), Z(k), I(k)), "bs": blk(I(k), Z(k), s, I(k)),
            "bt": blk(I(k), Z(k), si, I(k))}


def transpose(d):
    return {g: M.T.copy() for g, M in d.items()}


def tensor(d1, d2):
    return {g: L3.kron(d1[g], d2[g]) for g in d1}


def library(side, maxdim):
    names = L3.LEFT if side == "L" else L3.RIGHT
    nat = left_nat if side == "L" else right_nat
    lib = {"1": {g: I(1) for g in names}}
    for sn, s in SCALARS.items():
        d = nat(s)
        lib["N" + sn] = d
        lib["N" + sn + "T"] = transpose(d)
    base = [k for k in lib if k != "1"]
    for a, b in itertools.combinations_with_replacement(base, 2):
        d = tensor(lib[a], lib[b])
        if d[names[0]].shape[0] <= maxdim:
            lib[a + "x" + b] = d
    return {k: v for k, v in lib.items() if v[names[0]].shape[0] <= maxdim}


def dsum(d1, d2):
    out = {}
    for g in d1:
        A, B = d1[g], d2[g]
        M = np.zeros((A.shape[0] + B.shape[0],) * 2, dtype=np.uint8)
        M[:A.shape[0], :A.shape[0]] = A
        M[A.shape[0]:, A.shape[0]:] = B
        out[g] = M
    return out


def layer_pair(LL, RL, x, y):
    return LL[x], RL[y]


def sum_model(LL, RL, spec):
    """spec: three lists of (left name, right name); each layer is the direct
    sum of the tensor layers in its list.  Direct sums of X (x) Y are not of
    the form X (x) Y, so the Model is built from full block matrices."""
    layers = []
    for parts in spec:
        mats = None
        for x, y in parts:
            Ld, Rd = LL[x], RL[y]
            a, b = Ld["as"].shape[0], Rd["b1"].shape[0]
            full = {}
            for g in L3.LEFT:
                full[g] = L3.kron(Ld[g], np.eye(b, dtype=np.uint8))
            for g in L3.RIGHT:
                full[g] = L3.kron(np.eye(a, dtype=np.uint8), Rd[g])
            mats = full if mats is None else dsum(mats, full)
        # encode as a layer with trivial 1-dim right factor: Model multiplies
        # left by I_1 and right by I_(dim), so pass (left=full, right=identity)
        n = mats["as"].shape[0]
        Ld = {g: mats[g] for g in L3.LEFT}
        Rd = {g: np.eye(1, dtype=np.uint8) for g in L3.RIGHT}
        layers.append((Ld, Rd, {g: mats[g] for g in L3.RIGHT}))
    model = L3.Model([(Ld, Rd) for Ld, Rd, _ in layers])
    # overwrite right generators with the true block matrices
    for g in L3.RIGHT:
        M = np.zeros((model.n, model.n), dtype=np.uint8)
        for i in range(3):
            s, e = model.off[i], model.off[i + 1]
            M[s:e, s:e] = layers[i][2][g]
        model.G[g] = M
    return model


def random_sums(trials, extra, seed, maxparts=2, laydim=6):
    rels = TG.TRAP_RELS + (TG.EXTRA_RELS if extra else [])
    LL = library("L", 4)
    RL = library("R", 4)
    tl = [(a, b) for a in LL for b in RL
          if LL[a]["as"].shape[0] * RL[b]["b1"].shape[0] <= 4]
    rng = np.random.default_rng(seed)
    stats = {"trials": 0, "both_nonzero": 0, "hits": 0}
    for _ in range(trials):
        spec = []
        for _i in range(3):
            while True:
                k = int(rng.integers(1, maxparts + 1))
                parts = [tl[int(rng.integers(0, len(tl)))] for _j in range(k)]
                dim = sum(LL[x]["as"].shape[0] * RL[y]["b1"].shape[0] for x, y in parts)
                if dim <= laydim:
                    break
            spec.append(parts)
        model = sum_model(LL, RL, spec)
        res, info = L3.search(model, rels, rng)
        stats["trials"] += 1
        assert info["trapA"] and info["trapB"]
        if info["dimA"] and info["dimB"]:
            stats["both_nonzero"] += 1
        if res is not None:
            stats["hits"] += 1
            print("HIT", spec, info)
            report_hit(model, res[3])
            break
    print("sums", "extra" if extra else "trap-only", stats)


def report_hit(model, U):
    import orbit_trap_check as OT
    size, bad = OT.orbit_trap(model.G, U, gf2.mm, np.array_equal,
                              lambda M: M.tobytes())
    print("  right orbit Z size", size, "violations of (C):", len(bad),
          sorted(set(bad))[:6])
    for g in L3.LEFT + L3.RIGHT:
        print("  ", g, model.G[g].tolist())
    print("   u", U.tolist())


def main():
    if sys.argv[1] == "sums":
        random_sums(int(sys.argv[2]), len(sys.argv) > 3 and sys.argv[3] == "extra",
                    int(sys.argv[4]) if len(sys.argv) > 4 else 0)
        return
    maxdim = int(sys.argv[1])
    extra = len(sys.argv) > 2 and sys.argv[2] == "extra"
    laydim = int(sys.argv[3]) if len(sys.argv) > 3 else 8
    rels = TG.TRAP_RELS + (TG.EXTRA_RELS if extra else [])
    LL = library("L", maxdim)
    RL = library("R", maxdim)
    layers = [(a, b) for a in LL for b in RL
              if LL[a]["as"].shape[0] * RL[b]["b1"].shape[0] <= laydim]
    print("left", list(LL), "right", list(RL), "layers", len(layers))
    rng = np.random.default_rng(0)
    stats = {"triples": 0, "both_nonzero": 0, "hits": 0}
    for top, mid, bot in itertools.product(layers, repeat=3):
        model = L3.Model([(LL[x], RL[y]) for x, y in (top, mid, bot)])
        res, info = L3.search(model, rels, rng)
        stats["triples"] += 1
        assert info["trapA"] and info["trapB"]
        if info["dimA"] and info["dimB"]:
            stats["both_nonzero"] += 1
        if res is not None:
            stats["hits"] += 1
            print("HIT", top, mid, bot, info)
            report_hit(model, res[3])
            if stats["hits"] >= 3:
                break
    print("extra" if extra else "trap-only", stats)


if __name__ == "__main__":
    main()
