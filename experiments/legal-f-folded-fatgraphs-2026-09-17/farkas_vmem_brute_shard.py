"""farkas_vmem_brute.py split into shards, so that each process fits a wall-clock limit on a loaded machine.
The enumeration is farkas_vmem_brute.walk restricted to the polygons whose first (smallest) type d1 satisfies
d1 % K == i; the shards partition the polygons, because every polygon is enumerated once, from its smallest type.
Arithmetic is exact Python integers, as in farkas_vmem_brute.py.

  python3 farkas_vmem_brute_shard.py pass1 cert.json K i out.json       partial R_d and polygon count of shard i
  python3 farkas_vmem_brute_shard.py merge1 cert.json K dir             R = max of the K partial R's -> dir/R.json
  python3 farkas_vmem_brute_shard.py pass2 cert.json K i dir out.json   max shifted charge and count of shard i
  python3 farkas_vmem_brute_shard.py final cert.json K dir              window check and the verdict

Shard files are dir/p1_<i>.json and dir/p2_<i>.json.  The verdict needs: every shard present in both passes,
equal total counts in the two passes, maximum shifted polygon charge <= 0, and z'_norm > 0.
"""
import sys, json, os
import lp_vmem as VM
from ffold import inv


def walk_shard(TY, g, maxval, visit, K, i):
    """farkas_vmem_brute.walk, with the outer loop over first types d1 restricted to d1 % K == i."""
    N = TY.N
    slots = [[] for _ in range(N)]
    for d in range(N):
        for q in TY.bylabel[inv(TY.label[d])]:
            if TY.kind[d] == "-" and TY.kind[q] == "-":
                continue
            for n in TY.succ[q]:
                slots[d].append((q, n))
    gl = [g[TY.label[j]] for j in range(N)]
    km = [TY.kind[j] == "-" for j in range(N)]
    fd = TY.fdart
    count = [0]

    def rec(darts, sl, gs, nminus, nf):
        d1 = darts[0]; d = darts[-1]; k = len(darts)
        for (q, n) in slots[d]:
            if n == d1:
                if k >= 2 and not (nf and k != 2):
                    visit(sl + [(d, q)]); count[0] += 1
                continue
            if n <= d1 or k >= maxval:
                continue
            ga = gl[n]
            if ga in gs or (nminus and km[n]):
                continue
            f2 = nf + fd[n]
            if f2 > 1 or (f2 and k >= 2):
                continue
            rec(darts + [n], sl + [(d, q)], gs | {ga}, nminus + km[n], f2)
    for d1 in range(i, N, K):
        rec([d1], [], {gl[d1]}, int(km[d1]), int(fd[d1]))
    return count[0]


def load(path):
    J = json.load(open(path))
    phi, g, TY, maxval = VM.setup(J["phi0"], J["power"], J["rm"], J["rp"])
    z = [int(v) for v in J["zrows"]]
    zpair = {}
    for a, b, v in J["zpairs"]:
        zpair[(int(a), int(b))] = zpair.get((int(a), int(b)), 0) + int(v)
    return J, g, TY, maxval, z, zpair


def charge(P, zt, zpair):
    s = 0
    for d, q in P:
        s += zt[d]
        s += zpair.get((min(d, q), max(d, q)), 0) * (1 if d < q else -1)
    return s


def main():
    mode, cert, K = sys.argv[1], sys.argv[2], int(sys.argv[3])
    J, g, TY, maxval, z, zpair = load(cert)
    N = TY.N
    if mode == "pass1":
        i, out = int(sys.argv[4]), sys.argv[5]
        R = [0] * N

        def v1(P):
            c = charge(P, z, zpair)
            r = -((-c) // len(P))                  # ceil(c / k), exact
            for d, _ in P:
                if r > R[d]:
                    R[d] = r
        n = walk_shard(TY, g, maxval, v1, K, i)
        json.dump({"K": K, "i": i, "count": n, "R": R}, open(out, "w"))
        print("pass1 shard", i, "of", K, "polygons", n)
    elif mode == "merge1":
        dr = sys.argv[4]
        R = [0] * N; n = 0
        for i in range(K):
            S = json.load(open(os.path.join(dr, "p1_%d.json" % i)))
            assert S["K"] == K and S["i"] == i
            n += S["count"]
            R = [max(a, b) for a, b in zip(R, S["R"])]
        json.dump({"K": K, "count": n, "R": R}, open(os.path.join(dr, "R.json"), "w"))
        print("merged", K, "shards: polygons", n, "darts shifted", sum(1 for r in R if r > 0), "max R", max(R))
    elif mode == "pass2":
        i, dr, out = int(sys.argv[4]), sys.argv[5], sys.argv[6]
        R = json.load(open(os.path.join(dr, "R.json")))["R"]
        zp = [z[d] - R[d] if d < N else z[d] for d in range(len(z))]
        worst = [None]

        def v2(P):
            c = charge(P, zp, zpair)
            if worst[0] is None or c > worst[0]:
                worst[0] = c
        n = walk_shard(TY, g, maxval, v2, K, i)
        json.dump({"K": K, "i": i, "count": n, "worst": worst[0]}, open(out, "w"))
        print("pass2 shard", i, "of", K, "polygons", n, "max shifted charge", worst[0])
    elif mode == "final":
        dr = sys.argv[4]
        Rj = json.load(open(os.path.join(dr, "R.json"))); R = Rj["R"]
        n2, worst = 0, None
        for i in range(K):
            S = json.load(open(os.path.join(dr, "p2_%d.json" % i)))
            assert S["K"] == K and S["i"] == i
            n2 += S["count"]
            if S["worst"] is not None and (worst is None or S["worst"] > worst):
                worst = S["worst"]
        zp = z[:]
        for d in range(N):
            zp[d] -= R[d]
        _, _, ccols = VM.build(TY, [])
        wch = [sum(v * zp[row] for row, v in col.items()) for col in ccols]
        znorm = -max(wch)
        print("phi0", J["phi0"], "m", J["power"], "rm", J["rm"], "rp", J["rp"], "types", N, "shards", K,
              "polygons", Rj["count"], n2, "darts shifted", sum(1 for r in R if r > 0), "max R", max(R))
        print("max polygon charge", worst, "z'_norm", znorm, "max window charge", max(w + znorm for w in wch))
        ok = Rj["count"] == n2 and worst is not None and worst <= 0 and znorm > 0
        print("BRUTE FARKAS", "VERIFIED" if ok else "FAILED", flush=True)
        return 0 if ok else 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
