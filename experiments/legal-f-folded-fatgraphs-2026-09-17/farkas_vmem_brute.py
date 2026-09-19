"""Independent brute-force re-check of a farkas_vmem.py certificate, in exact Python integers.
It does not use max-plus products.  It walks every typed polygon of the mixed-memory LP one at a time (the
enumeration of lp_memory.polygons, the definition of the LP's polygon columns, streamed instead of stored), in
two passes:
  pass 1: R_d = max(0, max over polygons P through d of ceil(charge(P) / |P|));
  pass 2: with z'_d = z_d - R_d, every polygon has charge'(P) <= 0 (checked, not deduced).
Then every window column has charge <= 0 with z'_norm = -max window charge, and z'_norm > 0 is required.
usage: python3 farkas_vmem_brute.py cert.json
"""
import sys, json
import lp_vmem as VM
from ffold import inv


def walk(TY, g, maxval, visit):
    """call visit(slots) for every legal typed polygon (as lp_memory.polygons, without storing them)."""
    N = TY.N
    slots = [[] for _ in range(N)]
    for d in range(N):
        for q in TY.bylabel[inv(TY.label[d])]:
            if TY.kind[d] == "-" and TY.kind[q] == "-":
                continue
            for n in TY.succ[q]:
                slots[d].append((q, n))
    gl = [g[TY.label[i]] for i in range(N)]
    km = [TY.kind[i] == "-" for i in range(N)]
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
    for d1 in range(N):
        rec([d1], [], {gl[d1]}, int(km[d1]), int(fd[d1]))
    return count[0]


def main():
    J = json.load(open(sys.argv[1]))
    phi, g, TY, maxval = VM.setup(J["phi0"], J["power"], J["rm"], J["rp"])
    N = TY.N
    z = [int(v) for v in J["zrows"]]
    zpair = {}
    for a, b, v in J["zpairs"]:
        zpair[(int(a), int(b))] = zpair.get((int(a), int(b)), 0) + int(v)

    def charge(P, zt):
        s = 0
        for d, q in P:
            s += zt[d]
            key = (min(d, q), max(d, q))
            s += zpair.get(key, 0) * (1 if d < q else -1)
        return s
    R = [0] * N

    def v1(P):
        c = charge(P, z)
        k = len(P)
        r = -((-c) // k)                       # ceil(c / k), exact
        for d, _ in P:
            if r > R[d]:
                R[d] = r
    n1 = walk(TY, g, maxval, v1)
    zp = z[:]
    for d in range(N):
        zp[d] -= R[d]
    worst = [None]

    def v2(P):
        c = charge(P, zp)
        if worst[0] is None or c > worst[0]:
            worst[0] = c
    n2 = walk(TY, g, maxval, v2)
    _, _, ccols = VM.build(TY, [])
    wch = [sum(v * zp[row] for row, v in col.items()) for col in ccols]
    znorm = -max(wch)
    print("phi0", J["phi0"], "m", J["power"], "rm", J["rm"], "rp", J["rp"], "types", N, "polygons", n1, n2,
          "darts shifted", sum(1 for r in R if r > 0), "max R", max(R))
    print("max polygon charge", worst[0], "z'_norm", znorm, "max window charge", max(w + znorm for w in wch))
    ok = n1 == n2 and worst[0] <= 0 and znorm > 0
    print("BRUTE FARKAS", "VERIFIED" if ok else "FAILED", flush=True)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
