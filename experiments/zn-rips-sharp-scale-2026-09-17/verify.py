"""Independent verifier for uniform.cpp certificates (numpy; shares no code with the search).

Usage: python3 verify.py n r certfile [statefile [budget_seconds]]
With a statefile, the replay stops at a move boundary after budget_seconds (default 900), saves the
current set C and the position, and a rerun with the same arguments resumes (the state records the
certificate's sha256 and (n, r), and is refused if they differ). ACCEPT is printed only at the end.

Lmax = { x in Z^n : |x|_1 <= r, x > 0 }  (x > 0: last nonzero coordinate positive).
The certificate is a sequence of moves on a current set C (initially Lmax):
  D x | w        : x, w in C, w != x, w in hull(0,x), and every z in C with d(z,x) <= r has d(z,w) <= r.
  K x | p m      : then m lines "y | w". Let S = {z in C : z != x, d(z,x) <= r}, p in S, p in hull(0,x).
                   Each line: y, w in S, w != y, w in hull(0,x,y), every z in S with d(z,y) <= r has
                   d(z,w) <= r; then S := S - y. At the end S == {p}.
  After each move, C := C - x.
Accept iff every move checks and the final C is {e_1, ..., e_n}.
"""
import hashlib
import os
import sys
import time

import numpy as np


def main():
    n, r, path = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    state = sys.argv[4] if len(sys.argv) > 4 else None
    budget = float(sys.argv[5]) if len(sys.argv) > 5 else 900.0
    t0 = time.time()
    with open(path, "rb") as f:
        h = hashlib.sha256()
        for chunk in iter(lambda: f.read(1 << 24), b""):
            h.update(chunk)
        sha = h.hexdigest()
    def ball(k, budget_):  # all integer vectors of length k with l^1 norm <= budget_
        if k == 0:
            yield ()
            return
        for v in range(-budget_, budget_ + 1):
            for rest in ball(k - 1, budget_ - abs(v)):
                yield (v,) + rest

    pts = [x for x in ball(n, r) if any(x) and [v for v in x if v][-1] > 0]
    P = np.array(pts, dtype=np.int16)
    idx = {p: i for i, p in enumerate(pts)}
    alive = np.ones(len(pts), dtype=bool)

    def dist(i):
        return np.abs(P - P[i]).sum(axis=1)

    def hull(w, pts_):  # w in hull(0, *pts_)
        for k in range(n):
            vals = [0] + [q[k] for q in pts_]
            if not (min(vals) <= w[k] <= max(vals)):
                return False
        return True

    def parse(line):
        a, b = line.split("|")
        return tuple(map(int, a.split())), b.split()

    nD = nK = nsteps = 0
    pos = 0  # byte offset of the first move not yet replayed
    if state and os.path.exists(state):
        z = np.load(state)
        assert str(z["sha"]) == sha and int(z["n"]) == n and int(z["r"]) == r, "state does not match certificate"
        alive = z["alive"].copy()
        counts = [int(v) for v in z["counts"]]
        if len(counts) == 4:  # older state format: position counted in lines
            with open(path, "rb") as f:
                for _ in range(counts[0]):
                    f.readline()
                counts[0] = f.tell()
        pos, nD, nK, nsteps = counts[:4]
    with open(path, "rb") as f:
        size = os.path.getsize(path)
        f.seek(pos)
        pos0 = pos
        while True:
            if state and pos > pos0 and time.time() - t0 > budget:
                np.savez(state, alive=alive, counts=np.array([pos, nD, nK, nsteps, 1]), sha=sha, n=n, r=r)
                print(f"checkpoint at byte {pos}/{size}: D={nD} K={nK} linksteps={nsteps}; rerun to continue")
                return
            raw = f.readline()
            if not raw:
                break
            line = raw.decode().rstrip("\n")
            kind, rest = line[0], line[1:]
            x, tail = parse(rest)
            i = idx[x]
            assert alive[i], ("dead x", x)
            dx = dist(i)
            if kind == "D":
                w = tuple(map(int, tail))
                j = idx[w]
                assert alive[j] and j != i and hull(w, [x]), ("bad D dominator", x, w)
                nb = alive & (dx <= r)
                assert (dist(j)[nb] <= r).all(), ("D not dominated", x, w)
                nD += 1
            elif kind == "K":
                p, m = tuple(map(int, tail[:n])), int(tail[n])
                mask = alive & (dx <= r)
                mask[i] = False
                sidx = np.nonzero(mask)[0]          # link vertex set S, as indices into P
                Q = P[sidx]
                loc = {int(g): k for k, g in enumerate(sidx)}
                S = np.ones(len(sidx), dtype=bool)  # current S inside the link
                jp = idx[p]
                assert jp in loc and hull(p, [x]), ("bad K survivor", x, p)
                for _ in range(m):
                    y, wt = parse(f.readline().decode())
                    w = tuple(map(int, wt))
                    iy, iw = idx[y], idx[w]
                    assert iy in loc and iw in loc, ("K step outside link", x, y, w)
                    ly, lw = loc[iy], loc[iw]
                    assert S[ly] and S[lw] and ly != lw and hull(w, [x, y]), ("bad K step", x, y, w)
                    nb = S & (np.abs(Q - P[iy]).sum(axis=1) <= r)
                    assert (np.abs(Q[nb] - P[iw]).sum(axis=1) <= r).all(), ("K step not dominated", x, y, w)
                    S[ly] = False
                    nsteps += 1
                assert S.sum() == 1 and S[loc[jp]], ("K link not collapsed to p", x)
                nK += 1
            else:
                raise ValueError(line)
            alive[i] = False
            pos = f.tell()
    final = sorted(tuple(map(int, P[i])) for i in np.nonzero(alive)[0])
    basis = sorted(tuple(int(k == j) for k in range(n)) for j in range(n))
    print(f"n={n} r={r} |Lmax|={len(pts)} D={nD} K={nK} linksteps={nsteps} |K|={len(final)} basis={final == basis}")
    assert final == basis
    print("ACCEPT")


if __name__ == "__main__":
    main()
