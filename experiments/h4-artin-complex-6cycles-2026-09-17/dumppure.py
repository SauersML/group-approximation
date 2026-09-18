"""Dump pure-braid balls for the single-edge (Case 1) configurations, for tsearch.c.
In the single-edge case pi(omega) = one edge of the Coxeter complex, so a, b, c have images in W_Z;
modulo A_Z on the right they are pure.  Standard generators of the pure group P_T: for each
reflection t = w s w^{-1} of W_T (w of minimal length), A_t = w s s w^{-1} (positive lifts).
usage: python3 dumppure.py NAME La Lb Lc Lu Lu2 OUTPREFIX
  a in PureBall_Y(La), b in PureBall_X(Lb), c in PureBall_Y(Lc) (mod A_Z, identity dropped);
  u in R_X(Lu), R_X(Lu2) (ordinary simple-letter balls, identity kept)."""
import sys
from search import Setup

name = sys.argv[1]; La, Lb, Lc, Lu, Lu2 = map(int, sys.argv[2:7]); pre = sys.argv[7]
S = Setup(name, 3); W, A = S.W, S.A


def pure_gens(mask):
    refl = {}
    for w in sorted((w for w in range(W.N) if W.supp[w] & ~mask == 0), key=lambda w: W.length[w]):
        for s in range(W.n):
            if not (mask >> s) & 1:
                continue
            t = W.mul(W.mul(w, W.lmul[0][s]), W.inv[w])
            if t not in refl:
                g = A.mul(A.mul(A.simple(w), A.simple(W.lmul[0][s])), A.mul(A.simple(W.lmul[0][s]), A.inv(A.simple(w))))
                refl[t] = g
    gens = list(refl.values())
    return gens + [A.inv(g) for g in gens]


def pure_ball(mask, L):
    gens = pure_gens(mask)
    out = {A.coset_key(A.one, S.Z, Nb=8): A.one}
    layer = [A.one]; seen = {A.one}
    for _ in range(L):
        new = []
        for g in layer:
            for h in gens:
                gh = A.mul(g, h)
                if gh in seen:
                    continue
                seen.add(gh); new.append(gh)
                key = A.coset_key(gh, S.Z, Nb=12 * L + 12)
                if key not in out:
                    out[key] = gh
        layer = new
    R = [g for g in out.values() if g != A.one]
    return sorted(R, key=lambda g: (len(g[1]) + abs(g[0]), g))


with open(pre + ".tab", "w") as f:
    f.write(f"{W.n} {W.N} {W.w0} {S.X} {S.Y} {S.Z}\n")
    for w in range(W.N):
        f.write(" ".join(map(str, [W.length[w], W.inv[w], W.ld[w], W.rd[w], W.supp[w], W.tau[w]] + W.lmul[w] + W.rmul[w] + [len(W.word[w])] + list(W.word[w]))) + "\n")


def write_ball(f, R, pws):
    f.write(f"{len(R)}\n")
    for g, pw in zip(R, pws):
        f.write(" ".join(map(str, [g[0], pw, len(g[1])] + list(g[1]))) + "\n")


with open(pre + ".reps", "w") as f:
    for mask, L in ((S.Y, La), (S.X, Lb), (S.Y, Lc)):
        R = pure_ball(mask, L)
        write_ball(f, R, [0] * len(R))
        print("pure ball", mask, L, len(R), flush=True)
    for L in (Lu, Lu2):
        R = sorted(S.reps(S.X, L), key=lambda r: (len(r[0][1]) + abs(r[0][0]), r[0]))
        write_ball(f, [r[0] for r in R], [r[1] for r in R])
print(name, "dumped", flush=True)
