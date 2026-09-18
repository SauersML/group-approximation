"""Dump Coxeter tables and coset-representative balls for the C search (tsearch.c).
usage: python3 dump.py NAME La Lb Lc Lu Lu2 OUTPREFIX
Writes OUTPREFIX.tab (W tables) and OUTPREFIX.reps (balls R_Y(La), R_X(Lb), R_Y(Lc), R_X(Lu), R_X(Lu2))."""
import sys
from search import Setup
name = sys.argv[1]; La, Lb, Lc, Lu, Lu2 = map(int, sys.argv[2:7]); pre = sys.argv[7]
S = Setup(name, 3); W, A = S.W, S.A
with open(pre + ".tab", "w") as f:
    f.write(f"{W.n} {W.N} {W.w0} {S.X} {S.Y} {S.Z}\n")
    for w in range(W.N):
        f.write(" ".join(map(str, [W.length[w], W.inv[w], W.ld[w], W.rd[w], W.supp[w], W.tau[w]] + W.lmul[w] + W.rmul[w] + [len(W.word[w])] + list(W.word[w]))) + "\n")
def ball(mask, L, drop_one):
    R = S.reps(mask, L)
    if drop_one:
        R = [r for r in R if r[0] != A.one]
    return sorted(R, key=lambda r: (len(r[0][1]) + abs(r[0][0]), r[0]))
with open(pre + ".reps", "w") as f:
    for (mask, L, drop) in ((S.Y, La, True), (S.X, Lb, True), (S.Y, Lc, True), (S.X, Lu, False), (S.X, Lu2, False)):
        R = ball(mask, L, drop)
        f.write(f"{len(R)}\n")
        for (g, pw) in R:
            f.write(" ".join(map(str, [g[0], pw, len(g[1])] + list(g[1]))) + "\n")
print(name, "dumped", flush=True)
