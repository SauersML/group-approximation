"""Tables and meridian generators for cchelly.c, for any linear diagram of search.DIAGRAMS.
usage: python3 dumpgen.py NAME OUTPREFIX
X = S - {s_1}, Y = S - {s_n}, Z = X cap Y.  For each reflection r of W_T - W_Z (T = Y for F, T = X for N) the generator
is w s^2 w^-1 (w a positive lift, w in W_T, s in T, r = w s w^-1, l(w) minimal, first in BFS order): the meridian of
the wall of r along a positive path, so it lies in P_T and in the kernel of the retraction onto P_Z.
For H4 this reproduces the letters of chelly.py up to naming (checked by --check)."""
import sys
sys.path.insert(0, '/home/user/group-approximation/experiments/h4-artin-complex-6cycles-2026-09-17')
from garside import Coxeter, Artin
from search import DIAGRAMS
name, pre = sys.argv[1], sys.argv[2]
n, md = DIAGRAMS[name]
W = Coxeter(n, md); G = Artin(W)
full = (1 << n) - 1; X = full & ~1; Y = full & ~(1 << (n - 1)); Z = X & Y
def mer(T):
    order = sorted([w for w in range(W.N) if W.supp[w] & ~T == 0], key=lambda w: (W.length[w], W.word[w]))
    seen = {}
    for w in order:
        for s in range(n):
            if not (T >> s) & 1 or W.length[W.rmul[w][s]] < W.length[w]:
                continue
            r = W.mul(W.rmul[w][s], W.inv[w])
            if r in seen or W.supp[r] & ~Z == 0:
                continue
            seen[r] = [i + 1 for i in W.word[w]] + [s + 1, s + 1] + [-(i + 1) for i in reversed(W.word[w])]
    return list(seen.values())
FWs, NWs = mer(Y), mer(X)
with open(pre + '.tab', 'w') as f:
    f.write(f"{W.n} {W.N} {W.w0} {X} {Y} {Z}\n")
    for w in range(W.N):
        f.write(' '.join(map(str, [W.length[w], W.inv[w], W.ld[w], W.rd[w], W.supp[w], W.tau[w]] + W.lmul[w] + W.rmul[w]
                                    + [len(W.word[w])] + list(W.word[w]))) + '\n')
with open(pre + '.gens', 'w') as f:
    for L, c in ((FWs, 'p'), (NWs, 'x')):
        f.write(f"{2 * len(L)}\n")
        for i, wd in enumerate(L):
            g = G.word(wd)
            for (lab, h) in ((f"{c}{i}", g), (f"{c}{i}'", G.inv(g))):
                f.write(' '.join(map(str, [lab, h[0], len(h[1])] + list(h[1]))) + '\n')
print(name, 'W', W.N, 'F-letters', len(FWs), 'N-letters', len(NWs), flush=True)
for L, c in ((FWs, 'p'), (NWs, 'x')):
    for i, wd in enumerate(L):
        print(f"  {c}{i} = {wd}")
