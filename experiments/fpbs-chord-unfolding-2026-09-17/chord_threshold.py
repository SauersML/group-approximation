"""Monte Carlo test: do iid graphings with longer labels generate R_L over R_K
at lower total mass than iid single-coset b-seeds?

Pair: L = F(a, b), K = <a, c>, c = b a b^-2.  Free action: L acting on itself
by left multiplication (the Bernoulli orbit picture: iid labels on points).
We truncate to the ball B_N of the Cayley tree, put iid seeds of each label h
with density q_h, join w ~ a w, w ~ c w (K-moves) and w ~ h w for seeded w
(all pairs with both ends in B_N), and report

    D_M = fraction of w with |w| <= M such that w ~ b w,

which increases with N to P(w R' b w) for the infinite free action.  R' = R_L
iff that probability is 1.  Total mass = sum_h q_h.

Usage: python3 chord_threshold.py [N] [M] [reps]
"""
import sys
import numpy as np
from scipy.sparse import coo_matrix
from scipy.sparse.csgraph import connected_components

GEN = "aAbB"
INV = {"a": "A", "A": "a", "b": "B", "B": "b"}


def build_ball(N):
    """Nodes = reduced words of length <= N; returns first-letter, parent,
    child tables and length.  child[w, y] = node for y*w, or -1."""
    first = [-1]
    parent = [-1]
    length = [0]
    child = [[-1] * 4]
    layer = [0]
    for n in range(1, N + 1):
        nxt = []
        for w in layer:
            fw = first[w]
            for yi, y in enumerate(GEN):
                if fw >= 0 and GEN[fw] == INV[y]:
                    continue
                idx = len(first)
                first.append(yi)
                parent.append(w)
                length.append(n)
                child.append([-1] * 4)
                child[w][yi] = idx
                nxt.append(idx)
        layer = nxt
    return (np.array(first), np.array(parent), np.array(child),
            np.array(length))


class Ball:
    def __init__(self, N):
        self.first, self.parent, self.child, self.length = build_ball(N)
        self.n = len(self.first)
        self.lm = {}
        for yi, y in enumerate(GEN):
            inv = GEN.index(INV[y])
            res = self.child[:, yi].copy()
            back = self.first == inv
            res[back] = self.parent[back]
            self.lm[y] = res

    def act(self, word, nodes=None):
        """Return h * w for each node (h given as a word, applied right to
        left, as left multiplication), -1 if it leaves the ball."""
        cur = np.arange(self.n) if nodes is None else nodes.copy()
        for y in reversed(word):
            ok = cur >= 0
            nxt = np.full_like(cur, -1)
            nxt[ok] = self.lm[y][cur[ok]]
            cur = nxt
        return cur


def run(ball, labels, M, rng):
    """labels: list of (word, density).  Returns D_M."""
    rows, cols = [], []
    for kw in ("a", "baBB"):
        t = ball.act(kw)
        ok = t >= 0
        rows.append(np.nonzero(ok)[0])
        cols.append(t[ok])
    for word, q in labels:
        t = ball.act(word)
        seed = rng.random(ball.n) < q
        ok = (t >= 0) & seed
        rows.append(np.nonzero(ok)[0])
        cols.append(t[ok])
    r = np.concatenate(rows)
    c = np.concatenate(cols)
    g = coo_matrix((np.ones(len(r), dtype=np.int8), (r, c)),
                   shape=(ball.n, ball.n))
    _, comp = connected_components(g, directed=False)
    inner = np.nonzero(ball.length <= M)[0]
    bw = ball.act("b", inner)
    return float(np.mean(comp[inner] == comp[bw]))


SCHEMES = {
    # name: list of (label word, share of total mass)
    # <K, H> = L is checked in stallings_membership.py for every H below
    # except "bab" (<K, bab> != L, so it must give D = 0: a control).
    "b": [("b", 1.0)],
    "bab(ctrl)": [("bab", 1.0)],
    # b^2 = c^-1 b a lies in K b K: b-length 1 (coset_b_length.py)
    "bb": [("bb", 1.0)],
    "b+bb": [("b", 0.5), ("bb", 0.5)],
    # bab, bAb, baab, bAAb have b-length 2
    "b+bab": [("b", 0.5), ("bab", 0.5)],
    "len2mix": [("bab", 0.25), ("bAb", 0.25), ("baab", 0.25), ("bAAb", 0.25)],
    # babab has b-length 3
    "b+babab": [("b", 0.5), ("babab", 0.5)],
}


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 11
    M = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    reps = int(sys.argv[3]) if len(sys.argv) > 3 else 3
    rng = np.random.default_rng(20260918)
    ball = Ball(N)
    print(f"ball radius N={N}, nodes={ball.n}, inner radius M={M}, reps={reps}")
    masses = [0.05, 0.10, 0.14, 0.18, 0.22, 0.30, 0.40]
    for name, sch in SCHEMES.items():
        out = []
        for m in masses:
            labels = [(w, s * m) for w, s in sch]
            vals = [run(ball, labels, M, rng) for _ in range(reps)]
            out.append(f"{m:.2f}:{np.mean(vals):.3f}")
        print(f"{name:10s} " + " ".join(out), flush=True)


if __name__ == "__main__":
    main()
