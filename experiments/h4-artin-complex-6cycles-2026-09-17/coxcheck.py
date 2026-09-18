"""Finite core: bottom-triple (upward flag) condition in the Coxeter complex C_W, which embeds in the
Artin complex as the positive apartment {lift(w) A_T} and is a simplicial retract of it via the
projection pi: Delta -> C (quotient by the pure Artin group).  Hence a triple of type-s1hat vertices in C
that is pairwise upper bounded but has no common upper bound in C is a counterexample in Delta."""
import sys, itertools
from search import DIAGRAMS
from garside import Coxeter

def min_rep(W, w, mask):
    while True:
        c = W.rd[w] & mask
        if not c:
            return w
        i = (c & -c).bit_length() - 1
        w = W.rmul[w][i]

def check(name):
    n, md = DIAGRAMS[name]
    W = Coxeter(n, md)
    full = (1 << n) - 1
    X = full & ~1; Y = full & ~(1 << (n - 1))
    WX = [w for w in range(W.N) if W.supp[w] & ~X == 0]
    WY = [w for w in range(W.N) if W.supp[w] & ~Y == 0]
    XY = set(W.mul(x, y) for x in WX for y in WY)
    xs = sorted(set(min_rep(W, w, X) for w in range(W.N)))
    ys = sorted(set(min_rep(W, w, Y) for w in range(W.N)))
    nbr = {}
    for x in xs:
        xi = W.inv[x]
        nbr[x] = frozenset(y for y in ys if W.mul(xi, y) in XY)
    bad = 0; tri = 0; examples = []
    for a, b, c in itertools.combinations(xs, 3):
        if nbr[a] & nbr[b] and nbr[a] & nbr[c] and nbr[b] & nbr[c]:
            tri += 1
            if not (nbr[a] & nbr[b] & nbr[c]):
                bad += 1
                if len(examples) < 3:
                    examples.append((W.word[a], W.word[b], W.word[c]))
    print(f"[{name}] |W|={W.N} #s1hat={len(xs)} #snhat={len(ys)} deg={len(nbr[0])} pairwise-bounded triples={tri} without common upper bound={bad} ex={examples}", flush=True)

for g in sys.argv[1:]:
    check(g)
