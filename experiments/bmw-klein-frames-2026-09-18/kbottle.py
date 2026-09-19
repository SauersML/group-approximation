# Flat Klein bottles: all pure inverting pairs (A, B) with |A| = p fixed and |B| UNBOUNDED.
# A is a reduced word of family F (h or v), B a reduced nonempty word of the other family, both of even
# length, and A B A^-1 = B^-1.  Pushing B through A letter by letter gives a p x q grid of squares whose
# top and bottom rows are A and whose sides are B and B^-1: a flat Klein bottle in the square complex.
# Meet in the middle: track (S, T) = (section of A after the first i letters of B, section of A before
# the last i letters), plus the last letters used on each side (for free reduction of B).
# Step: choose x = b_i;  S x = x' S';  choose y' = x^-1 and solve T' y = y' T for (T', y);  need x' = y^-1.
# A pair exists with |B| = 2k iff some diagonal (A, A) reaches a diagonal (S, S) in k steps with the
# junction x_k y_{k+1} reduced.  BFS from all diagonals at once is complete for the given p.
# usage: kbottle.py census.json class P [--swap] [--cap N]   (P: max even |A|; --swap: A a v-word)
import sys, json
from collections import deque
D = json.load(open(sys.argv[1])); ci = int(sys.argv[2]); P = int(sys.argv[3])
SWAP = '--swap' in sys.argv
CAP = int(sys.argv[sys.argv.index('--cap') + 1]) if '--cap' in sys.argv else 3 * 10 ** 6
m, n, iA, iB = D['m'], D['n'], D['iA'], D['iB']
SQ = {tuple(a): tuple(b) for a, b in D['reps'][ci]}          # h v = v' h'
if SWAP:                                                      # v h = h' v':  (v, h) -> (h', v')
    T2 = {}
    for (h, v), (v2, h2) in SQ.items(): T2[(iB[v2], h)] = (h2, iB[v])
    SQ = T2; m, n, iA, iB = n, m, iB, iA
# now "A-letters" are 0..m-1 (inverse iA), "B-letters" 0..n-1 (inverse iB); SQ[(a, b)] = (b', a'): a b = b' a'
INV = {v: k for k, v in SQ.items()}                           # (b', a') -> (a, b)
def push(S, x):                                               # S x = x' S'
    S = list(S)
    for i in range(len(S) - 1, -1, -1):
        x, S[i] = SQ[(S[i], x)]
    return x, tuple(S)
def back(T, y2):                                              # T' y = y2 T  ->  (T', y)
    Tp = []; z = y2
    for t in T:
        a, z = INV[(z, t)]; Tp.append(a)
    return tuple(Tp), z
def words(p):
    o = [()]
    for _ in range(p): o = [w + (c,) for w in o for c in range(m) if not w or w[-1] != iA[c]]
    return o
def red(w, inv): return all(w[i + 1] != inv[w[i]] for i in range(len(w) - 1))
res = []
for p in range(2, P + 1, 2):
    par = {}; dq = deque(); found = []
    for A in words(p):
        s = (A, A, -1, -1); par[s] = None; dq.append(s)
    over = False
    while dq:
        s = dq.popleft(); S, T, lx, ly = s
        for x in range(n):
            if lx >= 0 and x == iB[lx]: continue
            x2, S2 = push(S, x)
            T2_, y = back(T, iB[x])
            if x2 != iB[y] or (ly >= 0 and y == iB[ly]): continue
            t = (S2, T2_, x, y)
            if S2 == T2_ and x != iB[y]:
                # reconstruct
                fr = [x]; bk = [y]; u = s
                while par[u] is not None:
                    fr.append(u[2]); bk.append(u[3]); u = par[u]
                A = u[0]; B = tuple(reversed(fr)) + tuple(bk)
                found.append((A, B))
            if t not in par:
                par[t] = s; dq.append(t)
                if len(par) > CAP: over = True; break
        if over or len(found) >= 5: break
    rec = {'class': ci, 'swap': SWAP, 'p': p, 'states': len(par), 'complete': not over and not found or bool(found),
           'capped': over, 'pairs': [[''.join(map(str, A)), ''.join(map(str, B))] for A, B in found[:5]]}
    print(json.dumps(rec), flush=True)
    del par, dq
