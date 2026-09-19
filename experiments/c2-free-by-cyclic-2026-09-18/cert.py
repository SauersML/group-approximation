# Finite certificate that rank V_{M+1} = rank V_M + 2 for all M >= M0, where
#   V_M = < phi^3 C, phi^3 E, phi^4 E, phi^j A (0<=j<=M), phi^j B (-1<=j<=M) >  (image of a basis subset of K_C)
#   V_{M+1} = < phi(V_M), A, phi^-1 B >.
# Work in train-track coordinates: Gamma_M = Stallings graph of theta(V_M), and theta phi = psi theta, psi a rose train track.
import sys
from collections import deque
from tt2 import TH, PSI, L, inv, red, apply, A, B, Cc, E, pw
from fold2 import SG
D = {}
for c in L: D[c] = PSI[c][0]; D[c.upper()] = inv(PSI[c])[0]
def orb(x):
    o = [x]
    for _ in range(20): x = D[x]; o.append(x)
    return o
O = {x: orb(x) for x in D}
def illegal(x, y): return x != y and any(O[x][k] == O[y][k] for k in range(21))
def psiw(c): return PSI[c] if c.islower() else inv(PSI[c.lower()])
# train-track check: every turn inside an edge image is legal
for c in L:
    w = PSI[c]
    for i in range(len(w) - 1): assert not illegal(w[i].swapcase(), w[i + 1]), ('not a train track', c)
def Vgens(M): return [pw(Cc, 3), pw(E, 3), pw(E, 4)] + [pw(A, j) for j in range(M + 1)] + [pw(B, j) for j in range(-1, M + 1)]
NEW = [apply(TH, A), apply(TH, pw(B, -1))]   # theta of the two generators added at each step
def dist(G, base):
    d = {base: 0}; Qu = deque([base])
    while Qu:
        v = Qu.popleft()
        for lab, t in G.out[v].items():
            t = G.f(t)
            if t not in d: d[t] = d[v] + 1; Qu.append(t)
    return d
def datum(G, base, R, extra=None):
    # ball of radius R: vertices within R, inside edges, and labels of edges leaving the ball.
    # extra[v] = additional outgoing labels at v that leave the ball (outside edges not stored in G)
    extra = extra or {}
    d = dist(G, base); order = [base]; idx = {base: 0}
    for v in order:
        for lab in sorted(G.out[v]):
            t = G.f(G.out[v][lab])
            if d[t] <= R and t not in idx: idx[t] = len(order); order.append(t)
    rows = []
    for v in order:
        row = []
        for lab in sorted(list(G.out[v]) + extra.get(v, [])):
            t = G.f(G.out[v][lab]) if lab in G.out[v] else None
            row.append((lab, idx[t] if t is not None and t in idx else -1))
        rows.append(tuple(row))
    return tuple(rows)
def legal_vertex(labs): return not any(illegal(x, y) for i, x in enumerate(labs) for y in labs[i + 1:])
def step(dat, R, new=NEW):
    # returns (ok, message, newdatum, rankdrop)
    Z = SG(); n = len(dat)
    for _ in range(n - 1): Z.new()
    nV, nE = n, 0
    for v, row in enumerate(dat):
        for lab, t in row:
            if t < 0 or not lab.islower(): continue   # each inside edge once, from its lower-case end
            w = psiw(lab); cur = v
            for k, c in enumerate(w):
                nxt = t if k == len(w) - 1 else Z.new()
                Z.edge(cur, c, nxt); cur = nxt
            nE += 1
    rankZ = nE - nV + 1 + len(new)
    for u in new: Z.add_loop(u, 0)
    V2, E2, rankZ2 = Z.stats()
    outs = {}
    for v, row in enumerate(dat):
        for lab, t in row:
            if t < 0: outs.setdefault(Z.f(v), []).append(D[lab])
    for w, labs in outs.items():
        allf = list(Z.out[w]) + labs
        if len(set(allf)) != len(allf): return False, 'outside edge clashes at a boundary image', None, None
    d = dist(Z, Z.f(0)); dprime = min(d[w] for w in outs)
    if dprime < R: return False, 'boundary image at distance %d < R' % dprime, None, None
    for w in Z.verts():
        if d[w] > R and not legal_vertex(list(Z.out[w]) + outs.get(w, [])):
            return False, 'illegal vertex beyond R', None, None
    return True, 'ok (dprime=%d)' % dprime, datum(Z, Z.f(0), R, outs), rankZ - rankZ2
def canon_ok(G, base, R):
    d = dist(G, base)
    return all(legal_vertex(list(G.out[v])) for v in G.verts() if d[v] > R)
if __name__ == '__main__':
    R = int(sys.argv[1]); M0 = int(sys.argv[2])
    for M in range(M0 + 1):
        G = SG()
        for u in Vgens(M): G.add_loop(apply(TH, u))
        V, Ed, rk = G.stats(); b = G.f(0)
        dt = datum(G, b, R)
        ok, msg, nd, drop = step(dt, R)
        print('M', M, 'V', V, 'rank', rk, 'want', 2 * M + 6, 'legal beyond R', canon_ok(G, b, R), 'ball size', len(dt),
              'step', msg, 'rank drop', drop, 'fixed point' if nd == dt else 'moves', flush=True)
        if M: print('   step prediction matches actual datum:', prev_nd == dt)
        prev_nd = nd
