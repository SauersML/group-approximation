"""Handle excision with a lattice donor.  alpha, beta: edge loops at a cone point A (edge paths A -> A that do
not revisit A), holonomies u, w with det(u, w) != 0, edge-disjoint.  Donor: Z^2 / <u, w>.  Swap alpha with the
donor copy alpha' (same start side, same word), then beta with beta'.  Lemma: if beta crosses alpha at A with
the sign of det(u, w), the first swap is neutral and the second lowers the excess by 2."""
from swap import Surf, apply_swap, excess
from math import gcd
DIRS = [(1, 0), (0, 1), (-1, 0), (0, -1)]
OFF = [(0, 0), (1, 0), (1, 1), (0, 1)]          # corner k of square (0,0): start of side k          # side k of a square is traversed in direction DIRS[k]
def path(S, st, word):
    P = [st]
    for mv in word: P.append(S.step(P[-1], mv))
    return P
def lattice_torus(u, w):
    """Z^2/<u,w> as a permutation pair; returns b, c and index of point (x, y)."""
    det = u[0]*w[1] - u[1]*w[0]; assert det != 0
    # HNF: lattice contains (a, 0) and (t, h) with h = gcd(u1, w1)
    h = gcd(u[1], w[1]); a = abs(det)//h
    # find integer combination giving second coordinate h
    def eg(p, q):
        if q == 0: return (1 if p >= 0 else -1, 0)
        x, y = eg(q, p % q); return (y, x - (p//q)*y)
    x1, y1 = eg(u[1], w[1]); t = (x1*u[0] + y1*w[0]); assert x1*u[1] + y1*w[1] in (h, -h)
    if x1*u[1] + y1*w[1] == -h: t = -t
    def idx(x, y):
        k = y // h; x -= k*t; y -= k*h
        return (x % a) + a*y
    n = a*h; b = [0]*n; c = [0]*n
    for y in range(h):
        for x in range(a):
            b[idx(x, y)] = idx(x+1, y); c[idx(x, y)] = idx(x, y+1)
    return b, c, idx
def loops(S, L):
    """All edge loops of length <= L at cone points: (A, start state, word, holonomy, sites)."""
    out = []; cones = set(S.cones())
    for x in range(len(S.b)):
        for k in range(4):
            st = (x, k); A = S.vstart(st)
            if A not in cones: continue
            stack = [((), st, (0, 0))]
            while stack:
                word, cur, pos = stack.pop()
                dx, dy = DIRS[cur[1]]; npos = (pos[0]+dx, pos[1]+dy)
                v = S.vend(cur)
                if v == A:
                    P = path(S, st, word); sites = [S.site(p) for p in P]
                    if len(set(sites)) == len(sites): out.append((A, st, word, npos, sites))
                    continue
                if len(word) + 1 >= L: continue
                for mv in range(3): stack.append((word + (mv,), S.step(cur, mv), npos))
    return out
def try_handle(b, c, al, be):
    """Apply the two swaps; return (excess0, excess after 1st, excess after 2nd) or None."""
    (A, sa, wa, u, _), (_, sb, wb, w, _) = al, be
    Tb, Tc, idx = lattice_torus(u, w); d = len(b)
    B = b + [d + y for y in Tb]; C = c + [d + y for y in Tc]
    S = Surf(B, C); e0 = excess(B, C)
    Pa = path(S, sa, wa); Pa2 = path(S, (d + idx(-OFF[sa[1]][0], -OFF[sa[1]][1]), sa[1]), wa)
    r = apply_swap(S, Pa, Pa2)
    if r is None: return None
    S1 = Surf(*r); e1 = excess(*r)
    Pb = path(S1, sb, wb); Pb2 = path(S1, (d + idx(-OFF[sb[1]][0], -OFF[sb[1]][1]), sb[1]), wb)
    r2 = apply_swap(S1, Pb, Pb2)
    if r2 is None: return None
    return e0, e1, excess(*r2)
def best_handle(b, c, L):
    S = Surf(b, c); lp = loops(S, L); best = None
    for i, al in enumerate(lp):
        for be in lp:
            if be[0] != al[0]: continue
            u, w = al[3], be[3]
            if u[0]*w[1] - u[1]*w[0] == 0 or set(al[4]) & set(be[4]): continue
            tot = len(al[2]) + len(be[2]) + 2
            if best is not None and tot >= best[0]: continue
            r = try_handle(b, c, al, be)
            if r and r[1] <= r[0] and r[2] < r[0]: best = (tot, u, w, r)
    return best
if __name__ == '__main__':
    import json
    from stalls_lib import components, restrict
    from swap import excised
    for n in (4, 5, 6, 7):
        _, _, b, c = excised(n); cm = max(components(b, c), key=len); B, C = restrict(b, c, cm)
        print('excised', n, best_handle(B, C, 3))
    for s in json.load(open('stalls.json')):
        for cm in components(s['bs'], s['cs']):
            B, C = restrict(s['bs'], s['cs'], cm)
            if excess(B, C): print(s['trial'], len(B), best_handle(B, C, 5), flush=True)
