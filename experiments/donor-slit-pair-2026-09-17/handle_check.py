"""Check the handle lemma's sign condition against simulation on all short loop pairs of test surfaces."""
import random
from swap import Surf, excess, tori, perturb_local, excised
from stalls_lib import components, restrict
from handle import loops, try_handle, path
from blocks import excise_block
def N(S, j, x): return [S.ci, S.b, S.c, S.bi][j][x]
def rot(S, st): x, k = st; return (N(S, (k - 1) % 4, x), (k + 1) % 4)
def rev(S, st): x, k = st; return (N(S, k, x), (k + 2) % 4)
def ccw_order(S, st0):
    order = [st0]; st = rot(S, st0)
    while st != st0: order.append(st); st = rot(S, st)
    return order
def classify(S, al, be):
    (A, sa, wa, u, _), (_, sb, wb, w, _) = al, be
    Pa, Pb = path(S, sa, wa), path(S, sb, wb)
    order = ccw_order(S, sa); pos = {st: i for i, st in enumerate(order)}
    ao, ai, bo, bi = 0, pos[rev(S, Pa[-1])], pos[sb], pos[rev(S, Pb[-1])]
    inL = lambda p: 0 < p < ai
    if inL(bo) == inL(bi): return 'nocross'
    det = u[0]*w[1] - u[1]*w[0]
    return 'H1' if inL(bo) == (det < 0) else 'anti-H1'   # H1: beta leaves alpha to the right iff det(u, w) > 0
from handle import DIRS, OFF, lattice_torus
def pts(st, word):
    x, k = st; p = OFF[k]; out = [p]
    cur = k
    for mv in (None,) + tuple(word):
        if mv == 1: cur = (cur + 1) % 4
        elif mv == 2: cur = (cur - 1) % 4
        dx, dy = DIRS[cur]; p = (p[0] + dx, p[1] + dy); out.append(p)
    return out
def donor_simple(al, be):
    u, w = al[3], be[3]; _, _, idx = lattice_torus(u, w)
    qa = pts(al[1], al[2]); qb = pts(be[1], be[2])
    qa = [(p[0]-qa[0][0], p[1]-qa[0][1]) for p in qa]; qb = [(p[0]-qb[0][0], p[1]-qb[0][1]) for p in qb]
    ia = [idx(*p) for p in qa[:-1]]; ib = [idx(*p) for p in qb[:-1]]
    return len(set(ia)) == len(ia) and len(set(ib)) == len(ib) and set(ia) & set(ib) == {idx(0, 0)}
def run(b, c, L, tally):
    S = Surf(b, c); lp = loops(S, L)
    for al in lp:
        for be in lp:
            if al[0] != be[0] or al is be: continue
            u, w = al[3], be[3]
            if u[0]*w[1] - u[1]*w[0] == 0 or set(al[4]) & set(be[4]): continue
            # loops must meet only at A: no common vertex other than A
            Va = {S.vend(p) for p in path(S, al[1], al[2])}; Vb = {S.vend(p) for p in path(S, be[1], be[2])}
            if Va & Vb != {al[0]}: continue
            Pa, Pb = path(S, al[1], al[2]), path(S, be[1], be[2])
            if len(Va) != len(Pa) or len(Vb) != len(Pb): continue   # simple loops in S
            if not donor_simple(al, be): continue
            cl = classify(S, al, be); r = try_handle(b, c, al, be)
            ok = r is not None and r[1] == r[0] and r[2] == r[0] - 2
            neutral = r is not None and r[1] == r[0]
            tally[(cl, "lowers" if ok else "no-drop", "1st-neutral" if neutral else "1st-not-neutral")] = tally.get((cl, "lowers" if ok else "no-drop", "1st-neutral" if neutral else "1st-not-neutral"), 0) + 1
tally = {}
for n in (4, 5): _, _, b, c = excised(n); cm = max(components(b, c), key=len); run(*restrict(b, c, cm), 5, tally)
for (n, k, l) in [(8, 2, 2), (8, 2, 3), (9, 3, 3)]:
    b, c = excise_block(n, k, l); cm = max(components(b, c), key=len); run(*restrict(b, c, cm), 5, tally)
rng = random.Random(3)
for t in range(40):
    b0, c0 = tori([(rng.randrange(4, 8), rng.randrange(4, 8))]); b, c = perturb_local(b0, c0, rng.randrange(1, 4), rng, 3)
    for cm in components(b, c):
        B, C = restrict(b, c, cm)
        if excess(B, C): run(B, C, 5, tally)
for k, v in sorted(tally.items()): print(k, v)
