"""Corner rule for a same-word loop pair at a cone point A, and its check against real swaps.

nu = counterclockwise successor of corners around their vertex (corner ids 4x+j, j = BL, BR, TR, TL):
  nu(BL x) = BR(b^-1 x), nu(BR x) = TR(c^-1 x), nu(TR x) = TL(b x), nu(TL x) = BL(c x).
For paths P, Q from A to A, let a_P, a_Q be the start corners (4x+k of the first state) and
g_P, g_Q the end corners (4x+k+1 of the last state).  Rule: after the swap, the corners of A form the
cycles of (a_P a_Q) o nu o (g_P g_Q) restricted to A's corners (all other vertices keep their angles).
"""
import sys
from swap import Surf, apply_swap, excess, vertices
from h2 import onecyl, twocyl

def nu_map(b, c):
    from swap import inv
    bi, ci = inv(b), inv(c); d = len(b); nu = [0]*(4*d)
    for x in range(d):
        nu[4*x+0] = 4*bi[x]+1; nu[4*x+1] = 4*ci[x]+2
        nu[4*x+2] = 4*b[x]+3;  nu[4*x+3] = 4*c[x]+0
    return nu

def cycles_on(perm, dom):
    seen = set(); out = []
    for s in dom:
        if s in seen: continue
        cyc = []; x = s
        while x not in seen: seen.add(x); cyc.append(x); x = perm[x]
        out.append(frozenset(cyc))
    return set(out)

def predicted(nu, dom, aP, aQ, gP, gQ):
    t = {aP: aQ, aQ: aP}; u = {gP: gQ, gQ: gP}
    perm = {x: t.get(nu[u.get(x, x)], nu[u.get(x, x)]) for x in dom}
    return cycles_on(perm, dom)

def check(b, c, Lmax):
    S = Surf(b, c); nu = nu_map(b, c); A = S.cones()[0]; dom = S.cls[A]
    assert all(nu[x] in dom for x in dom)
    secs = [(i // 4, i % 4) for i in dom]; ok = bad = low = 0
    for k in range(4):
        sk = [s for s in secs if s[1] == k]
        for i in range(len(sk)):
            for j in range(len(sk)):
                if i == j: continue
                stack = [([sk[i]], [sk[j]])]
                while stack:
                    P, Q = stack.pop()
                    eP, eQ = S.vend(P[-1]), S.vend(Q[-1])
                    if eP == A and eQ == A:
                        verts = [S.vend(s) for s in P[:-1]] + [S.vend(s) for s in Q[:-1]]
                        if len(set(verts)) == len(verts) and A not in verts:
                            r = apply_swap(S, P, Q)
                            if r is not None:
                                lab, cls = vertices(*r)
                                real = set(frozenset(x for x in cl) for cl in cls.values() if cl[0] in dom or any(y in dom for y in cl))
                                real = set(frozenset(y for y in cl if y in dom) for cl in real)
                                pred = predicted(nu, dom, 4*P[0][0]+P[0][1], 4*Q[0][0]+Q[0][1],
                                                 4*P[-1][0]+(P[-1][1]+1)%4, 4*Q[-1][0]+(Q[-1][1]+1)%4)
                                if real == pred: ok += 1
                                else: bad += 1
                                if excess(*r) < excess(b, c): low += 1
                    if len(P) < Lmax and eP != A and eQ != A:
                        for mv in (0, 1, 2):
                            stack.append((P + [S.step(P[-1], mv)], Q + [S.step(Q[-1], mv)]))
    return ok, bad, low

if __name__ == '__main__':
    Lmax = int(sys.argv[1])
    for name, bc in [('one123H8', onecyl(1, 2, 3, 8, 1)), ('one114H5', onecyl(1, 1, 4, 5, 0)),
                     ('one235H4', onecyl(2, 3, 5, 4, 2)), ('two', twocyl(4, 2, 1, 2, 3, 1)),
                     ('two2', twocyl(5, 1, 0, 3, 2, 2))]:
        print(name, check(*bc, Lmax), flush=True)
