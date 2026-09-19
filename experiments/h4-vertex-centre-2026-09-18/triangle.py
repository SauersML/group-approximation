"""Vertex-free Case 1 tuples from transporter triangles.

With F_0 = F, F_1 = b1 F b1^-1, F_2 = b3^-1 F b3 (b1, b3 in P_X), pick
  q in F_0 & F_1 \\ F_2,  p in F_0 & F_2 \\ F_1,  r = b1 f b1^-1 in F_1 & F_2 \\ F_0.
Then  alpha_1 = p q,  alpha_2 = (b1^-1 q^-1 b1) f  lie in F and (alpha_1, b1, alpha_2, b3) solves
  (*)  b3^-1 (alpha_1 alpha_2) b3 = alpha_1 b1 alpha_2 b1^-1,
with c_01 = q^-1 r, c_12 = b1^-1 p q b1, c_20 = b3 p q b3^-1 all outside F: no hexagon vertex is a pure centre.
Every candidate is re-verified from scratch: (*) and genuineness by Garside normal forms, the three c_P by the
exact test fmem.in_F.
Run: python3 triangle.py LG LF [maxhits]"""
import sys
from fmem import in_F, inv, nf, G
from gens4 import FG, NG, ZG, words

LG = int(sys.argv[1]); LF = int(sys.argv[2]); MAXH = int(sys.argv[3]) if len(sys.argv) > 3 else 20
XG = dict(NG); XG.update(ZG)
FW = words(FG, LF)
GW = words(XG, LG)


def T(g):
    return [(fs, f) for fs, f in FW if in_F(g + f + inv(g))]


def verify(a1, b1, a2, b3):
    lhs = nf(inv(b3) + a1 + a2 + b3); rhs = nf(a1 + b1 + a2 + inv(b1))
    if lhs != rhs or nf(a1 + a2) == G.one or nf(b1 + b3) == G.one:
        return None
    c = {'01': b1 + a2 + inv(b1), '12': inv(b1) + a1 + b1, '20': b3 + a1 + inv(b3)}
    return {P: in_F(w) for P, w in c.items()}


TT = {}
for s, g in GW:
    t = T(g)
    if t:
        TT[s] = (g, t)
print('conjugators with nontrivial transporter:', len(TT), flush=True)
hits = 0
for s1, (g1i, Tq) in TT.items():          # g1i = b1^-1
    b1 = inv(g1i)
    for s3, (b3, Tp) in TT.items():
        Q = [(qs, q) for qs, q in Tq if not in_F(b3 + q + inv(b3))]
        if not Q:
            continue
        Pp = [(ps, p) for ps, p in Tp if not in_F(g1i + p + b1)]
        if not Pp:
            continue
        Tf = [(fs, f) for fs, f in T(b3 + b1) if not in_F(b1 + f + g1i)]
        if not Tf:
            continue
        qs, q = Q[0]; ps, p = Pp[0]; fs, f = Tf[0]
        a1 = p + q; a2 = g1i + inv(q) + b1 + f
        v = verify(a1, b1, a2, b3)
        print('HIT b1^-1=[%s] b3=[%s] q=[%s] p=[%s] f=[%s] verify=%s' % (s1, s3, qs, ps, fs, v), flush=True)
        hits += 1
        if hits >= MAXH:
            sys.exit(0)
print('done, hits', hits)
