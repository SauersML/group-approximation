# Screen: does psi' (a,b -> +1; c,x,z -> -1) descend to the image of H_Q = <a,b,c,x,z> in PGL_2(F_p)?
# rho from radu-horizontal-tree-group-is-linear: x=diag(1,-1), z=[[0,1],[1,0]], a=[[0,m],[1,0]],
# y=[[s,-2m],[2,-s]], b=zaz, c=yby, with 2m^4-m^3+2m^2-m+2=0, s^2=-4(m^2+m+1), reduced at F_p-points.
import sys
from collections import deque

def canon(M, p):
    a, b, c, d = M
    for v in (a, b, c, d):
        if v % p:
            inv = pow(v, p - 2, p)
            return tuple((w * inv) % p for w in (a, b, c, d))
    raise ValueError("zero matrix")

def mm(A, B, p):
    a, b, c, d = A; e, f, g, h = B
    return canon(((a*e + b*g) % p, (a*f + b*h) % p, (c*e + d*g) % p, (c*f + d*h) % p), p)

def closure(gens, p):
    # gens: list of (matrix, sign); BFS on (g, sign)
    I = canon((1, 0, 0, 1), p)
    seen = {(I, 1)}
    dq = deque([(I, 1)])
    while dq:
        g, s = dq.popleft()
        for (h, t) in gens:
            k = (mm(g, h, p), s * t)
            if k not in seen:
                seen.add(k); dq.append(k)
    return seen

def run(p):
    out = []
    for m in range(1, p):
        if (2*m**4 - m**3 + 2*m**2 - m + 2) % p or (m + 1) % p == 0:
            continue
        for s in range(p):
            if (s*s + 4*(m*m + m + 1)) % p:
                continue
            x = canon((1, 0, 0, p - 1), p); z = canon((0, 1, 1, 0), p)
            a = canon((0, m, 1, 0), p); y = canon((s, (-2*m) % p, 2, (-s) % p), p)
            if (s*(-s) - (-2*m)*2) % p == 0:
                continue
            b = mm(mm(z, a, p), z, p); c = mm(mm(y, b, p), y, p)
            H = closure([(a, 1), (b, 1), (c, -1), (x, -1), (z, -1)], p)
            Hmats = {g for g, _ in H}
            descends = len(H) == len(Hmats)
            Q = closure([(a, 1), (x, 1), (y, 1), (z, 1)], p)
            out.append((p, m, s, len(Hmats), len(Q), descends, y in Hmats))
    return out

if __name__ == "__main__":
    for p in [int(t) for t in sys.argv[1:]]:
        for row in run(p):
            print("p=%d m=%d s=%d |H|=%d |Q|=%d psi_descends=%s y_in_H=%s" % row, flush=True)
    print("DONE")
