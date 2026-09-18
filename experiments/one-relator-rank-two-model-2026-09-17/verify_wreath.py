"""Certificate: an explicit homomorphism pi : G_2 -> L wr Z (restricted wreath
product, L <= upper triangular GL_3(Z[1/2]), solvable) with
  pi(u) != 1, pi(b1) != 1, pi(v) not in pi(F_-) = <pi(a0), pi(a1)>,
where u = [a0,a1], b1 = [a0, a1 a0 a1^-1], v = a2 u a2^-1 (a square root of u).
Convention: x^s = s^-1 x s, [x,y] = x^-1 y^-1 x y, a_k = t^-k a t^k.
Wreath law: (g,s)(h,s') = (g * (s.h), s+s'), (s.h)(j) = h(j-s).  pi(t) = (1,1),
pi(a) = (f,0) with f(k) = M_k (k = 0,1,2) and 1 elsewhere, so pi(a_k)(j) = M_(j+k).
Exact rational arithmetic."""
from sympy import Matrix, diag, eye
M = {0: Matrix([[1,-1,-1],[0,1,-1],[0,0,1]]),
     1: Matrix([[1,0,0],[0,-1,1],[0,0,-1]]),
     2: diag(1,2,2)}
I = eye(3)
class W:
    def __init__(s, g, sh): s.g = {k: v for k, v in g.items() if v != I}; s.sh = sh
    def __mul__(s, o):
        g = dict(s.g)
        for j, v in o.g.items():
            jj = j + s.sh
            g[jj] = g.get(jj, I) * v
        return W(g, s.sh + o.sh)
    def inv(s):
        return W({j - s.sh: v.inv() for j, v in s.g.items()}, -s.sh)
    def is_id(s): return s.sh == 0 and not s.g
def word(wd, A, T):
    r = W({}, 0)
    for c in wd:
        r = r * {'a': A, 'A': A.inv(), 't': T, 'T': T.inv()}[c]
    return r
def inv(w): return ''.join(c.swapcase() for c in reversed(w))
def conj(x, s): return inv(s) + x + s
def comm(x, y): return inv(x) + inv(y) + x + y
A = W(dict(M), 0); T = W({}, 1)
a0, a1, a2 = 'a', conj('a', 't'), conj('a', 'tt')
u = comm(a0, a1); b1 = comm(a0, a1 + a0 + inv(a1)); v = a2 + u + inv(a2)
rel = inv(a2) + u + a2 + inv(u) + inv(u)
print("relator maps to identity:", word(rel, A, T).is_id())
pu, pb, pv = word(u, A, T), word(b1, A, T), word(v, A, T)
print("pi(u):", {j: m.tolist() for j, m in pu.g.items()})
print("pi(b1):", {j: m.tolist() for j, m in pb.g.items()})
print("pi(v):", {j: m.tolist() for j, m in pv.g.items()})
# pi(F_-) lies in the base; coordinate 0 of pi(F_-) is <M0,M1> <= GL_3(Z).
print("coordinate-0 generators of pi(F_-):", word(a0,A,T).g.get(0,I).tolist(), word(a1,A,T).g.get(0,I).tolist())
print("pi(v) at coordinate 0 is non-integral:", not all(x.is_integer for x in pv.g.get(0, I)))
print("pi(u) != 1:", not pu.is_id(), " pi(b1) != 1:", not pb.is_id())
