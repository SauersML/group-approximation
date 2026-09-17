"""Check the derived-length-3 example in solvable-by-metabelian-edge-images-collapse-higman-quotients.
H = Z^(Z) x Z with (v,s)(v',s') = (v+v', s+s'+beta(v,v')), beta(e_i,e_j) = 1 iff j = i+1.
t shifts e_i -> e_{i+1} and preserves beta. G = H x| <t> = <x_0, t>.
We check [x_i, x_{i+1}] = c^(+-1) and [x_0^-1 x_1, x_1^-1 x_2] = c^(+-2) (so G'' != 1)."""
from collections import defaultdict
def beta(v, w):
    return sum(v.get(i, 0) * w.get(i + 1, 0) for i in list(v))
def mul(p, q):
    v = defaultdict(int, p[0])
    for i, x in q[0].items(): v[i] += x
    return ({i: x for i, x in v.items() if x}, p[1] + q[1] + beta(p[0], q[0]))
def inv(p):
    v = {i: -x for i, x in p[0].items()}
    return (v, -p[1] + beta(p[0], p[0]))  # (v,s)(-v,s') = (0, s+s'-beta(v,v))
def comm(p, q):
    r = mul(inv(p), inv(q)); r = mul(r, p); return mul(r, q)
x = lambda i: ({i: 1}, 0)
for i in range(-2, 3):
    assert mul(x(i), inv(x(i))) == ({}, 0)
    print("[x_%d,x_%d] =" % (i, i + 1), comm(x(i), x(i + 1)))
u1 = mul(inv(x(0)), x(1)); u2 = mul(inv(x(1)), x(2))
print("[x_0^-1 x_1, x_1^-1 x_2] =", comm(u1, u2))
