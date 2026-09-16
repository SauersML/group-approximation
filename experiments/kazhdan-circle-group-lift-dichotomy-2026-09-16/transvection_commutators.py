"""Exact check: in Aut(F_3), do the right transvections rho_12, rho_23 generate a
Heisenberg-type configuration (commutator central in the pair)?

rho_ij : x_i -> x_i x_j, other generators fixed.  Automorphisms are dicts
generator -> reduced word (tuple of nonzero ints, -k = x_k^{-1}).  Composition is
(phi * psi)(w) = phi(psi(w)).  Commutator [a, b] = a b a^-1 b^-1.
This is evidence for the note only (why Witte Morris's nilpotent mechanism has no
direct analogue on these elements); it proves nothing about orderability.
"""
N = 3

def red(w):
    out = []
    for a in w:
        if out and out[-1] == -a:
            out.pop()
        else:
            out.append(a)
    return tuple(out)

def inv_word(w):
    return tuple(-a for a in reversed(w))

def apply(phi, w):
    res = []
    for a in w:
        img = phi[abs(a)]
        res.extend(img if a > 0 else inv_word(img))
    return red(res)

def comp(phi, psi):  # phi after psi
    return {k: apply(phi, psi[k]) for k in range(1, N + 1)}

def ident():
    return {k: (k,) for k in range(1, N + 1)}

def rho(i, j, e=1):
    d = ident()
    d[i] = (i, j) if e == 1 else (i, -j)
    return d

def inverse(phi, cands):
    for c in cands:
        if comp(phi, c) == ident() and comp(c, phi) == ident():
            return c
    raise ValueError("inverse not in candidate list")

def comm(a, ainv, b, binv):
    return comp(comp(comp(a, b), ainv), binv)

r12, r12i = rho(1, 2), rho(1, 2, -1)
r23, r23i = rho(2, 3), rho(2, 3, -1)
r13, r13i = rho(1, 3), rho(1, 3, -1)
assert comp(r12, r12i) == ident() and comp(r23, r23i) == ident()

c = comm(r12, r12i, r23, r23i)
print("[rho12, rho23] =", c)
print("equals rho13 ?", c == r13, "; equals rho13^-1 ?", c == r13i)
print("rho13 commutes with rho12 ?", comp(r13, r12) == comp(r12, r13))
print("rho13 commutes with rho23 ?", comp(r13, r23) == comp(r23, r13))
print("c commutes with rho12 ?", comp(c, r12) == comp(r12, c))
print("c commutes with rho23 ?", comp(c, r23) == comp(r23, c))
print("rho13(rho12(x1)) =", apply(r13, apply(r12, (1,))), " rho12(rho13(x1)) =", apply(r12, apply(r13, (1,))))
