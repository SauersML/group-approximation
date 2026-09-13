# 2-adic check of the PGL_2 representation of Radu's BMW lattice.
# m: root of 2m^4 - m^3 + 2m^2 - m + 2 with v_2(m) = 1; s^2 = -4(m^2+m+1).
# Checks: x,y,z in PGL_2(Z_2) (after scaling), a,b,c send v_0 to the three distinct neighbours,
# and the orders of <x,y,z> acting on the ball of radius n (image in PGL_2(Z/2^n)).
PREC = 60
MOD = 1 << PREC

def f(t):
    return (2 * t**4 - t**3 + 2 * t**2 - t + 2)

def hensel_root():
    # m = 2u, 16u^4 - 4u^3 + 4u^2 - u + 1 = 0, simple root mod 2 (derivative -1 odd)
    g = lambda u: 16 * u**4 - 4 * u**3 + 4 * u**2 - u + 1
    u = 1
    for k in range(1, PREC + 4):
        m2 = 1 << (k + 1)
        if g(u) % m2 != 0:
            u += 1 << k
    assert g(u) % (1 << PREC) == 0
    return 2 * u

m = hensel_root() % MOD
assert f(m) % (1 << (PREC - 2)) == 0
print("m mod 64 =", m % 64, "v_2(m) = 1:", m % 2 == 0 and m % 4 != 0)
d = (-(m * m + m + 1)) % MOD  # s = 2*sqrt(d)
print("-(m^2+m+1) mod 8 =", d % 8)

def sqrt2adic(dv):
    assert dv % 8 == 1
    r = 1
    for k in range(3, PREC):
        if (r * r - dv) % (1 << (k + 1)) != 0:
            r += 1 << (k - 1)
    assert (r * r - dv) % (1 << (PREC - 2)) == 0
    return r

h = sqrt2adic(d)  # s/2
print("s/2 mod 16 =", h % 16)
# integral normalized matrices (entries mod 2^PREC), PGL_2 elements
x = (1, 0, 0, MOD - 1)
z = (0, 1, 1, 0)
y = (h, (-m) % MOD, 1, (-h) % MOD)   # y/2
a = (0, m, 1, 0)

def mm(A, B, mod):
    return ((A[0]*B[0] + A[1]*B[2]) % mod, (A[0]*B[1] + A[1]*B[3]) % mod,
            (A[2]*B[0] + A[3]*B[2]) % mod, (A[2]*B[1] + A[3]*B[3]) % mod)

def det(A, mod):
    return (A[0]*A[3] - A[1]*A[2]) % mod

print("det y/2 odd:", det(y, MOD) % 2 == 1, " det x, det z odd:", det(x, 8) % 2, det(z, 8) % 2)
print("det a has v_2 = 1:", det(a, MOD) % 2 == 0 and det(a, MOD) % 4 != 0)
b = mm(mm(z, a, MOD), z, MOD)
c = mm(mm(y, b, MOD), y, MOD)

def neighbour(A):
    # A maps O^2 to a lattice; for det of valuation 1 with integral entries, the image lattice
    # contains 2O^2 with index 2 and equals span(col1, col2) + 2O^2; its reduction is a line in F_2^2.
    cols = [(A[0] % 2, A[2] % 2), (A[1] % 2, A[3] % 2)]
    nz = [cv for cv in cols if cv != (0, 0)]
    return nz[0] if nz else None

print("neighbours of v_0 via a,b,c:", neighbour(a), neighbour(b), neighbour(c))
print("det b, det c valuation 1:", [det(M, 4) % 4 == 2 for M in (b, c)])

def pgl_key(A, n):
    mod = 1 << n
    A = tuple(v % mod for v in A)
    # normalise by a unit scalar: make the first odd entry equal to 1
    for v in A:
        if v % 2 == 1:
            inv = pow(v, -1, mod)
            return tuple((w * inv) % mod for w in A)
    return None

def group_order(gens, n):
    mod = 1 << n
    e = pgl_key((1, 0, 0, 1), n)
    seen = {e}
    frontier = [e]
    gk = [pgl_key(g, n) for g in gens]
    while frontier:
        new = []
        for A in frontier:
            for G in gk:
                B = pgl_key(mm(A, G, mod), n)
                if B not in seen:
                    seen.add(B)
                    new.append(B)
        frontier = new
    return len(seen)

for n in range(1, 7):
    print("level", n, "order of <x,y,z> in PGL_2(Z/2^n):", group_order([x, y, z], n))
print("DONE")
