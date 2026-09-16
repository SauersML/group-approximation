# Which line directions i*zeta^j R (j=0..4) of ChJN's family L are rational for Lat=<w1,w2>?
import sympy as sp
z = sp.symbols('z')
cyc = sp.Poly(z**4+z**3+z**2+z+1, z)
def vec(expr):
    p = sp.Poly(sp.expand(expr), z).rem(cyc)
    c = p.all_coeffs()[::-1]
    c = c + [0]*(4-len(c))
    return [sp.Rational(x) for x in c]
w1 = z**2 - z**3
w2 = 5*(1 - z**2 - z**3 + z**4)
u = z - z**4           # 2 i sin(72 deg), purely imaginary
r5 = 1 + 2*(z + z**4)  # sqrt(5)
# check sqrt5^2 = 5
assert vec(r5*r5) == vec(5)
for j in range(5):
    a = z**j*u
    b = z**j*u*r5
    M = sp.Matrix([vec(w1), vec(w2), vec(a), vec(b)]).T
    rk = M.rank()
    print("direction i*zeta^%d: dim(Lat_Q  cap  line_Q) = %d" % (j, 4-rk))
    if rk < 4:
        ns = M.nullspace()
        for n in ns:
            print("   relation (coeffs of w1,w2,a,b):", list(n))
# numeric sanity
import cmath
zz = cmath.exp(2j*cmath.pi/5)
print("w1 =", zz**2-zz**3, " w2 =", 5*(1-zz**2-zz**3+zz**4))
for j in range(5):
    d = 1j*zz**j
    print(j, "angle(deg) of i zeta^j:", round(cmath.phase(d)*180/cmath.pi,3))
print("angle w2:", cmath.phase(5*(1-zz**2-zz**3+zz**4))*180/cmath.pi)
