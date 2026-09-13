# Exact check that x,y,z,a in PGL_2(K), K = Q(m,s), 2m^4-m^3+2m^2-m+2=0, s^2=-4(m^2+m+1),
# satisfy the square relations of Radu's BMW lattice, plus (xz)^2 and (xyz)^3.
from fractions import Fraction as Fr
import cmath

def norm(d):
    return {k: v for k, v in d.items() if v != 0}

def mul(p, q):
    r = {}
    for (i, j), u in p.items():
        for (k, l), w in q.items():
            e, f, c = i + k, j + l, u * w
            terms = {(e, f): c}
            out = {}
            # reduce s^2 = -4(m^2+m+1)
            while terms:
                (e1, f1), c1 = terms.popitem()
                if f1 >= 2:
                    for de in (2, 1, 0):
                        key = (e1 + de, f1 - 2)
                        terms[key] = terms.get(key, 0) + c1 * (-4)
                elif e1 >= 4:
                    # m^4 = (m^3 - 2 m^2 + m - 2)/2
                    for de, cc in ((3, Fr(1, 2)), (2, Fr(-1)), (1, Fr(1, 2)), (0, Fr(-1))):
                        key = (e1 - 4 + de, f1)
                        terms[key] = terms.get(key, 0) + c1 * cc
                else:
                    out[(e1, f1)] = out.get((e1, f1), 0) + c1
            for key, v in out.items():
                r[key] = r.get(key, 0) + v
    return norm(r)

def add(p, q):
    r = dict(p)
    for k, v in q.items():
        r[k] = r.get(k, 0) + v
    return norm(r)

def neg(p):
    return {k: -v for k, v in p.items()}

def const(c):
    return norm({(0, 0): Fr(c)})

M_ = {(1, 0): Fr(1)}
S_ = {(0, 1): Fr(1)}

def mat(a, b, c, d):
    return [[a, b], [c, d]]

def mmul(A, B):
    return [[add(mul(A[i][0], B[0][j]), mul(A[i][1], B[1][j])) for j in range(2)] for i in range(2)]

def prod(*Ms):
    R = Ms[0]
    for X in Ms[1:]:
        R = mmul(R, X)
    return R

def is_scalar(A):
    return A[0][1] == {} and A[1][0] == {} and add(A[0][0], neg(A[1][1])) == {} and A[0][0] != {}

x = mat(const(1), {}, {}, const(-1))
z = mat({}, const(1), const(1), {})
a = mat({}, M_, const(1), {})
y = mat(S_, neg(mul(const(2), M_)), const(2), neg(S_))
b = prod(z, a, z)
c = prod(y, b, y)
rels = {
    "a^2": prod(a, a), "b^2": prod(b, b), "c^2": prod(c, c), "x^2": prod(x, x), "y^2": prod(y, y), "z^2": prod(z, z),
    "axax": prod(a, x, a, x), "ayay": prod(a, y, a, y), "azbz": prod(a, z, b, z), "bxbx": prod(b, x, b, x),
    "bycy": prod(b, y, c, y), "cxcz": prod(c, x, c, z), "(xz)^2": prod(x, z, x, z), "(xyz)^3": prod(x, y, z, x, y, z, x, y, z),
}
for name, R in rels.items():
    print(name, "scalar" if is_scalar(R) else "NOT SCALAR", R if not is_scalar(R) else "")

# numeric embeddings: roots of 2m^4 - m^3 + 2m^2 - m + 2
coef = [2, -1, 2, -1, 2]
def poly(t):
    v = 0
    for co in coef:
        v = v * t + co
    return v
roots = [complex(0.4, 0.9) ** k for k in range(4)]
for it in range(500):
    new = []
    for i, r in enumerate(roots):
        den = 2
        for j, q in enumerate(roots):
            if j != i:
                den *= (r - q)
        new.append(r - poly(r) / den)
    roots = new
for mv in roots:
    for sg in (1, -1):
        sv = sg * cmath.sqrt(-4 * (mv * mv + mv + 1))
        # xy = [[s,-2m],[-2,s]] ; tr^2/det
        tr, det = 2 * sv, sv * sv - 4 * mv
        ratio = tr * tr / det
        disc = cmath.sqrt(tr * tr - 4 * det)
        l1, l2 = (tr + disc) / 2, (tr - disc) / 2
        print("m=%.6f%+.6fi s=%.6f%+.6fi |poly|=%.1e tr^2/det(xy)=%.6f%+.6fi |l1/l2|=%.6f" % (
            mv.real, mv.imag, sv.real, sv.imag, abs(poly(mv)), ratio.real, ratio.imag, abs(l1 / l2)))
print("DONE")
