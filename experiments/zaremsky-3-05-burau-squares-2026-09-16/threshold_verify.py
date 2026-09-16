"""Exact sympy checks for the closed projective ping-pong threshold
(f^m, k^n), Witzel-Zaremsky generators of the reduced Burau image of B_4.
Checks the hypotheses of the obstruction lemma for min(m,n) <= 2 (on P^2 and
on the dual plane), the conjugacy P A(-t) P^-1 = f, P B(-t) P^-1 = k, and
that the lemma's hypotheses fail for exponent 3 (consistency).
All nonvanishing entries are checked to be +-t^a * product of cyclotomic
polynomials, so they are nonzero at every t0 with |t0| != 1 in every field."""
import sympy as sp
t = sp.symbols('t')
f = sp.diag(t, 1, 1/t)
k = sp.Matrix([[0, -1-t, -1/t-1-t], [0, 1/t+1+t, t**-2+1/t+1+t], [1, 0, 0]])
s = sp.Matrix([[1, 1, 1/t], [-(t**-2+1), -(1/t+1), -(t**-2+1)], [1/t, 1, 1]])
assert sp.simplify(k - s*f*s.inv()) == sp.zeros(3)
assert sp.factor(s.det()) == sp.factor((t-1)**3/t**3)
CYC = [sp.cyclotomic_poly(n, t) for n in range(1, 40)]

def cyclo_ok(x):
    x = sp.factor(sp.together(x))
    if x == 0:
        return False
    for part in (sp.numer(x), sp.denom(x)):
        c, fl = sp.factor_list(part)
        if abs(c) != 1:
            return False
        for p, _ in fl:
            if p != t and not any(sp.expand(p - q) == 0 or sp.expand(p + q) == 0 for q in CYC):
                return False
    return True

e1, e2, e3 = [sp.eye(3)[:, i] for i in range(3)]

def lemma_hyp(b):
    """b in a frame where a = diag(t^e, 1, t^-e). Returns which hypothesis holds."""
    bi = sp.simplify(b.inv())
    # (i) b{x3=0} != {x3=0}: some of b e1, b e2 has x3 != 0 (nonvanishing at t0)
    i1 = cyclo_ok((b*e1)[2]) or cyclo_ok((b*e2)[2])
    i2 = cyclo_ok((b*e2)[0]) or cyclo_ok((b*e3)[0])
    out = {'(i)': i1 and i2}
    for eps, (M, N) in {+1: (b, bi), -1: (bi, b)}.items():
        v, w = sp.simplify(M*e1), sp.simplify(N*e3)
        ok = (sp.simplify(v[2]) == 0 and cyclo_ok(v[1]) and
              sp.simplify(w[0]) == 0 and cyclo_ok(w[1]))
        out['(ii) eps=%+d' % eps] = ok
    hit = False
    for M in (b, bi):
        for v in (M*e1, M*e3):
            v = sp.simplify(v)
            if (sp.simplify(v[1]) == 0 and sp.simplify(v[2]) == 0) or \
               (sp.simplify(v[0]) == 0 and sp.simplify(v[1]) == 0):
                hit = True
    out["(ii')"] = hit
    return out

def verdict(h):
    return h['(i)'] and (h['(ii) eps=+1'] or h['(ii) eps=-1'] or h["(ii')"])

res = {}
for m in (1, 2, 3):
    for n in (1, 2, 3):
        a_fr = verdict(lemma_hyp(k**n))                       # a = f^m, frame e
        b_fr = verdict(lemma_hyp(sp.simplify(s.inv()*f**m*s)))  # a = k^n, frame s
        # dual plane: g acts by (g^-1)^T
        fd = f**(-m); kd = sp.simplify((k**(-n)).T)
        sd = sp.simplify(s.inv().T)       # kd = sd f^-n sd^-1
        assert sp.simplify(kd - sd*f**(-n)*sd.inv()) == sp.zeros(3)
        da = verdict(lemma_hyp(kd))
        db = verdict(lemma_hyp(sp.simplify(sd.inv()*fd*sd)))
        res[(m, n)] = (a_fr, b_fr, da, db)
        print('m=%d n=%d  P2: X_a closed obstr %s | X_b closed obstr %s   dual: %s | %s'
              % (m, n, a_fr, b_fr, da, db))
for n in (1, 2):
    assert res[(3, n)][0] and res[(3, n)][2]
for m in (1, 2):
    assert res[(m, 3)][1] and res[(m, 3)][3]
assert not any(res[(3, 3)])
print('k e1 =', list(k*e1), ' k^2 e1 =', [sp.factor(x) for x in k**2*e1])
print('k^-2 e3 =', [sp.factor(x) for x in sp.simplify(k**-2*e3)])
for m in (1, 2):
    M = sp.simplify(s.inv()*f**m*s)
    print('m=%d M e3 =' % m, [sp.factor(x) for x in M*e3],
          ' M^-1 e1 =', [sp.factor(x) for x in sp.simplify(M.inv()*e1)])
# conjugacy to the Beridze-Bigelow-Traczyk matrices
A = sp.Matrix([[0, 0, 1/t], [0, t, 1/t-t], [-1, 0, 1/t+1]])      # A(-t)
B = sp.Matrix([[1/t, 1, 0], [0, 1, 0], [0, 1, t]])                # B(-t)
P = sp.Matrix([[-t, -t**2+t, t**2], [t**2+1, 0, -t**2-1], [-t**2, 0, t]])
assert sp.simplify(P*A - f*P) == sp.zeros(3) and sp.simplify(P*B - k*P) == sp.zeros(3)
print('det P =', sp.factor(P.det()))
assert sp.factor(P.det()) == sp.factor(-t**2*(t-1)**2*(t**2+1))
# explicit matrices quoted in the artifact, section 3
u, w, z = t+1, t**2+1, t**2+t+1
KI = sp.Matrix([[0, 0, 1], [u*w/t**2, z/t, 0], [-z/t, -u, 0]])
K2 = sp.Matrix([[-z/t, -u*z/t, -u**2*w/t**2], [u*w/t**2, z**2/t**2, u*w*z/t**3], [0, -u, -z/t]])
K2I = sp.Matrix([[-z/t, -u, 0], [u*w*z/t**3, z**2/t**2, u*w/t**2], [-u**2*w/t**2, -u*z/t, -z/t]])
assert sp.simplify(k.inv() - KI) == sp.zeros(3)
assert sp.simplify(k**2 - K2) == sp.zeros(3)
assert sp.simplify(k.inv()**2 - K2I) == sp.zeros(3)
# symmetry s: s^-1 f s = k^-1 and s^-1 k s = f
assert sp.simplify(s.inv()*f*s - KI) == sp.zeros(3)
assert sp.simplify(s.inv()*k*s - f) == sp.zeros(3)
# exponent 3 vector
assert sp.simplify((k**3*e1)[2] + z/t) == 0
print('ALL CHECKS PASSED')
