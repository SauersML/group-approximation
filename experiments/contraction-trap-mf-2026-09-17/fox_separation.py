# Metabelian Fox test for the rank-three contraction trap Gamma_3 = T(F_6, phi_C).
#
# Checks, exactly (sympy over Z[x1^+-1..x6^+-1] and over F_p):
#  (1) the Magnus homomorphism mg: F_6 -> G = Z[A]^6 x| A (A = Z^6 written multiplicatively,
#      mg(x_i) = (x_i, e_i), product (a,f)(b,h) = (ab, f + a h)) and the abelianized Fox Jacobian
#      D_{ji} = (d phi(x_j) / d x_i)^ab, read off as mg(phi(x_j)) = (phi_ab(x_j), row j of D);
#  (2) Phi(a,f) = (phi_ab(a), phi_ab(f) D) satisfies Phi o mg = mg o phi on random words
#      (chain rule), so t mg(x) t^-1 = mg(phi(x)) defines M = <F_6, g | C1-C6> -> Q = G_inf x| <t>;
#  (3) phi_ab is in GL_6(Z) and det D != 0, so Phi is injective and Q is an ascending HNN of G;
#  (4) certificate: a point x in (F_p^*)^6 where e_1 is NOT in the row space of D(x) over F_p.
#      Hence e_1 != h D for every h in Z[A]^6, so mg(a1) is not in Phi(G), so
#      t^-1 mg(a1) t is not in G, which contains mg(F_6): the image of y = g^-1 a1 g is outside
#      the image of A = F_6 in the solvable group Q;
#  (5) calibration: the Baumslag-Solitar toy trap a -> a^2 passes, an automorphism fails.
# Exit code 0 iff every check passes.
import random
import sys

import sympy as sp

fails = 0


def check(name, ok):
    global fails
    print(('PASS ' if ok else 'FAIL ') + name)
    if not ok:
        fails += 1


GENS = ['a1', 'a2', 'a3', 'a4', 'c', 'd']
X = sp.symbols('x1:7')
LAM = {g: X[i] for i, g in enumerate(GENS)}
MSYM = sp.symbols('m1:7')
MU = {g: MSYM[i] for i, g in enumerate(GENS)}


def W(s):
    return [(t[:-1], -1) if t.endswith("'") else (t, 1) for t in s.split()]


def inv(w):
    return [(g, -e) for g, e in reversed(w)]


def mg(word, lam=LAM, mu=MU):
    """Magnus image (a, f) of a word; f is linear in the formal basis symbols m_i."""
    L, F = sp.Integer(1), sp.Integer(0)
    for g, e in word:
        if e == 1:
            l, t = lam[g], mu[g]
        else:
            l, t = 1 / lam[g], -mu[g] / lam[g]
        F = F + L * t
        L = L * l
    return sp.simplify(L), sp.expand(F)


def row(F, msym=MSYM):
    return [sp.simplify(sp.diff(F, s)) for s in msym]


def rank_mod_p(rows, p):
    M = [[v % p for v in r] for r in rows]
    rk, ncol = 0, len(M[0])
    for col in range(ncol):
        piv = next((i for i in range(rk, len(M)) if M[i][col]), None)
        if piv is None:
            continue
        M[rk], M[piv] = M[piv], M[rk]
        iv = pow(M[rk][col], p - 2, p)
        M[rk] = [v * iv % p for v in M[rk]]
        for i in range(len(M)):
            if i != rk and M[i][col]:
                c = M[i][col]
                M[i] = [(vi - c * vr) % p for vi, vr in zip(M[i], M[rk])]
        rk += 1
    return rk


def fox_test(gens, phi, letter, primes=(5, 7, 11, 13), tries=20000, seed=1):
    """Return (phi_ab exponent matrix, D, det D, certificate or None)."""
    n = len(gens)
    x = sp.symbols('y1:%d' % (n + 1))
    lam = {g: x[i] for i, g in enumerate(gens)}
    ms = sp.symbols('n1:%d' % (n + 1))
    mu = {g: ms[i] for i, g in enumerate(gens)}
    D = sp.zeros(n, n)
    images = []
    for j, g in enumerate(gens):
        L, F = mg(phi[g], lam, mu)
        images.append(L)
        r = row(F, ms)
        for i in range(n):
            D[j, i] = sp.together(r[i])
    E = sp.Matrix([[sp.degree(sp.numer(sp.together(L)), xi) - sp.degree(sp.denom(sp.together(L)), xi)
                    for xi in x] for L in images])
    det = sp.factor(sp.together(D.det()))
    nums = [sp.lambdify(x, sp.numer(sp.together(D[j, i])), 'math') for j in range(n) for i in range(n)]
    dens = [sp.lambdify(x, sp.denom(sp.together(D[j, i])), 'math') for j in range(n) for i in range(n)]
    k = gens.index(letter)
    rng = random.Random(seed)
    for p in primes:
        for _ in range(tries):
            pt = [rng.randrange(1, p) for _ in range(n)]
            vals = []
            ok = True
            for a, b in zip(nums, dens):
                db = int(b(*pt)) % p
                if db == 0:
                    ok = False
                    break
                vals.append(int(a(*pt)) * pow(db, p - 2, p) % p)
            if not ok:
                continue
            Dp = [vals[j * n:(j + 1) * n] for j in range(n)]
            ek = [1 if i == k else 0 for i in range(n)]
            if rank_mod_p(Dp + [ek], p) > rank_mod_p(Dp, p):
                return E, D, det, (p, pt, Dp)
    return E, D, det, None


def phi_ab_subst(expr, gens, E, x):
    sub = {x[i]: sp.Mul(*[x[k] ** int(E[i, k]) for k in range(len(gens))]) for i in range(len(gens))}
    return sp.together(expr.subs(sub, simultaneous=True))


def chain_rule_check(gens, phi, D, E, trials=6, length=5, seed=7):
    """Phi(mg(u)) == mg(phi(u)) for random words u (the relation t mg(u) t^-1 = mg(phi(u)))."""
    n = len(gens)
    x = sp.symbols('y1:%d' % (n + 1))
    lam = {g: x[i] for i, g in enumerate(gens)}
    ms = sp.symbols('n1:%d' % (n + 1))
    mu = {g: ms[i] for i, g in enumerate(gens)}
    rng = random.Random(seed)
    for _ in range(trials):
        u = [(rng.choice(gens), rng.choice([1, -1])) for _ in range(length)]
        a, F = mg(u, lam, mu)
        f = sp.Matrix([row(F, ms)])
        lhs_a = phi_ab_subst(a, gens, E, x)
        lhs_f = sp.Matrix([[phi_ab_subst(v, gens, E, x) for v in f]]) * D
        phiu = []
        for g, e in u:
            phiu += phi[g] if e == 1 else inv(phi[g])
        b, H = mg(phiu, lam, mu)
        h = row(H, ms)
        if sp.simplify(lhs_a - b) != 0:
            return False
        if any(sp.simplify(lhs_f[i] - h[i]) != 0 for i in range(n)):
            return False
    return True


def run(name, gens, phi, letter, expect_pass):
    print('==', name)
    E, D, det, cert = fox_test(gens, phi, letter)
    check(name + ': phi_ab injective (exponent matrix det != 0)', E.det() != 0)
    print('   det(exponent matrix of phi_ab) =', E.det())
    check(name + ': det D != 0 in Q(A)', det != 0)
    print('   det D =', det)
    check(name + ': chain rule Phi o mg = mg o phi on random words', chain_rule_check(gens, phi, D, E))
    if expect_pass:
        check(name + ': F_p certificate, e_%s not in row space of D(x)' % letter, cert is not None)
        if cert:
            p, pt, Dp = cert
            print('   p =', p, ' point x =', pt)
            print('   D(x) mod p =', Dp)
            print('   rank D(x) =', rank_mod_p(Dp, p))
    else:
        # control: phi an automorphism of F, so D is invertible over Z[A]; no certificate may exist
        check(name + ': control finds no certificate', cert is None)
    return E, D, det, cert


# The rank-three contraction trap (jacobson-el3-is-not-lef, relations C1-C6).
U = W("a2 a4' a2 a1' a3 a1'")
PHI_C = {'a1': W('a2'), 'a2': W('c') + U + W('a1') + inv(U), 'a3': W('a4'),
         'a4': U + W('a3') + inv(U) + W("d'"), 'c': U + W('c') + inv(U), 'd': U + W('d') + inv(U)}

E, D, det, cert = run('Gamma_3 trap', GENS, PHI_C, 'a1', True)
check('Gamma_3: phi_ab in GL_6(Z)', abs(E.det()) == 1)

# Non-unit factor of det D (the metabelian obstruction polynomial).
y = sp.symbols('y1:7')
num = sp.numer(sp.together(det))
fl = sp.factor_list(num)
nonmono = [f for f, k in fl[1] if len(sp.Poly(f, *y).terms()) > 1]
print('   non-monomial factors of det D:', nonmono)
check('Gamma_3: det D is not a unit of Z[A] (has a non-monomial factor)', len(nonmono) >= 1)
if cert:
    p, pt, Dp = cert
    Pval = [int(f.subs(dict(zip(y, pt)))) % p for f in nonmono]
    print('   non-monomial factors at the certificate point (mod p):', Pval)

# Invariant-character specialization (x1=x2=al, x3=x4=be, x5=x6=1): det becomes a unit,
# which is why every phi-invariant affine representation g -> (gamma, 0) fails.
al, be = sp.symbols('alpha beta')
spec = {y[0]: al, y[1]: al, y[2]: be, y[3]: be, y[4]: 1, y[5]: 1}
dspec = sp.factor(sp.together(det.subs(spec)))
print('   det D at invariant characters =', dspec)
check('invariant-character specialization of det D is a monomial (unit)',
      len(sp.Poly(sp.numer(dspec), al, be).terms()) == 1)
check('P_C restricts to -alpha^2 beta on the phi-fixed torus',
      sp.expand(nonmono[0].subs(spec) + al ** 2 * be) == 0)
ga = sp.symbols('gamma')
Dspec = D.subs(spec)
cpoly = sp.factor(sp.together((Dspec - ga * sp.eye(6)).det()))
print('   det(D - gamma) on the fixed torus =', cpoly)
check('det(D - gamma) = (alpha^2 + beta gamma)(gamma-1)^4(gamma+1)/beta on the fixed torus',
      sp.simplify(cpoly - (al ** 2 + be * ga) * (ga - 1) ** 4 * (ga + 1) / be) == 0)
check('row a1 of D on the torus is e_a2 (relation C1: mu_a2 = gamma mu_a1)',
      list(Dspec.row(0)) == [0, 1, 0, 0, 0, 0])

# Calibration 1: Baumslag-Solitar toy trap <a, g, e | g a g^-1 = a^2, [e, a]>.
run('BS(1,2) toy trap', ['a'], {'a': W('a a')}, 'a', True)
# Calibration 2 (control): an automorphism a1 -> a1 a2, a2 -> a2 (no trap; y lies in A).
run('automorphism control', ['a1', 'a2'], {'a1': W('a1 a2'), 'a2': W('a2')}, 'a1', False)

print('fails =', fails)
sys.exit(1 if fails else 0)
