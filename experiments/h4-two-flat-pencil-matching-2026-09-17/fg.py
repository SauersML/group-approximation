"""Fast exact Case 1 relation test through the faithful Artin action of P_7 on F_7.

F is normal in P and rho_a is injective on F with the same image F_Y in every shadow (gens_cache.pkl: the F images
agree in V0, V1, V2).  So for alpha in F and beta in N,  beta^-1 alpha beta  is determined by the braid
rho_0(beta)^-1 rho_0(alpha) rho_0(beta), and the Case 1 relation
    beta_3^-1 (alpha_1 alpha_2) beta_3 = alpha_1 beta_1 alpha_2 beta_1^-1        (*)
holds in P iff it holds for the rho_0 images in P_7 iff the two braids induce the same automorphism of F_7
(Artin's representation is faithful).  The key of a braid is the tuple of reduced images of x_1..x_7.
Consequence used below: the N-letters x6, x7, x8, x9, x10 have trivial rho_0 image, so they centralise F; the
relation (*) and the three x-arcs depend on beta_1, beta_3 only modulo the subgroup K they generate.
"""
import os, pickle, itertools

HERE = os.path.dirname(os.path.abspath(__file__))
FGEN, NGEN = pickle.load(open(os.path.join(HERE, 'gens_cache.pkl'), 'rb'))
NS = 7


def red(w):
    out = []
    for g in w:
        if out and out[-1] == -g:
            out.pop()
        else:
            out.append(g)
    return tuple(out)


def winv(w):
    return tuple(-g for g in reversed(w))


def _sig(i, e):
    """automorphism of F_7 (images of x_1..x_7) for sigma_i^e: x_i -> x_i x_{i+1} x_i^-1, x_{i+1} -> x_i."""
    im = [(k,) for k in range(1, NS + 1)]
    if e == 1:
        im[i - 1] = (i, i + 1, -i)
        im[i] = (i,)
    else:
        im[i - 1] = (i + 1,)
        im[i] = (-(i + 1), i, i + 1)
    return tuple(im)


SIG = {(i, e): _sig(i, e) for i in range(1, NS) for e in (1, -1)}
ID = tuple((k,) for k in range(1, NS + 1))


def sub(phi, w):
    """phi applied to the word w"""
    out = []
    for g in w:
        out += phi[g - 1] if g > 0 else winv(phi[-g - 1])
    return red(out)


def comp(phi, psi):
    """phi o psi"""
    return tuple(sub(phi, psi[k]) for k in range(NS))


def aut(braid):
    phi = ID
    for g in braid:
        phi = comp(phi, SIG[(abs(g), 1 if g > 0 else -1)])
    return phi


def ainv(phi):
    """inverse automorphism, by composing the letters backwards is not available; use the braid instead"""
    raise NotImplementedError


FA_ = {g[0]: aut(g[2][0]) for g in FGEN}
FAi = {g[0]: aut([-x for x in reversed(g[2][0])]) for g in FGEN}
NA_ = {g[0]: aut(g[2][0]) for g in NGEN}
NAi = {g[0]: aut([-x for x in reversed(g[2][0])]) for g in NGEN}
EFF = [g[0] for g in NGEN if g[2][0]]          # N-letters acting non-trivially on F (rho_0 image non-trivial)


def fword(spec):
    """automorphism of an F-word given as list of (name, sign)"""
    phi = ID
    for n, s in spec:
        phi = comp(phi, FA_[n] if s == 1 else FAi[n])
    return phi


def nword(spec):
    phi = ID
    for n, s in spec:
        phi = comp(phi, NA_[n] if s == 1 else NAi[n])
    return phi


def nword_inv(spec):
    return nword([(n, -s) for n, s in reversed(spec)])


def words(names, L):
    let = [(n, 1) for n in names] + [(n, -1) for n in names]
    out = []
    for n in range(1, L + 1):
        for w in itertools.product(let, repeat=n):
            if any(w[k][0] == w[k + 1][0] and w[k][1] == -w[k + 1][1] for k in range(n - 1)):
                continue
            out.append(w)
    return out


def spec(w):
    return ' '.join(n + ('' if s == 1 else "'") for n, s in w)
