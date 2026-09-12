"""Randomized sanity check of the robust Lemma 3.5 inequality for Radu's lattice.

For involutions a,b,c,x,y,z on d points, with normalized Hamming distance d_H,
eps1..eps6 = defects of axax, ayay, azbz, bxbx, bycy, cxcz,
delta = xz, u = y delta^2 y, kappa1 = d_H(u delta, delta u), kappa2 = d_H(u delta b, delta b u),
the claimed bounds are

  d_H(delta^4, 1) <= 2 kappa1 + 3e1 + 2e2 + 4e3 + e4 + 2e5 + 4e6
  d_H(delta^4, 1) <= 2 kappa2 + 9e1 + 6e2 + 12e3 + 3e4 + 2e5 + 4e6
  kappa1 <= kappa2 + (e1 + 2e2 + 2e3 + e4) + 2e1 + 2e3      (and symmetric)

Words are group products g1 g2 ... gk acting on the left (rightmost first).
"""
import random, sys

def compose(p, q):
    return [p[i] for i in q]

def inv(p):
    r = [0]*len(p)
    for i, j in enumerate(p):
        r[j] = i
    return r

def dH(p, q):
    return sum(1 for i, j in zip(p, q) if i != j) / len(p)

def ident(d):
    return list(range(d))

def prod(*ps):
    r = ident(len(ps[0]))
    for p in ps:
        r = compose(r, p)
    return r

def rand_invol(d, rng, fixfrac):
    pts = list(range(d)); rng.shuffle(pts)
    p = ident(d)
    nfix = int(fixfrac * d)
    rest = pts[nfix:]
    for i in range(0, len(rest) - 1, 2):
        u, v = rest[i], rest[i+1]
        p[u], p[v] = v, u
    return p

def near_model(d, rng):
    """start from a random exact-ish structure then perturb: gives small defects sometimes"""
    a = rand_invol(d, rng, rng.random()*0.3)
    x = rand_invol(d, rng, rng.random()*0.3)
    y = rand_invol(d, rng, rng.random()*0.3)
    z = rand_invol(d, rng, rng.random()*0.3)
    b = prod(z, a, z)                       # exact azbz
    c = prod(y, b, y)                       # exact bycy
    return a, b, c, x, y, z

def check(a, b, c, x, y, z):
    d = len(a); I = ident(d)
    e1 = dH(prod(a, x, a, x), I)
    e2 = dH(prod(a, y, a, y), I)
    e3 = dH(prod(a, z, b, z), I)
    e4 = dH(prod(b, x, b, x), I)
    e5 = dH(prod(b, y, c, y), I)
    e6 = dH(prod(c, x, c, z), I)
    dl = prod(x, z)
    dl2 = prod(dl, dl)
    u = prod(y, dl2, y)
    k1 = dH(prod(u, dl), prod(dl, u))
    db = prod(dl, b)
    k2 = dH(prod(u, db), prod(db, u))
    mark = dH(prod(dl2, dl2), I)
    lam = e1 + 2*e2 + 2*e3 + e4
    r1 = 2*k1 + 3*e1 + 2*e2 + 4*e3 + e4 + 2*e5 + 4*e6
    r2 = 2*k2 + 9*e1 + 6*e2 + 12*e3 + 3*e4 + 2*e5 + 4*e6
    ok = (mark <= r1 + 1e-12) and (mark <= r2 + 1e-12) \
         and (k1 <= k2 + lam + 2*e1 + 2*e3 + 1e-12) and (k2 <= k1 + lam + 2*e1 + 2*e3 + 1e-12)
    return ok, dict(e=(e1, e2, e3, e4, e5, e6), k1=k1, k2=k2, mark=mark, r1=r1, r2=r2)

if __name__ == '__main__':
    rng = random.Random(20260911)
    trials = 0; fails = 0; tight = 0.0
    for d in [8, 12, 30, 64, 128]:
        for t in range(400):
            gens = near_model(d, rng) if t % 2 else tuple(rand_invol(d, rng, rng.random()*0.5) for _ in range(6))
            ok, info = check(*gens)
            trials += 1
            if not ok:
                fails += 1
                print('FAIL', d, info); sys.stdout.flush()
            if info['r1'] > 0:
                tight = max(tight, info['mark'] / info['r1'])
    # exact-model sanity: a structured example where all six relators hold exactly
    print(f'trials {trials}, failures {fails}, max mark/r1 ratio {tight:.4f}')
