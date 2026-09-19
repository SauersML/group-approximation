"""Genuine braid monodromy of the three fibred I_2(5) shadows rho_a : P -> G_a in P_7.

An H_4 Artin word (letters +-i, i = 1..4, generator s_i) is realised as a path in M(A) from a real base point b
of the fundamental chamber (Brieskorn): the letter s_i^{e} after prefix w in W is the path
    w( b + tau (s_i b - b) + i e eps sin(pi tau) alpha_i ),  tau in [0,1],
which crosses only the wall w(H_i).  For a pure word the path closes.  Along it the fibre points
lambda_H(z) = -<n_H,z>/<n_H,x> of the 6 fibre walls of V_a, together with t = 0, trace a pure 7-strand braid; it is
read off from real-part swaps (sign = which point passes above).  Strands are numbered by the real order at b,
which is q q q p p p t (collision walls are walls of A, so this order is constant on the chamber).
Everything is floating point on the exact root system; the swap reader bisects until each step is a single
adjacent transposition."""
import itertools, os, sys
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', '..', 'lib'))
from fibred import setup, through, walls, is_wall

n, sim, W, om = setup('H4'); x = om[0]; y = om[3]
Ax = through(W, [x]); Ay = through(W, [y]); Az = through(W, [x, y])
Ap = walls(Ax + Ay); Ayz = [w for w in Ay if not is_wall(w, Az)]; Axz = [w for w in Ax if not is_wall(w, Az)]
SIM = [np.array(s, float) for s in sim]


def idx(v):
    v = v / np.linalg.norm(v)
    for k, w in enumerate(W):
        if abs(abs(np.dot(v, w)) - 1) < 1e-9:
            return k
    return None


def name(k):
    w = W[k]
    if is_wall(w, Az):
        return 'z%d' % [idx(u) for u in Az].index(k)
    if is_wall(w, Ayz):
        return 'p%d' % ([idx(u) for u in Ayz].index(k) + 1)
    if is_wall(w, Axz):
        return 'x%d' % [idx(u) for u in Axz].index(k)
    return 'o%d' % k


flats = []   # (walls of V as index set, fibre wall normals)
for w1 in Ayz:
    for w2 in Axz:
        B2 = np.array([w1, w2]); Pr = B2.T @ np.linalg.pinv(B2.T)
        AV = [w for w in W if np.linalg.norm(Pr @ w - w) < 1e-9]
        if len(AV) != 5:
            continue
        Bw = walls(Ap + AV)
        fib = [w for w in Bw if abs(np.dot(w, x)) > 1e-9]
        good = all(is_wall(np.dot(v, x) * u - np.dot(u, x) * v, Ax) for u, v in itertools.combinations(fib, 2))
        key = frozenset(idx(w) for w in AV)
        if good and key not in [f[0] for f in flats]:
            flats.append((key, fib))

BASE = sum(c * om[j] for j, c in enumerate([1.0, 1.37, 0.81, 1.13]))
EPS = 0.45
JIT = 1e-7 * np.exp(2j * np.pi * np.array([0.13, 0.71, 0.37, 0.93, 0.29, 0.57, 0.0]))
ROT = np.exp(-0.0137j)   # generic projection direction: breaks simultaneous real-part ties


def refl_mat(a):
    return np.eye(4) - 2 * np.outer(a, a) / np.dot(a, a)


SMAT = [refl_mat(a) for a in SIM]


class Shadow:
    """fibre points of one flat, ordered by real part at BASE; strand 7 = t = 0."""

    def __init__(self, a):
        self.a = a
        fib = flats[a][1]
        lam0 = [-np.dot(f, BASE) / np.dot(f, x) for f in fib]
        order = sorted(range(6), key=lambda k: lam0[k])
        self.fib = np.array([fib[k] for k in order])
        self.lab = [name(idx(fib[k])) for k in order] + ['t']
        self.den = self.fib @ x
        assert all(l < 0 for l in lam0), lam0

    def pts(self, z):
        return (np.concatenate([-(self.fib @ z) / self.den, [0j]]) + JIT) * ROT


def path_points(word, shadows, steps=64):
    """yield, per letter, a function tau -> z (complex 4-vector)."""
    Wm = np.eye(4)
    for g in word:
        i, e = abs(g) - 1, (1 if g > 0 else -1)
        b0 = Wm @ BASE; b1 = Wm @ (SMAT[i] @ BASE); al = Wm @ SIM[i]
        yield (lambda tau, b0=b0, b1=b1, al=al, e=e: b0 + tau * (b1 - b0) + 1j * e * EPS * np.sin(np.pi * tau) * al)
        Wm = Wm @ SMAT[i]
    assert True


def weyl(word):
    Wm = np.eye(4)
    for g in word:
        Wm = Wm @ SMAT[abs(g) - 1]
    return Wm


def is_pure(word):
    return np.allclose(weyl(word), np.eye(4), atol=1e-9)


def _order(p):
    return tuple(np.argsort(p.real, kind='stable'))


def read_braid(sh, word, steps=48):
    """pure 7-strand braid word (ints +-k = sigma_k^{+-1}) of the loop 'word' in the shadow sh."""
    out = []
    cur = None
    for seg in path_points(word, [sh]):
        f = lambda tau: sh.pts(seg(tau))
        if cur is None:
            cur = list(_order(f(0.0)))
        ts = np.linspace(0, 1, steps + 1)
        for t0, t1 in zip(ts[:-1], ts[1:]):
            _advance(f, t0, t1, cur, out, 0)
    assert cur == list(range(7)), ('not pure in shadow', cur)
    return out


def _advance(f, t0, t1, cur, out, depth):
    new = list(_order(f(t1)))
    if new == cur:
        return
    diff = [k for k in range(7) if new[k] != cur[k]]
    if len(diff) == 2 and diff[1] == diff[0] + 1 and new[diff[0]] == cur[diff[1]] and new[diff[1]] == cur[diff[0]]:
        k = diff[0]; L, R = cur[k], cur[k + 1]
        a, b = t0, t1
        for _ in range(60):
            m = (a + b) / 2
            p = f(m)
            if p[L].real < p[R].real:
                a = m
            else:
                b = m
        p = f((a + b) / 2)
        if abs(p[L] - p[R]) < 1e-5:
            raise RuntimeError('near collision')
        out.append((k + 1) if p[L].imag > p[R].imag else -(k + 1))
        cur[k], cur[k + 1] = R, L
        return
    if depth >= 40:
        raise RuntimeError('cannot isolate swaps %s -> %s' % (cur, new))
    m = (t0 + t1) / 2
    _advance(f, t0, m, cur, out, depth + 1)
    _advance(f, m, t1, cur, out, depth + 1)


def free_reduce(w):
    out = []
    for g in w:
        if out and out[-1] == -g:
            out.pop()
        else:
            out.append(g)
    return out


SH = [Shadow(a) for a in range(len(flats))]

if __name__ == '__main__':
    for sh in SH:
        print('V%d strands' % sh.a, ' '.join('%d:%s' % (k + 1, l) for k, l in enumerate(sh.lab)))
    for i in range(1, 5):
        w = [i, i]
        print('s%d^2' % i, [free_reduce(read_braid(sh, w)) for sh in SH])
