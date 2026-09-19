"""Operator-norm twisted Iwahori matching for W_3 (theta = pi/3), second-generation optimiser.

Problem (node sl2-half-triple-cover-mf-iff-twisted-iwahori-opnorm-matching, swarm branch, Theorem A):
unknowns are exact unitary reps (s, r), (S, R) of PSL_2(Z) = C_2 * C_3 on C^n (s^2 = S^2 = 1, r^3 = R^3 = 1), and

    delta = max( || S R - g (s r)^2 || , || s r^-1 - g^-1 (S R^-1)^2 || ),     g = exp(-i theta / 6).

W_3 is MF iff inf_n delta_n(pi/3) = 0.

Differences from the w18 optimiser (match.py): exact spectra throughout (s = V diag(+-1) V^*, r = V diag(mu_3) V^*),
L-BFGS with strong-Wolfe line search on the normalised Schatten-p surrogate, p ramped 8 -> 2048 by repeated squaring
of D^*D / c^2 (no eigh backward), and seeds built from exact SL_2(F_p) data, their tensor products with exact
theta = 0 representations, and random unitary conjugates.  The reported number is always the float64 operator norm
of exact data (relator error ~ 1e-14), so every reported value is a certified upper bound for delta_n(pi/3).
"""
import math, sys, time, argparse
import numpy as np
import torch

torch.set_default_dtype(torch.float64)
CD = torch.complex128
W = np.exp(2j * np.pi / 3)


# ---------------------------------------------------------------- exact seeds from SL_2(F_p) on F_p^2 \ 0
def gens_mod(p):
    inv2 = pow(2, -1, p)
    x = np.array([[0, -1], [1, 0]]) % p              # over S
    y = np.array([[0, -1], [1, 1]]) % p              # over S T
    X = np.array([[0, -2], [inv2, 0]]) % p           # a x a^-1
    Y = np.array([[0, -2], [inv2, 1]]) % p           # a y a^-1
    return x, y, X, Y


def perm_parts(p):
    pts = [(a, b) for a in range(p) for b in range(p) if (a, b) != (0, 0)]
    idx = {v: i for i, v in enumerate(pts)}
    N = len(pts)

    def P(g):
        M = np.zeros((N, N))
        for v, i in idx.items():
            w = tuple(int(t) for t in (g @ np.array(v)) % p)
            M[idx[w], i] = 1
        return M
    mats = [P(g) for g in gens_mod(p)]
    # even / odd bases
    seen, ev, od = set(), [], []
    for v in pts:
        if v in seen:
            continue
        mv = ((-v[0]) % p, (-v[1]) % p)
        seen |= {v, mv}
        e = np.zeros(N); e[idx[v]] = 1
        f = np.zeros(N); f[idx[mv]] = 1
        ev.append((e + f) / math.sqrt(2)); od.append((e - f) / math.sqrt(2))
    Be, Bo = np.array(ev).T, np.array(od).T
    E = [Be.T @ M @ Be for M in mats]
    O = [Bo.T @ M @ Bo for M in mats]
    return E, O


def block_data(mats, theta0):
    """(x, y, X, Y) exact with c = x^2 = e^{i theta0}  ->  (s, r, S, R)."""
    al, be = np.exp(1j * theta0 / 2), np.exp(1j * theta0 / 3)
    x, y, X, Y = [m.astype(complex) for m in mats]
    return [x / al, y / be, X / al, Y / be]


def seed(tokens):
    """tokens: E<p> (theta=0 even part), O<p> (theta=pi odd part), 1 (trivial), N<k> (k-dim random exact point)."""
    blocks = []
    for t in tokens:
        if t == '1':
            blocks.append([np.eye(1, dtype=complex)] * 4)
        elif t.startswith('L:'):  # previously saved exact data (direct summand)
            z = np.load(t[2:]); blocks.append([z['s'], z['r'], z['S'], z['R']])
        elif t[0] in 'EO':
            E, O = perm_parts(int(t[1:]))
            blocks.append(block_data(E, 0.0) if t[0] == 'E' else block_data(O, math.pi))
    n = sum(b[0].shape[0] for b in blocks)
    out = []
    for k in range(4):
        M = np.zeros((n, n), dtype=complex); o = 0
        for b in blocks:
            d = b[k].shape[0]; M[o:o + d, o:o + d] = b[k]; o += d
        out.append(M)
    return out


def tensor(A, B):
    return [np.kron(a, b) for a, b in zip(A, B)]


# ---------------------------------------------------------------- defects and certification
def defects_np(s, r, S, R, g):
    T = s @ r
    L = S @ R.conj().T
    return S @ R - g * T @ T, s @ r.conj().T - (1 / g) * L @ L


def certify(s, r, S, R, theta):
    g = np.exp(-1j * theta / 6)
    n = s.shape[0]; I = np.eye(n)
    nrm = lambda A: float(np.linalg.norm(A, 2))
    rel = max(nrm(s @ s - I), nrm(S @ S - I), nrm(r @ r @ r - I), nrm(R @ R @ R - I),
              max(nrm(M.conj().T @ M - I) for M in (s, r, S, R)))
    DT, DU = defects_np(s, r, S, R, g)
    return max(nrm(DT), nrm(DU)), rel


def windings(s, r, S, R, theta):
    g = np.exp(-1j * theta / 6)
    T = s @ r; L = S @ R.conj().T
    A = S @ R @ np.linalg.inv(g * T @ T)
    B = s @ r.conj().T @ np.linalg.inv((1 / g) * L @ L)
    n = s.shape[0]
    tT = np.sum(np.angle(np.linalg.eigvals(A))); tU = np.sum(np.angle(np.linalg.eigvals(B)))
    return round((tT - n * theta / 6) / (math.pi / 3), 3), round((tU + n * theta / 6) / (math.pi / 3), 3)


# ---------------------------------------------------------------- optimiser
def to_param(s, r, S, R):
    """Diagonalise each exact unitary: M = V diag(ev) V^*; returns (V list, eigenvalue list)."""
    Vs, evs = [], []
    for M in (s, r, S, R):
        H = (M + M.conj().T) / 2 + 1e-9 * np.diag(np.arange(M.shape[0]))  # not used for spectra
        ev, V = np.linalg.eig(M)
        # exact spectra: snap
        order = 2 if np.allclose(M @ M, np.eye(M.shape[0]), atol=1e-8) else 3
        k = np.round(np.angle(ev) / (2 * np.pi / order)) % order
        ev = np.exp(2j * np.pi * k / order)
        # orthonormalise eigenvectors within eigenspaces (normal matrix): QR of V per eigenvalue
        Q = np.zeros_like(V)
        for kk in range(order):
            cols = np.where(k == kk)[0]
            if len(cols):
                q, _ = np.linalg.qr(V[:, cols]); Q[:, cols] = q
        q, _ = np.linalg.qr(Q)  # global polish (eigenspaces already orthogonal for unitary M)
        Vs.append(Q); evs.append(ev)
    return Vs, evs


class Model:
    def __init__(self, data, theta, noise=0.0, rng=None):
        Vs, evs = to_param(*data)
        self.n = data[0].shape[0]
        self.V0 = [torch.tensor(V, dtype=CD) for V in Vs]
        self.ev = [torch.tensor(e, dtype=CD) for e in evs]
        rng = rng or np.random.default_rng(0)
        self.A = [torch.tensor(noise * (rng.standard_normal((self.n, self.n)) + 1j * rng.standard_normal((self.n, self.n)))
                               / math.sqrt(self.n), dtype=CD).requires_grad_(True) for _ in range(4)]
        self.g = complex(np.exp(-1j * theta / 6))
        self.theta = theta

    def mats(self):
        out = []
        for V0, e, A in zip(self.V0, self.ev, self.A):
            K = (A - A.conj().T) / 2
            V = torch.linalg.matrix_exp(K) @ V0
            out.append(V @ torch.diag(e) @ V.conj().T)
        return out

    def D(self):
        s, r, S, R = self.mats()
        T = s @ r; L = S @ R.conj().T
        return S @ R - self.g * T @ T, s @ r.conj().T - (1 / self.g) * L @ L

    def exact_np(self):
        with torch.no_grad():
            return [M.numpy().copy() for M in self.mats()]


def schatten(D, p, c):
    M = D.conj().T @ D / (c * c)
    k = p // 2
    while k > 1:
        M = M @ M
        k //= 2
    return torch.real(torch.trace(M))


def adam_phase(model, ps=(8, 32, 128, 256), steps=400, lr=0.03, verbose=False):
    """w18-style Adam on log Schatten mass with geometric lr decay (global exploration)."""
    opt = torch.optim.Adam(model.A, lr=lr)
    sched = torch.optim.lr_scheduler.ExponentialLR(opt, gamma=(1e-2) ** (1.0 / (len(ps) * steps)))
    for p in ps:
        for it in range(steps):
            DT, DU = model.D()
            loss = torch.log(schatten(DT, p, 1.0) + schatten(DU, p, 1.0) + 1e-300) / p
            opt.zero_grad(); loss.backward(); opt.step(); sched.step()
        if verbose:
            d, rel = certify(*model.exact_np(), model.theta)
            print(f'  adam p={p} delta={d:.6f}', flush=True)


def optimise(model, ps=(8, 32, 128, 512, 2048), iters=150, verbose=False, adam=0):
    best = (9.0, None)
    if adam:
        adam_phase(model, steps=adam, verbose=verbose)
        best = (certify(*model.exact_np(), model.theta)[0], model.exact_np())
    for p in ps:
        snap = [A.detach().clone() for A in model.A]
        with torch.no_grad():
            DT, DU = model.D()
            c = max(float(torch.linalg.matrix_norm(DT, 2)), float(torch.linalg.matrix_norm(DU, 2)), 1e-6)
        opt = torch.optim.LBFGS(model.A, lr=1, max_iter=iters, history_size=30, line_search_fn='strong_wolfe',
                                tolerance_grad=1e-12, tolerance_change=1e-15)

        def closure():
            opt.zero_grad()
            DT, DU = model.D()
            loss = c * (schatten(DT, p, c) + schatten(DU, p, c)) ** (1.0 / p)
            loss.backward()
            return loss
        try:
            opt.step(closure)
        except Exception as ex:  # numerical failure: keep best
            if verbose:
                print('  lbfgs failure', ex, flush=True)
        ok = all(bool(torch.isfinite(A).all()) for A in model.A)
        try:
            d, rel = certify(*model.exact_np(), model.theta) if ok else (9.0, 9.0)
        except np.linalg.LinAlgError:
            d, rel = 9.0, 9.0
        if d < best[0]:
            best = (d, model.exact_np())
        elif d > best[0] + 1e-9:  # overflow or regression: restore snapshot, stop ramp
            with torch.no_grad():
                for A, S0 in zip(model.A, snap):
                    A.copy_(S0)
            if verbose:
                print(f'  p={p} regressed ({d:.3g}); restored', flush=True)
            break
        if verbose:
            print(f'  p={p} delta={d:.6f} rel={rel:.1e}', flush=True)
    return best


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--seed', nargs='+', default=['O3', 'E3', 'E3'])
    ap.add_argument('--tensor', nargs='*', default=[], help='tensor the seed with exact theta=0 data, e.g. E3')
    ap.add_argument('--theta', type=float, default=1 / 3, help='units of pi')
    ap.add_argument('--noise', type=float, default=0.3)
    ap.add_argument('--restarts', type=int, default=2)
    ap.add_argument('--iters', type=int, default=150)
    ap.add_argument('--adam', type=int, default=0, help='Adam steps per p before the L-BFGS polish')
    ap.add_argument('--load', default=None)
    ap.add_argument('--save', default=None)
    a = ap.parse_args()
    th = a.theta * math.pi
    if a.load:
        z = np.load(a.load); data = [z['s'], z['r'], z['S'], z['R']]
    else:
        data = seed(a.seed)
    for t in a.tensor:
        data = tensor(data, seed([t]))
    d0, rel0 = certify(*data, th)
    print(f'seed={a.seed} tensor={a.tensor} load={a.load} n={data[0].shape[0]} theta={a.theta}pi start delta={d0:.5f} '
          f'rel={rel0:.1e} w={windings(*data, th)}', flush=True)
    best = (9.0, None)
    for k in range(a.restarts):
        t0 = time.time()
        m = Model(data, th, noise=a.noise if (k > 0 or not a.load) else a.noise * 0.3, rng=np.random.default_rng(k))
        d, mats = optimise(m, iters=a.iters, verbose=True, adam=a.adam)
        dd, rel = certify(*mats, th)
        print(f' restart {k}: delta={dd:.6f} rel={rel:.1e} w={windings(*mats, th)} secs={time.time()-t0:.0f}', flush=True)
        if dd < best[0]:
            best = (dd, mats)
    d, mats = best
    print(f'BEST n={mats[0].shape[0]} delta={d:.6f} profile 2sin(pi/36)={2*math.sin(math.pi/36):.6f}', flush=True)
    if a.save:
        np.savez_compressed(a.save, s=mats[0], r=mats[1], S=mats[2], R=mats[3])


if __name__ == '__main__':
    main()
