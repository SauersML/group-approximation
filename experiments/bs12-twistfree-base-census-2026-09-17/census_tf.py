"""Census over exact BS(1,2) pairs whose base has order M prime to 3 (twist-free bases).

Sharp test pair (as in bs12-twisted-clock-exact-pair-census):
  N odd, 3 | N,  D e_j = w^j e_j,  W e_j = e_(j/2 mod N),  V e_j = e_(j+1),
  A_s = W exp(i s (V + V^*)).

Base class (new).  Fix odd M <= N and r = N - M >= 0.  The base spectrum is the
multiset {e^(2 pi i k/M) : k in Z/M} plus r extra copies of 1.  Squaring permutes
Z/M (M odd) and fixes 0, so multiplicities are squaring-invariant and every exact
pair with this base spectrum is
    Z = U Z0 U^*,   C = U C0 Theta U^*,
with Z0 diagonal in a fixed aligned basis, C0 the square-root permutation
(e_k -> e_(k (M+1)/2)) and Theta in the commutant of Z0 (phases on the simple
eigenvalues, an (r+1) x (r+1) unitary block on E_1).  If 3 does not divide M then
Z^M = 1 and Z has no eigenvalue of order 3, so the twist u = Z^(N/3) used in
bs12-sharp-pair-twist-coherent-corrections-are-bounded-below does not exist.
M = N, r = 0 is the old census class (run as a control with the same optimizer).

We minimize max(||C - A_s||, ||Z - D||) by a Schatten-p surrogate and L-BFGS and
report true operator norms of the final feasible exact pair (upper bounds on the
distance from (A_s, D) to exact pairs in U(N)).

usage: python3 census_tf.py N M s [restarts] [iters]
"""
import sys, math, os, torch

torch.set_default_dtype(torch.float64)
torch.set_num_threads(1)
SAVE = os.environ.get("CENSUS_SAVE")
BAND = int(os.environ.get("CENSUS_BAND", "3"))


def sharp_pair(N, s):
    j = torch.arange(N)
    w = torch.exp(2j * math.pi * j / N)
    D = torch.diag(w).to(torch.complex128)
    half = (N + 1) // 2
    W = torch.zeros(N, N, dtype=torch.complex128)
    W[(j * half) % N, j] = 1.0
    V = torch.zeros(N, N, dtype=torch.complex128)
    V[(j + 1) % N, j] = 1.0
    A = W @ torch.linalg.matrix_exp(1j * s * (V + V.conj().T))
    return A, D, W


def aligned_base(N, M):
    """Position j carries spectral label lab[j] in Z/M (label 0 = eigenvalue 1).
    Labels are placed in circular order so that Z0 is close to D."""
    r = N - M
    assert r >= 0 and M % 2 == 1
    # sorted target angles for positions j = 0..N-1 (angle j/N); spectrum angles
    spec = sorted([k / M for k in range(M)] + [0.0] * r)
    # rotate so that the r+1 zeros are centred at position 0
    lab_sorted = [round(a * M) % M for a in spec]
    shift = r // 2
    lab = [None] * N
    for i in range(N):
        lab[(i - shift) % N] = lab_sorted[i]
    return lab


def base_ops(N, M):
    lab = aligned_base(N, M)
    ang = torch.tensor([2 * math.pi * l / M for l in lab])
    Z0 = torch.diag(torch.exp(1j * ang)).to(torch.complex128)
    halfM = (M + 1) // 2
    # C0 e_j must be an eigenvector of Z0 with label lab[j]*halfM mod M.
    # Positions carrying each label:
    pos = {}
    for j, l in enumerate(lab):
        pos.setdefault(l, []).append(j)
    used = {l: 0 for l in pos}
    C0 = torch.zeros(N, N, dtype=torch.complex128)
    for j, l in enumerate(lab):
        t = (l * halfM) % M
        k = pos[t][used[t]]
        used[t] += 1
        C0[k, j] = 1.0
    # commutant mask of Z0
    L = torch.tensor(lab)
    mask = (L[:, None] == L[None, :]).to(torch.float64)
    Zc = C0 @ Z0 @ C0.conj().T
    assert torch.allclose(Zc, Z0 @ Z0, atol=1e-12)
    return Z0, C0, mask


def opn(X):
    return torch.linalg.matrix_norm(X, ord=2).item()


def run(N, M, s, restarts=3, iters=400, p=24, seed=0):
    A, D, W = sharp_pair(N, s)
    Z0, C0, mask = base_ops(N, M)
    g = torch.Generator().manual_seed(seed)
    best = None
    for r in range(restarts):
        # restart 0: U = 1.  Odd restarts: small dense noise.  Even restarts >= 2:
        # a banded random generator of bandwidth BAND and size ~1 (a position blur),
        # the mechanism seen in the simple-root census optima.
        if r == 0:
            Kr = torch.zeros(N, N); Ki = torch.zeros(N, N)
        elif r % 2 == 1:
            Kr = 0.3 / math.sqrt(N) * torch.randn(N, N, generator=g)
            Ki = 0.3 / math.sqrt(N) * torch.randn(N, N, generator=g)
        else:
            idx = torch.arange(N)
            dist = (idx[:, None] - idx[None, :]) % N
            dist = torch.minimum(dist, N - dist)
            band = (dist <= BAND).to(torch.float64)
            Kr = 0.5 * band * torch.randn(N, N, generator=g)
            Ki = 0.5 * band * torch.randn(N, N, generator=g)
        Kr = Kr.requires_grad_(); Ki = Ki.requires_grad_()
        Tr = torch.zeros(N, N).requires_grad_()
        Ti = torch.zeros(N, N).requires_grad_()
        params = [Kr, Ki, Tr, Ti]

        def build():
            K = torch.complex(Kr, Ki)
            U = torch.linalg.matrix_exp(K - K.conj().T)
            T = torch.complex(Tr * mask, Ti * mask)
            Th = torch.linalg.matrix_exp(T - T.conj().T)
            Z = U @ Z0 @ U.conj().T
            C = U @ C0 @ Th @ U.conj().T
            return C, Z

        for pp in (p, 2 * p):
            opt = torch.optim.LBFGS(params, lr=1, max_iter=iters, history_size=50,
                                    line_search_fn="strong_wolfe")

            def closure():
                opt.zero_grad()
                C, Z = build()
                ec = torch.linalg.eigvalsh((C - A).conj().T @ (C - A)).clamp_min(0)
                ez = torch.linalg.eigvalsh((Z - D).conj().T @ (Z - D)).clamp_min(0)
                Lf = (torch.sum(ec ** (pp / 2)) + torch.sum(ez ** (pp / 2))) ** (1 / pp)
                Lf.backward()
                return Lf

            opt.step(closure)
        with torch.no_grad():
            C, Z = build()
            dc, dz = opn(C - A), opn(Z - D)
            rel = opn(C @ Z @ C.conj().T - Z @ Z)
            uni = max(opn(C @ C.conj().T - torch.eye(N)), opn(Z @ Z.conj().T - torch.eye(N)))
        val = max(dc, dz)
        if best is None or val < best[0]:
            best = (val, dc, dz, rel, uni, r)
            if SAVE:
                import numpy as np
                np.savez(SAVE, C=C.numpy(), Z=Z.numpy(), N=N, M=M, s=s)
    return best


if __name__ == "__main__":
    N, M, s = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3])
    R = int(sys.argv[4]) if len(sys.argv) > 4 else 3
    it = int(sys.argv[5]) if len(sys.argv) > 5 else 400
    val, dc, dz, rel, uni, r = run(N, M, s, R, it)
    print(f"N={N} M={M} (3|M: {M % 3 == 0}) s={s} best max={val:.4f} "
          f"(||C-A||={dc:.4f}, ||Z-D||={dz:.4f}, rel err={rel:.1e}, unit err={uni:.1e}, restart {r})",
          flush=True)
