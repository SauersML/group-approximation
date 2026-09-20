"""Defect profile of shift-covariant local models of Thompson's F as the support L grows.

Ansatz (thompson-f-exact-shift-covariant-models-force-amenability): a unitary a on sites [0, L)
of the one-sided qudit chain (local dimension q), x_0 = a, x_1 = sigma(a).  Relations:

    (A)  a* sigma(a) a  = sigma^2(a)      support [0, L+2)
    (B)  a* sigma^2(a) a = sigma^3(a)     support [0, L+3)

Normalised HS norms do not change under tensoring with identities, so each quantity is computed
on its minimal support.  For fixed c we minimise dA^2 + dB^2 subject to ||[a, sigma a]||_2 >= c
(quadratic penalty, then a projection step: report only runs meeting 0.99 c).

Warm start: a_L (x) 1 is a legal model at support L+1 with the same numbers, so the profile
delta*(c, L) is non-increasing in L; each L is seeded with the previous optimum plus random restarts.

Usage: python3 shift_profile.py q Lmin Lmax restarts iters [c1,c2,...]
Best generators are saved to best_q{q}_L{L}_c{c}.pt and reused as warm starts.
"""
import sys
import torch

torch.set_num_threads(1)
torch.manual_seed(20260917)
DT = torch.complex128


def sh(a, q, L, k, n):
    """sigma^k(a) on n sites: I_{q^k} (x) a (x) I_{q^(n-L-k)}."""
    left = torch.eye(q ** k, dtype=DT)
    right = torch.eye(q ** (n - L - k), dtype=DT)
    return torch.kron(torch.kron(left, a), right)


def hs2(x):
    return (x.abs() ** 2).sum().real / x.shape[0]


def quantities(a, q, L):
    nA, nB, nC = L + 2, L + 3, L + 1
    a0, a1, a2 = sh(a, q, L, 0, nA), sh(a, q, L, 1, nA), sh(a, q, L, 2, nA)
    dA = hs2(a0.conj().T @ a1 @ a0 - a2)
    b0, b2, b3 = sh(a, q, L, 0, nB), sh(a, q, L, 2, nB), sh(a, q, L, 3, nB)
    dB = hs2(b0.conj().T @ b2 @ b0 - b3)
    c0, c1 = sh(a, q, L, 0, nC), sh(a, q, L, 1, nC)
    dC = hs2(c0 @ c1 - c1 @ c0)
    return dA, dB, dC


def unitary(h):
    m = h + h.conj().T
    return torch.linalg.matrix_exp(1j * m / 2)


def optimise(h0, q, L, c, iters, mu=1e3):
    h = h0.clone().detach().requires_grad_(True)
    opt = torch.optim.Adam([h], lr=0.03)
    sched = torch.optim.lr_scheduler.CosineAnnealingLR(opt, iters)
    for _ in range(iters):
        opt.zero_grad()
        dA, dB, dC = quantities(unitary(h), q, L)
        pen = torch.relu(c - torch.sqrt(dC + 1e-18)) ** 2
        loss = dA + dB + mu * pen
        loss.backward()
        opt.step()
        sched.step()
    with torch.no_grad():
        dA, dB, dC = quantities(unitary(h), q, L)
    return h.detach(), float(torch.sqrt(dA + dB)), float(torch.sqrt(dC))


def embed(h, q):
    """h on L sites -> h (x) 1 on L+1 sites (same unitary a (x) 1)."""
    return torch.kron(h, torch.eye(q, dtype=DT))


def main():
    q, Lmin, Lmax, restarts, iters = (int(x) for x in sys.argv[1:6])
    cs = [float(x) for x in sys.argv[6].split(",")] if len(sys.argv) > 6 else [0.1, 0.3, 0.6]
    prev = {}
    print(f"# q={q} restarts={restarts} iters={iters} Adam+cosine, penalty mu=1e3; best found, not certified")
    print("q L c     min_defect  commutator  seed")
    for L in range(Lmin, Lmax + 1):
        n = q ** L
        for c in cs:
            best = None
            seeds = []
            import os
            fn = f"best_q{q}_L{L-1}_c{c:.1f}.pt"
            if c not in prev and os.path.exists(fn):
                prev[c] = torch.load(fn)
            if c in prev:
                seeds.append(("warm", embed(prev[c], q) + 0.01 * torch.randn(n, n, dtype=DT)))
            for _ in range(restarts):
                seeds.append(("rand", torch.randn(n, n, dtype=DT)))
            for tag, h0 in seeds:
                h, d, cc = optimise(h0, q, L, c, iters)
                if cc >= 0.99 * c and (best is None or d < best[1]):
                    best = (h, d, cc, tag)
            if best is None:
                print(f"{q} {L} {c:.1f}   (constraint not met)")
            else:
                prev[c] = best[0]
                torch.save(best[0], f"best_q{q}_L{L}_c{c:.1f}.pt")
                print(f"{q} {L} {c:.1f}   {best[1]:.4f}      {best[2]:.4f}      {best[3]}")
            sys.stdout.flush()


if __name__ == "__main__":
    main()
