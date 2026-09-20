"""Commutator-to-relator ratio of shift-covariant pairs for Thompson's F.

Ansatz: a unitary on L qudit sites (local dimension q), X = a (x) 1 and Y = 1 (x) a on L+1 sites,
so Y = sigma(a) for the tensor shift.  Every word in X, Y lives on these L+1 sites, so the pair is
an honest pair in U(n), n = q^(L+1).  With e(U) = ||U - I||_2^2 = 2 - 2 Re tr_n U,

    R1 = [X Y^-1, X^-1 Y X],  R2 = [X Y^-1, X^-2 Y X^2],  c = [X, Y],
    C  = sqrt( e(c) / max(e(R1), e(R2)) ),

which is a lower bound for the fixed-dimension constant C_n(F) of
thompson-f-commutator-bound-holds-in-each-fixed-dimension (F hyperlinear iff sup_n C_n = infinity).

We minimise log max(e(R1), e(R2)) - log e(c), the max smoothed as an l^8 norm, subject to
e(c) >= tau (penalty), warm-starting support L+1 from the
support-L optimum a (x) 1, which realises the same numbers.  So the reported C is non-decreasing
in L by construction; the question is whether it keeps growing.

Usage: python3 ratio_shift.py q Lmin Lmax tau restarts iters
"""
import os
import sys
import torch

torch.set_num_threads(1)
torch.manual_seed(20260917)
DT = torch.complex128


def e(u):
    return 2.0 - 2.0 * torch.diagonal(u).sum().real / u.shape[0]


def pair(a, q):
    I = torch.eye(q, dtype=DT)
    return torch.kron(a, I), torch.kron(I, a)


def words(X, Y):
    Xi, Yi = X.conj().T, Y.conj().T
    g, gi = X @ Yi, Y @ Xi
    w1 = Xi @ Y @ X
    w2 = Xi @ w1 @ X
    r1 = g @ w1 @ gi @ w1.conj().T
    r2 = g @ w2 @ gi @ w2.conj().T
    cm = X @ Y @ Xi @ Yi
    return e(r1), e(r2), e(cm)


def unitary(h):
    return torch.linalg.matrix_exp(0.5j * (h + h.conj().T))


def optimise(h0, q, tau, iters, mu=1e3, lr=0.02):
    h = h0.clone().detach().requires_grad_(True)
    opt = torch.optim.Adam([h], lr=lr)
    sched = torch.optim.lr_scheduler.CosineAnnealingLR(opt, iters)
    for _ in range(iters):
        opt.zero_grad()
        r1, r2, cm = words(*pair(unitary(h), q))
        mx = (r1 ** 8 + r2 ** 8) ** 0.125
        loss = torch.log(mx) - torch.log(cm) + mu * torch.relu(tau - cm) ** 2
        loss.backward()
        opt.step()
        sched.step()
    with torch.no_grad():
        r1, r2, cm = words(*pair(unitary(h), q))
    return h.detach(), float(r1), float(r2), float(cm)


def main():
    q, Lmin, Lmax = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    tau = float(sys.argv[4])
    restarts, iters = int(sys.argv[5]), int(sys.argv[6])
    print(f"# ratio_shift q={q} tau={tau} restarts={restarts} iters={iters}; float search, upper bounds on D_n only")
    print("q L n     e(R1)    e(R2)    e(c)     C")
    for L in range(Lmin, Lmax + 1):
        m = q ** L
        seeds = []
        fn_prev = f"ratio_q{q}_L{L-1}_t{tau}.pt"
        if os.path.exists(fn_prev):
            hp = torch.load(fn_prev)
            seeds.append(("warm", torch.kron(hp, torch.eye(q, dtype=DT)) + 0.003 * torch.randn(m, m, dtype=DT)))
        for _ in range(restarts):
            seeds.append(("rand", torch.randn(m, m, dtype=DT)))
        best = None
        for tag, h0 in seeds:
            h, r1, r2, cm = optimise(h0, q, tau, iters)
            if cm >= 0.99 * tau:
                C = (cm / max(r1, r2)) ** 0.5
                if best is None or C > best[0]:
                    best = (C, h, r1, r2, cm, tag)
        if best is None:
            print(f"{q} {L} {q ** (L + 1)}  (constraint not met)")
            continue
        C, h, r1, r2, cm, tag = best
        torch.save(h, f"ratio_q{q}_L{L}_t{tau}.pt")
        print(f"{q} {L} {q ** (L + 1):<5} {r1:.5f}  {r2:.5f}  {cm:.4f}   {C:.4f}  {tag}")
        sys.stdout.flush()


if __name__ == "__main__":
    main()
