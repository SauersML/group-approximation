#!/usr/bin/env python3
"""Scale limit of MULTI-TYPE (shape-labelled) Markov size-chain test vectors for Thompson's F.

Extends experiments/thompson-f-markov-forest-2026-09-17/scale_limit.py (E1/E2 of
thompson-f-markov-size-chain-vectors-saturate-in-the-scale-limit).

Model.  Each tree carries a state x = (size, type h in 1..H); the type is a function of the shape (shape
classes).  The states of consecutive trees form a stationary Markov chain K.  A tree of state X is
(T0, T1) with child states (x0, x1); the shape law is sigma_X(T) = kappa(x0,x1|X) sigma_x0 sigma_x1 /
alpha(X|x0,x1), where alpha(.|x0,x1) is the fraction of child-shape pairs of states (x0,x1) whose
merged shape lies in class X (sum_X alpha <= 1) and kappa(.|X) is a probability law.  Summing
sqrt(Q(unmerged) Q(merged)) over the shapes of a part of mass alpha gives alpha sqrt(kappa/alpha):

  BC_merge = sum_X sum_{x0,x1} beta(x0,x1,X) sqrt(kappa(x0,x1|X) alpha(X|x0,x1)),
  beta = G(x0,X) S(x0,x1) Hm(x1,X),  S = sqrt K,  G = S^T diag(pi) S,  Hm = S S^T.

(With H = 1, alpha = 1 and this is E1.)  Optimising kappa given alpha:
BC_merge = sum_X sqrt(sum beta^2 alpha).

Scale limit (formal, as in E2): y = log n / log M on N bins, merge = max, a parent in bin J splits
into a small child in bin I <= J and a big child in bin J (small on the left or on the right).  With
piecewise-constant kernels and alpha constant on bins,

  cL[I,hs,hb,J,h] = G[(I,hs),(J,h)]^2 K[(I,hs),(J,hb)] Hm[(J,hb),(J,h)]^2      (small child left)
  cR[I,hs,hb,J,h] = G[(J,hb),(J,h)]^2 K[(J,hb),(I,hs)] Hm[(I,hs),(J,h)]^2      (small child right)
  C[I,J,h] = sum_{hs,hb} (cL alphaL + cR alphaR),  A = sum_{I<J} C,  d = C[J,J,h],
  B = sum_{J,h} int_0^1 sqrt(A + t d) dt,     R = (1 + B)/2.

Checks (selftest): H = 1 reproduces scale_limit.scale_B; a lumped chain (types drawn independently,
alpha = type weights) reproduces the H = 1 value; B <= 1.
"""
import os
import sys
import torch

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                '..', 'thompson-f-markov-forest-2026-09-17'))
from markov_ansatz import stationary, opt  # noqa: E402
import scale_limit  # noqa: E402

torch.set_default_dtype(torch.float64)


def sqrt_int(A, d):
    """int_0^1 sqrt(A + t d) dt, stable for d -> 0."""
    x = torch.sqrt(A + d + 1e-300)
    y = torch.sqrt(A + 1e-300)
    return (2.0 / 3.0) * (x * x + x * y + y * y) / (x + y)


def multitype_B(K, alphaL, alphaR, N, H):
    """K: (N*H, N*H) row-stochastic, state index j*H + h.  alphaL/alphaR: [I,hs,hb,J,h], sum_h <= 1."""
    pi = stationary(K)
    S = torch.sqrt(K.clamp_min(0))
    G = S.T @ (pi.unsqueeze(1) * S)
    Hm = S @ S.T
    G5 = G.reshape(N, H, N, H)          # G5[i,hi,j,hj]
    K5 = K.reshape(N, H, N, H)
    H5 = Hm.reshape(N, H, N, H)
    J = torch.arange(N)
    GJJ = G5[J, :, J, :]                # [J,hb,h]
    HJJ = H5[J, :, J, :]                # [J,hb,h]
    # cL[I,hs,hb,J,h] = G5[I,hs,J,h]^2 * K5[I,hs,J,hb] * HJJ[J,hb,h]^2
    cL = ((G5 ** 2).unsqueeze(2) * K5.permute(0, 1, 3, 2).unsqueeze(4)
          * (HJJ ** 2).permute(1, 0, 2).unsqueeze(0).unsqueeze(0))
    # cR[I,hs,hb,J,h] = GJJ[J,hb,h]^2 * K5[J,hb,I,hs] * H5[I,hs,J,h]^2
    KR = K5.permute(2, 3, 1, 0)         # [I,hs,hb,J]
    cR = ((GJJ ** 2).permute(1, 0, 2).unsqueeze(0).unsqueeze(0) * KR.unsqueeze(4)
          * (H5 ** 2).unsqueeze(2))
    C = (cL * alphaL + cR * alphaR).sum(dim=(1, 2))      # [I,J,h]
    low = torch.triu(torch.ones(N, N), diagonal=1).unsqueeze(2)   # I < J
    A = (C * low).sum(0)                                  # [J,h]
    d = C[J, J, :]                                        # [J,h]
    return sqrt_int(A, d).sum()


def unpack(z, N, H):
    nK = (N * H) ** 2
    K = torch.softmax(z[:nK].reshape(N * H, N * H), 1)
    a = z[nK:].reshape(2, N, H, H, N, H)
    al = torch.softmax(a, dim=5)
    return K, al[0], al[1]


def objective(z, N, H):
    K, aL, aR = unpack(z, N, H)
    return multitype_B(K, aL, aR, N, H)


def selftest():
    torch.manual_seed(1)
    N = 6
    K1 = torch.softmax(torch.randn(N, N), 1)
    b1 = scale_limit.scale_B(K1).item()
    ones = torch.ones(N, 1, 1, N, 1)
    bm = multitype_B(K1, ones, ones, N, 1).item()
    print("H=1: scale_B=%.15f multitype=%.15f diff=%.2e" % (b1, bm, abs(b1 - bm)))
    assert abs(b1 - bm) < 1e-12
    H = 3
    w = torch.softmax(torch.randn(H), 0)
    KL = (K1.unsqueeze(1).unsqueeze(3) * w.view(1, 1, 1, H)).expand(N, H, N, H).reshape(N * H, N * H)
    al = w.view(1, 1, 1, 1, H).expand(N, H, H, N, H)
    bl = multitype_B(KL, al, al, N, H).item()
    print("lumped H=3: %.15f diff=%.2e" % (bl, abs(bl - b1)))
    assert abs(bl - b1) < 1e-12
    for t in range(5):
        z = torch.randn((N * H) ** 2 + 2 * N * H * H * N * H) * 2
        v = objective(z, N, H).item()
        assert v <= 1 + 1e-12, v
    print("selftest ok")


def run(N, H, trials, iters, seed=0):
    torch.manual_seed(seed)
    best = (-1, None)
    for trial in range(trials):
        z0 = 0.5 * (trial + 1) * torch.randn((N * H) ** 2 + 2 * N * H * H * N * H)
        v, z = opt(lambda zz: objective(zz, N, H), z0, iters=iters)
        print("N=%d H=%d trial %d  B=%.6f  R=%.6f" % (N, H, trial, v, (1 + v) / 2), flush=True)
        if v > best[0]:
            best = (v, z)
    return best


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "test":
        selftest()
    else:
        N, H, trials, iters = (int(a) for a in sys.argv[1:5])
        v, z = run(N, H, trials, iters)
        print("BEST N=%d H=%d B=%.6f R=%.6f" % (N, H, v, (1 + v) / 2), flush=True)
        torch.save({'N': N, 'H': H, 'z': z, 'B': v},
                   os.path.join(os.path.dirname(os.path.abspath(__file__)), 'best_N%d_H%d.pt' % (N, H)))
