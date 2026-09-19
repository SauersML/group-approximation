#!/usr/bin/env python3
"""Scale limit for ORDER-2 Markov size chains (next size depends on the two previous sizes).

Same conventions as scale_limit.py.  K2[B,A,C] = P(next bin C | previous B, current A); p2 = stationary
pair law.  Merge of (k, j) into m = max; left-small split (k = s, j = m) and right-small (k = m, j = s):

  bL(s,m) = sum_{B,A,L} p2[B,A] sqrt(K2[B,A,s] K2[B,A,m] K2[A,s,m] K2[s,m,L] K2[A,m,L])
  bR(s,m) = sum_{B,A,L} p2[B,A] K2[B,A,m] sqrt(K2[A,m,s] K2[m,s,L] K2[A,m,L]) * H[s,m,L],
  H[s,m,L] = sum_C sqrt(K2[s,L,C] K2[m,L,C]),
  B = sum_J int_0^1 sqrt(sum_{I<J} c_IJ + t c_JJ) dt,  c = bL^2 + bR^2  (shape kernel optimised).
With K2[B,A,C] = K[A,C] this is exactly the order-1 formula (checked in __main__).
"""
import sys
import torch
from markov_ansatz import opt
import scale_limit

torch.set_default_dtype(torch.float64)


def stationary2(K2):
    N = K2.shape[0]
    # pair chain (b,a) -> (a,c) with prob K2[b,a,c]
    T = torch.zeros(N, N, N, N)
    idx = torch.arange(N)
    T[:, idx, idx, :] = K2.permute(0, 1, 2)  # T[b,a,a,c]
    T = T.reshape(N * N, N * N)
    A = T.T - torch.eye(N * N)
    A = torch.cat([A[:-1], torch.ones(1, N * N)], 0)
    rhs = torch.zeros(N * N)
    rhs[-1] = 1.0
    return torch.linalg.solve(A, rhs).reshape(N, N)


def scale_B2(K2):
    N = K2.shape[0]
    p2 = stationary2(K2)
    S = torch.sqrt(K2)
    # bL[s,m] = sum_{b,a,l} p2[b,a] S[b,a,s] S[b,a,m] S[a,s,m] S[s,m,l] S[a,m,l]
    X = torch.einsum('ba,bas,bam->asm', p2, S, S)            # sum over b
    Y = torch.einsum('sml,aml->asm', S, S)                    # sum over l
    bL = (X * Y * S).sum(0)                                   # S[a,s,m]; sum over a
    H = torch.einsum('slc,mlc->sml', S, S)
    # bR[s,m] = sum_{b,a,l} p2[b,a] K2[b,a,m] S[a,m,s] S[m,s,l] S[a,m,l] H[s,m,l]
    Z = torch.einsum('ba,bam->am', p2, K2)                    # = stationary pair law of (a,m)
    W = torch.einsum('msl,aml,sml->ams', S, S, H)
    bR = torch.einsum('am,ams,ams->sm', Z, S.permute(0, 1, 2), W)
    c = bL ** 2 + bR ** 2                                     # c[s,m] = c_IJ with I=s, J=m
    low = torch.triu(torch.ones(N, N), diagonal=1)
    Aj = (c * low).sum(0)
    d = torch.diagonal(c)
    return ((2.0 / 3.0) * ((Aj + d) ** 1.5 - Aj ** 1.5) / d).sum()


if __name__ == "__main__":
    torch.manual_seed(0)
    N0 = 5
    K = torch.softmax(torch.randn(N0, N0), 1)
    print("check order-1 embedding:", scale_B2(K.unsqueeze(0).repeat(N0, 1, 1)).item(),
          scale_limit.scale_B(K).item())
    for N in [int(a) for a in sys.argv[1:]] or [4, 8]:
        best = -1
        for trial in range(3):
            L0 = 0.5 * trial * torch.randn(N, N, N)
            v, L = opt(lambda z: scale_B2(torch.softmax(z, 2)), L0, iters=3000)
            best = max(best, v)
            print("N=%d trial %d  B=%.6f  R=%.6f" % (N, trial, v, (1 + v) / 2), flush=True)
        print("N=%d order-2 best B=%.6f" % (N, best), flush=True)
