---
rg: 2
id: central-d8-mark-radical-proof
kind: route
title: Amplify a surviving seed to a balanced involution and adjoin an exact Pauli partner
target: central-d8-mark-radical-equals-seed-radical
requires: []
artifacts:
  - research/artifacts/seed-radical-transfer-2026-09-16.md
---

Full proof: Section 1 of the artifact, using the standard facts F1 (tensor estimate) and F2 (diagonal
ultraproducts) of Section 0.

**If `b in Rad_hyp(G)`.** Every `Theta : P(G,b) -> U(Q)` restricts to `G`, so `Theta(b) = 1` and
`Theta(J) = [Theta(b), Theta(z)] = 1`.

**If `theta : G -> U(prod_omega M_(d_n))` has `theta(b) != 1`.**

1. `B = theta(b)` is a self-adjoint unitary with `t = tau(B) < 1`, by faithfulness of `tau`. Then `theta (+) 1` has
   seed trace `s = (1+t)/2 in [0,1)`.
2. The `k`-th tensor powers of the lifts have multiplicative defect at most `k` times the original, and seed trace
   `(tr)^k`. A diagonal choice of level `n_k` gives maps `V_k : G -> U(D_k)` with `D_k = (2d_(n_k))^k` even. Their
   defect on the first `k` group elements is `< 1/k`, `|tr V_k(b) - s^k| < 1/k`, and `||V_k(b)^2 - I||_2 < 1/k`.
3. For unimodular `lambda`, `|lambda - sgn(lambda)| <= |lambda^2 - 1|`, where `sgn(lambda) = 1` iff
   `Re lambda >= 0`. This follows from `|cos(phi/2)| >= 1/sqrt(2)` for `|phi| <= pi/2`. So `B_k = sgn(V_k(b))` is a
   self-adjoint unitary with `||V_k(b) - B_k||_2 < 1/k` and `|tr B_k| < s^k + 2/k`.
4. Flipping `r_k = D_k |tr B_k|/2` eigenvectors, an integer because `D_k` is even, gives a balanced involution
   `B'_k` with `||B_k - B'_k||_2^2 = 2|tr B_k| -> 0`. So `[B'_k] = [V_k(b)]`.
5. In an eigenbasis, `B'_k = I (x) diag(1,-1)`. With `Z_k = I (x) [[0,1],[1,0]]`, we get `Z_k^2 = I` and
   `B'_k Z_k B'_k Z_k = -I` exactly.
6. `Theta|_G = [V_k]`, `Theta(z) = [Z_k]` and `Theta(J) = -1` satisfy every relator of `(CDS1)`, so `Theta` is a
   homomorphism with `Theta(J) = -1`.
