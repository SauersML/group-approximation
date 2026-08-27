---
rg: 2
id: regular-atlas-linearized-h-coercivity
kind: claim
title: Five atlas boundary derivatives uniformly control the H-covariance tangent energy
artifacts:
  - experiments/atlas-boundary-h-irrep-greedy.json
---

Let `B_j`, for

```text
j in {0,11,30,44,55},
```

be the five exact boundary derivative operators at the classical fold, and let
`C_1,...,C_4` be the four infinitesimal covariance operators
`I-Ad(h)` for the standard transvections generating
`H=diag(GL_3(2),1)`.

There is a constant `C_lin<infinity`, depending only on this fixed finite
packet and **not** on the external regular multiplicity `k`, such that every
tangent vector `X` in every amplified regular-`A_8` chart satisfies

```text
sum_(ell=1)^4 ||C_ell X||_2^2
 <= C_lin * sum_j ||B_j X||_2^2.                      (LIN-H)
```

Thus the exact kernel certificate contains a genuine dimension-free linear
spectral gap: any infinitesimal motion with nonzero `H` covariance pays a
quantitatively positive amount of five-word boundary energy.  The remaining
problem in `atlas-two-s3-covariance-collapse` is to globalize this fixed linear
gap through large nonlinear chart motions; it is not to find a missing tangent
direction or an unbounded-multiplicity linear constant.