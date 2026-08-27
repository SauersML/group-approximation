---
rg: 2
id: canonical-arithmetic-swap-fold-gram-arcsine-proof
kind: route
title: Push the Haar fold spectrum through the two-projection principal-angle decomposition
target: canonical-arithmetic-swap-fold-gram-is-arcsine
requires:
  - arithmetic-double-swap-extension-is-binary-coset-wreath
artifacts:
  - research/artifacts/sl3-fold-positive-cross-gram-firewall-2026-08-23.md
---

The involution relator and functional calculus change `rho_n(s)` by `o(1)`
to `S_n`.  This changes every fixed word and normalized trace by `o(1)`.
The swap-extension normal form says

```text
v=[h,s]=hsh^(-1)s
```

has infinite order: it is the product of the two distinct free binary lamps
at `C` and `hC`.  Hence every `v^k`, `k!=0`, is nontrivial.  Canonicality and
fixed-word evaluation therefore give

```text
tr(V_n^k)->0                 for every fixed k!=0.       (ASR1)
```

The Fourier coefficients characterize Haar measure on the circle, proving
the first convergence in `(ASG2)`.

Apply the finite-dimensional two-projection decomposition to `P_n,Q_n`.
Apart from the four intersection summands, every summand is two-dimensional.
For a principal angle `theta`, the matrices on that summand have

```text
spec(V_n)={exp(2i theta),exp(-2i theta)},
spec(K_n)={0,cos(theta)^2}.                              (ASR2)
```

The intersection summands contribute only eigenvalues `+1` or `-1` to
`V_n`.  Their normalized total dimension tends to zero because Haar measure
has no atoms at those points.  Pushing Haar measure through

```text
z |-> (2+z+conjugate(z))/4=cos(theta)^2
```

gives the arcsine law on `[0,1]`; `(ASR2)` contributes one additional zero
for every generic two-dimensional block.  This proves the second convergence
in `(ASG2)`.

The arcsine first and second moments are `1/2` and `3/8`, and the generic
block occupies asymptotically all the space.  Multiplication by the one-half
corner weight gives `(ASG3)`.  Equivalently, directly for every exact pair,

```text
tr(K_n-K_n^2)
 =(1/2)||[P_n,Q_n]||_2^2
 =(1/16)(1-Re tr(V_n^2)),                                (ASR3)
```

so `(ASR1)` with `k=2` already gives the last two constants.

Finally the limiting half-arcsine measure has no atom at `1`.  Given
`epsilon_n->0`, dominate `[1-epsilon_n,1]` by `[1-epsilon,1]` for fixed
`epsilon`, apply weak convergence at its continuity boundary, and then let
`epsilon` tend to zero.  This proves `(ASG4)`.
