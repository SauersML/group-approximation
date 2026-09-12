---
rg: 2
id: iwahori-spectral-residual-gate-has-polynomial-step
kind: claim
title: Small operator residual and a low-singular-residual bound give an explicit Iwahori contraction
distinct_from:
  iwahori-admits-neutral-quadratic-directions: that asks for universally available flat neutral directions and quadratic cancellation; this gives an explicit first-order polynomial update under two stated residual conditions and uses no moment flatness.
  iwahori-newton-closes-near-sector: that asks for a uniform normalized-HS neighborhood of the compatible locus; this assumes an operator residual bound and a low-singular-residual bound at the actual inexact pair, without claiming capture from any HS neighborhood.
  iwahori-uniform-quadratic-repair-step: that asks for a repair at every sufficiently small-defect input with controlled padding; this proves a conditional same-dimensional half-contraction and supplies no preliminary surgery satisfying its hypotheses.
artifacts:
  - research/artifacts/iwahori-mixed-surgery-and-polynomial-step-2026-09-08.md
---

At a pair `q` of exact modular vertex representations, use the explicit
admissible parameterization `Psi_q`. Put `F=IwahoriResidual o Psi_q`,
`f=F(0)`, and `L=DF(0)`. Use the Hilbert tuple norm for normalized
HS norms and the maximum tuple operator norm. Let `L*` be the real
HS adjoint on the admissible anti-Hermitian parameter space.

If both words in each of the three residual coordinates have length
at most `ell>=1`, set `C=100 ell^2`. Then `L`, `L*` have the
dimension-independent mixed bounds proved in the artifact.
Fix `0<sigma<=C` and an integer `T>=1` with
`(1-sigma^2/C^2)^T<=1/8`. Suppose

```text
e=||f||_2,
||1_([0,sigma^2))(L L*) f||_2 <= e/8,
||f||_op <= C/(2T(2^T-1)).
```

The explicit admissible parameter

```text
K=-C^(-2) L* sum_(j=0)^(T-1) (I-C^(-2)L L*)^j f
```

then satisfies

```text
||F(K)||_2 <= e/2,
||K||_2 <= (T/C)e,
||K||_op <= ((2^T-1)/C)||f||_op.
```

The output remains an exact pair of modular vertex representations in
the same dimension, and its maximum normalized-HS generator movement
is at most `(4T/C)e`.

The low spectral projection includes the kernel, so no surjectivity is
assumed. Neither the projection nor a Moore--Penrose inverse is required
to be bounded in operator norm; the actual update is a fixed-degree
polynomial. This claim assumes no sixth-moment flatness and supplies
no surgery or endpoint construction that makes its hypotheses hold for
arbitrary small-defect inputs. It establishes no flexible stability or
nonhyperlinearity conclusion on its own.
