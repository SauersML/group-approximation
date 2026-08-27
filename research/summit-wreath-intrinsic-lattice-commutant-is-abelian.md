---
rg: 2
id: summit-wreath-intrinsic-lattice-commutant-is-abelian
kind: claim
title: The intrinsic lattice relative commutant in the summit wreath factor is abelian and quadratically entropy-null
distinct_from:
  coset-bernoulli-ce-refutes-relative-commutant-collapse: that exhibits one lattice-central lamp unitary moved by the ambient actor; this computes the entire intrinsic relative commutant and shows that its unitary moduli are only abelian-size.
  finite-congruence-wreath-lamp-torsors-are-subquadratic-gauge: that quotients exact finite wreath representation classes by global conjugacy; this is an infinite crossed-product Fourier calculation followed by a uniform finite-dimensional abelian covering bound.
  diffuse-pin-centralizer-has-zero-quadratic-covering: that controls the generally nonabelian stabilizer of a diffuse matrix pin; this proves that the canonical source of the lattice-commutant leak is itself abelian even before pinning.
---

Let

```text
Lambda=SL_3(Z),       Gamma=SL_3(Z[1/3]),
X={-1,1}^(Gamma/Lambda),
N=L^infinity(X) rtimes Gamma=L(W_3).                    (SIC1)
```

Then

```text
L(Lambda)' cap N = L^infinity(X)^Lambda.                (SIC2)
```

In particular the intrinsic relative commutant is abelian.  It is strictly
larger than `C`: the lamp at the base coset belongs to the right side and is
moved by every actor element outside `Lambda`.

There is also a uniform finite-dimensional entropy calibration.  If
`B_d<=M_d(C)` is any abelian unital star subalgebra, then for every fixed
`0<epsilon<1`, in normalized Hilbert--Schmidt metric,

```text
K_epsilon(U(B_d)) <= (C/epsilon)^d,                     (SIC3)
limsup_d d^-2 log K_epsilon(U(B_d))=0.                  (SIC4)
```

Thus the canonical lattice-central lamp algebra cannot itself supply the
`exp(c d^2)` pinned-fiber packing sought in
`coset-wreath-microstates-carry-excess-entropy`.  Such a packing must come
from **extrinsic nonabelian growth** of the finite-matrix approximate
`Lambda`-commutants (or from inequivalent embeddings of the abelian algebra),
not from the unitary geometry of the intrinsic relative commutant.

At finite level this returns the entropy branch to the arithmetic transfer
wall.  A dimension-free `p=3` commutant-transfer modulus absorbs every
approximately `Lambda`-central unitary into the approximately
`Gamma`-central gauge, so no commutant-ratio packing survives.  Conversely,
any macroscopic nonabelian commutant quotient contains transfer enemies.
The entropy route therefore needs a quadratic multiplicity of the same
outlier phenomenon; the canonical lamp commutant provides only an abelian,
quadratically null baseline.
