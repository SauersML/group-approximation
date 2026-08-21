---
rg: 2
id: sl3-two-point-lamp-mark-is-single-rcc-scalar
kind: claim
title: The arithmetic two-point lamp mark is already the single relative-commutant scalar
distinct_from:
  sl3-codense-coset-lamp-recursive-host: that constructs the full recursive lamp group and proves exact finite-dimensional invisibility; this identifies the strictly smaller normalized-HS scalar sufficient to collapse its mark.
  infinite-character-actor-word-energy-interface: that asks for the full character-orbit Dirichlet energy; this shows that the arithmetic two-point seed needs only one root-to-h commutator estimate.
  projective-trace-square-transfer-for-sl3-pair: that asks for projective trace-square transfer for arbitrary unitaries; this records the ordinary involutory specialization consumed by the D8 lamp seed.
---

ESTABLISHED as a reduction.

Let

```text
C=SL_3(Z) < A=SL_3(Z[1/2]),
h=diag(2,1,1/2),
```

and let `c` be the involution at the base coset.  The two-point lamp used in
the arithmetic host is

```text
m_0=c (h c h^-1)=[c,h].                                  (RCS1)
```

Adjoin involutions `z,J`, make `J` central, and impose

```text
[m_0,z]=J.                                                (RCS2)
```

For every unitary tuple, word telescoping gives

```text
||J-I||_2
 <= ||[m_0,z]-J||_2 + ||[m_0,z]-I||_2
 <= defect_(RCS2) + 2 ||m_0-I||_2.                        (RCS3)
```

Consequently the following single finite-matrix estimate already collapses
the marked sector:

```text
||[c,h]-I||_2
 <= omega(delta_A + sum_(s in S_C)||[c,s]-I||_2),          (RCS4)
```

with `omega(t)->0`, allowing the fixed canonical trace side tests required
by the arithmetic presentation.  No global lamp PVM, all-pairs additive
table, or character-orbit Poincare argument is then needed.

This is an **alternative** to the all-pairs checksum, not a formal consequence
of additive-module rounding.  In the exact infinite lamp module the product
`c(h c h^-1)=m_0` is a genuine nonzero lamp, so an exact all-pairs additive
table certainly does not make `(RCS4)` true.  The global-PVM route instead
uses character-orbit expansion to show that the sector on which the D8 mark
survives has vanishing mass.  The single-RCC route bypasses that spectral
argument by killing `m_0` directly in finite matrices.

`finite-orbital-checksum-cannot-expose-sl3-coset-module` shows why ordinary
error spreading among finitely many double-coset prototypes cannot prove
uniform all-pairs exposure: diagonal actor conjugacy never changes the double
coset of a lamp pair.  Separately, any proof of `(RCS4)` must use the genuinely
matrix-only arithmetic input--approximate correction/relative commutant
transfer--rather than a larger first-hit square function over lamp orbitals.
