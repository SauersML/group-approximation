---
rg: 2
id: sl3-two-point-lamp-mark-is-single-rcc-scalar
kind: claim
title: The arithmetic two-point lamp mark needs only one projective relative-commutant scalar
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

For a unitary `m`, put

```text
D(m)=inf_(lambda in T)||m-lambda I||_2.
```

For every unitary tuple, phase cancellation and word telescoping give

```text
||J-I||_2
 <= ||[m_0,z]-J||_2 + ||[m_0,z]-I||_2
 <= defect_(RCS2) + 2 D(m_0).                             (RCS3)
```

Indeed compare `[m_0,z]` with the commutator of `lambda I` and `z`, which is
the identity.  Moreover

```text
D(m)^2=2-2|tr(m)|
 <=2(1-|tr(m)|^2)=2 e(m),                                 (RCS4)
```

where `e(m)=1-|tr(m)|^2`.  Consequently the single projective transfer

```text
e([c,h])
 <= K sum_(s in S_C)e([c,s])+eta(defect_A),                (RCS5)
```

with `eta(t)->0`, already collapses the marked sector.  The root-stabilizer
relators make the right side vanish, then `(RCS3)--(RCS4)` make `J` converge
to the identity.  This is exactly the involutory specialization of
`projective-commutant-transfer-for-arithmetic-pair`.  No global lamp PVM,
all-pairs additive table, or character-orbit Poincare argument is needed.

However, `trace-zero-involution-projective-transfer-equals-rcc` shows that
the involution (even trace-zero involution) restriction by itself does **not**
make the qualitative transfer easier: a `2 x 2` self-adjoint dilation turns
every ordinary relative-commutant leak into such an involutory projective
leak while retaining a fixed positive energy gap.  A weaker successful
theorem must therefore use additional native lamp data, most economically
the joint relation `[c,h c h^-1]=1` or equivalent mixed moments.

This is an **alternative** to the all-pairs checksum, not a formal consequence
of additive-module rounding.  In the exact infinite lamp module the product
`c(h c h^-1)=m_0` is a genuine nonzero lamp, so an exact all-pairs additive
table certainly does not make `(RCS4)` true.  The global-PVM route instead
uses character-orbit expansion to show that the sector on which the D8 mark
survives has vanishing mass.  The single-RCC route bypasses that spectral
argument by making `m_0` projectively scalar in finite matrices.  The scalar
phase itself is harmless because it disappears inside `[m_0,z]`.

`finite-orbital-checksum-cannot-expose-sl3-coset-module` shows why ordinary
error spreading among finitely many double-coset prototypes cannot prove
uniform all-pairs exposure: diagonal actor conjugacy never changes the double
coset of a lamp pair.  Separately, any proof of `(RCS5)` must use the genuinely
matrix-only arithmetic input--approximate correction/relative commutant
transfer--rather than a larger first-hit square function over lamp orbitals.
