---
rg: 2
id: agent-free-compressor-chart-edge-has-multiplicity-gauge
kind: claim
title: A full finite-chart HNN edge does not determine its multiplicity prefix
distinct_from:
  binary-schur-canonical-weights-have-half-reservoir-escape: that exhibits the stationary half-reservoir module; this isolates the exact commutant gauge which prevents identifying its retained child with a prescribed next prefix.
  balanced-schur-active-child-is-next-prefix-source: that asks for the missing incidence; this gives a sharp necessary and sufficient one-involution seam at the representation level.
---

Let a finite-dimensional simple chart algebra act as

```text
A=M_r(C) on H=C^r tensor C^m,
pi(a)=a tensor I_m.                                      (MCG1)
```

Every unitary implementing the identity chart edge has the form

```text
T=lambda I_r tensor U,   U in U(m),                      (MCG2)
```

up to a scalar. More generally, after fixing one reference implementer for an
isomorphism between two copies of `A`, every other implementer differs from it
by such a multiplicity unitary. Therefore HNN conjugacy relations on the full
finite chart, all chart character moments, and all central child weights leave
the relative position of a projection

```text
C=I_r tensor c
```

completely free inside the multiplicity space. In particular they cannot imply
that a retained Schur child equals a separately prescribed next-prefix
projection of the same trace. They give no overlap bound beyond the elementary
dimension bound `max(0,tr(C)+tr(C')-1)`. Choosing `U` realizes every admissible
intersection dimension; for the balanced half-trace branch it can rotate the
two ranges to zero overlap at exactly zero relator defect.

The weakest representation-level identity which closes this gauge is the
conjugacy of one prefix involution by the **same** edge letter. If `s,s'` are
self-adjoint involutions and

```text
T s T^*=s',                                               (MCG3)
```

then their positive spectral projections `C=(1+s)/2` and `C'=(1+s')/2`
satisfy `TCT^*=C'`. Quantitatively, for arbitrary unitary matrices,

```text
||TCT^*-C'||_2 = (1/2)||TsT^*-s'||_2.                    (MCG4)
```

Thus a presentation relation authenticating `(MCG3)`, with `s` chosen outside
the scalar chart action so that its compression is the intended prefix, is
the minimal missing seam. If the retained-child projection `R` commutes with
`C` and its transported copy commutes with `C'`, `(MCG4)` immediately gives
the desired `O(sqrt(E))` incidence after cutting by `R`.

This does not construct a perfect-compatible ordinary-group compiler for
`(MCG3)`. A global conjugacy may constrain inactive/allowed sectors, and
making the prefix involution part of the full edge subgroup may recreate the
factor-two Morita cancellation. It does show exactly why the present
chart-only edge is insufficient and reduces the active-child/source seam to
one mixed prefix conjugacy rather than another recovery of packet moments.

## Attempts

- **Central child signs.** They act as scalars on `(MCG1)` and do not reduce
  the `U(m)` freedom.
- **Complete packet characters.** These determine the `A`-module multiplicity
  `m` but contain no information about a chosen subspace of `C^m`.
- **Independent prefix edge.** A second implementer has its own commutant
  gauge; only reuse of the same edge letter in `(MCG3)` fixes the relative
  incidence.
