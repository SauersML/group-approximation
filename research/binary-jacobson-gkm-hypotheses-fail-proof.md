---
rg: 2
id: binary-jacobson-gkm-hypotheses-fail-proof
kind: route
title: Read Theorem 1.1 and match its three base hypotheses against the infinite simple locally finite symbol kernel
target: binary-jacobson-gkm-semidirect-hypotheses-fail
requires:
  - binary-jacobson-elementary-mark-is-finite-quotient-invisible
artifacts:
  - research/artifacts/gkm-extension-theorem-vs-jacobson-kernel-2026-09-08.md
---

## The statement being tested

Gao--Kunnawalkam Elayavalli--Mj, `arXiv:2607.29571v1`, Theorem 1.1, quoted
from the v1 HTML render (fetched and read 2026-09-08):

> Let `G` be a finitely generated residually finite amenable group and `L` be
> an exact MF/PMF/PFF group.  Then `G x| L` is MF/PMF/PFF.

The archive's earlier body-read of this paper
(`research/artifacts/hyperlinear-q34-literature-2026-08-18.md`) recorded
Definition 2.6 and Theorems 1.2, 1.5 and 1.6, not Theorem 1.1.

## The input

The prerequisite supplies the symbol sequence

```text
1 -> L_J -> E -> Q_0 -> 1,
E = EL_5(J),   L_J = GL_fin(N x {1,...,5},F_2),   Q_0 = EL_5(F_2[z,z^-1]),
```

together with the two structural facts used below: `L_J` is **infinite simple
locally finite**, and `Q_0` is residually finite.  Matching this to
`G x| L` forces `L_J` into the role of the theorem's base `G`, since `L_J` is
the normal factor.

## The three hypotheses

**Amenable: satisfied.**  `L_J` is the directed union of the finite groups
`GL_n(F_2)` acting on finite subsets of the basis, so it is locally finite,
and a locally finite group is amenable (a directed union of amenable groups is
amenable; finite groups are amenable).

**Residually finite: fails.**  `L_J` is simple, so its only normal subgroups
are `1` and `L_J`, hence its only quotients are itself and the trivial group.
If `L_J` were residually finite there would be a nontrivial homomorphism to a
finite group, whose kernel is a proper normal subgroup, hence trivial, making
`L_J` itself finite.  `L_J` is infinite, so it is not residually finite.

**Finitely generated: fails.**  A finitely generated locally finite group is
finite: a finite generating set lies in a finite subgroup, which is then the
whole group.  `L_J` is infinite locally finite, so it is not finitely
generated.

Both failures use only *infinite simple locally finite*, which is what the
prerequisite establishes, so they survive any change of rank, basis or model
of the kernel.

## The semidirect requirement

`(GKM1)` is stated for `G x| L`, a split extension.  No splitting of the symbol
sequence is established in this archive.  Nothing above shows the sequence does
not split -- that is a separate and unaddressed question -- so the correct
statement is that applying `(GKM1)` needs an unproved input in addition to two
failed hypotheses.

## The far side, for completeness

`Q_0 = EL_5(F_2[z,z^-1])` is a finitely generated subgroup of
`GL_5(F_2[z,z^-1])`, hence linear, hence residually finite by Malcev and
therefore MF (`mf-positive-controls`); and finitely generated linear groups are
exact.  So the theorem's hypotheses on its second factor hold, and the mismatch
is entirely on the kernel side.  This is recorded so that the far side is not
re-checked by a later reader.

## The conditional corollary

`binary-jacobson-steinberg-head-root-is-mf-invisible` gives
`Rad_MF(E) = L_J != 1`, so `E` is not operator MF, while `(GKM1)` concludes MF
of the total group.  So no theorem with that conclusion can apply to this
extension.  That argument is only as good as the rank-weighted proof it cites,
which uses property (T) and is not machine-checked; the hypothesis check above
does not depend on it.
