---
rg: 2
id: leavitt-nonsoficity-does-not-close-macroscopic-mf-branch
kind: claim
title: Leavitt nonsoficity does not close the macroscopic MF branch without a new shadow-to-action converter
distinct_from:
  simple-torsion-groups-have-a-macroscopic-mf-dichotomy: that theorem converts a surviving norm-corona torsion mark into a faithful operator-norm asymptotic model with Hilbert--Schmidt separation; this audit identifies why the existing nonsofic endpoint cannot consume that model.
  openai-leavitt-unit-nonsofic: that is the established nonsoficity theorem; this records the exact Property-(T) dependency in both of its available derivations and the missing implication needed to combine it with MF reblocking.
artifacts:
  - research/property-t-free-leavitt-full-mf-radical.md
  - research/opnorm-packet-rank-does-not-yield-action-shadow.md
---

**ESTABLISHED AUDIT.**  Let

```text
Delta=St_20(L_(F_2)(1,2))
```

and let `z=x_13(s_1t_1)` be the normally generating involution used by
`property-t-free-leavitt-full-mf-radical`.  If a norm-matrix-corona
homomorphism sees `z`, then
`torsion-normal-generator-has-full-support-corona-core` and simplicity
reblock it to a faithful operator-norm asymptotic representation which is
pointwise separating in normalized Hilbert--Schmidt norm.  Thus the surviving
MF branch is a faithful **hyperlinear shadow** with additional operator-norm
multiplicativity.

This does not contradict the established nonsoficity of the binary Leavitt
unit group.  The missing implication would be

```text
faithful opnorm-asymptotic + HS-separated unitary model
   => sofic approximation.                              (LNS1)
```

No such converter is established.  Forgetting the operator-norm information
leaves precisely a hyperlinear model, and hyperlinear does not presently imply
sofic in this development.  Conversely, the two established derivations of
`openai-leavitt-unit-nonsofic` cannot be reused under the present restriction:

1. `openai-expander-matching-criterion` obtains the expanding components from
   Property `(T)` of the Leavitt elementary actor/core;
2. `one-sided-compression-nonsofic-criterion` uses the same Kazhdan expander
   decomposition in its kernel-checked implementation.

Therefore the composition

```text
MF visibility -> macroscopic HS visibility -> Leavitt nonsoficity
```

has one exact missing arrow: a Property-`(T)`-free conversion of this specific
operator-norm/HS shadow into the finite action charts consumed by the Thompson
`V` non-LEF witness.  Bare nonsoficity is not a terminal for the current MF
proof.

This audit rules out only the direct composition.  A Leavitt-specific
shadow-to-action converter exploiting the simultaneous operator-norm defect
still remains a live route and would bypass the coefficient-module decoder.
The natural implementation by fixed finite-packet exactification and
projection-rank rigidity is now fenced by
`opnorm-packet-rank-does-not-yield-action-shadow`: parabolic normalizers give
only the exact finite-actor countermodel, while the opposite roots needed to
read Leavitt multiplication do not act on that packet's atom set.  Any live
converter must add a common mixed-root atom algebra or a coefficient-sensitive
moving-occurrence lock; it cannot be obtained from the current `<1` rank
threshold alone.
