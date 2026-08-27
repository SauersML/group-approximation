---
rg: 2
id: leavitt-prefix-packet-pressure-certificate
kind: claim
title: The first finite Leavitt prefix packets admit a supercritical multiplicity certificate
refuted_by: finite-packet-functoriality-has-positive-regular-profile
---

**REFUTED.**  The proposed depth-one/depth-two diagram uses only finite-group
restriction, conjugacy, refinement and central isotypic-cut relations.
`finite-packet-functoriality-has-positive-regular-profile` supplies a
strictly positive compatible multiplicity vector for every irreducible type
in any such finite diagram.  Pairing that vector with `(LPC1)` gives a
strictly negative number on the left and a nonnegative number on the right.
Hence none of the requested certificates exists.

The former target was the following.  Let `R=L_(F_2)(1,2)` and let `z` be
the distinguished nonzero involutory elementary root in the binary-Leavitt
elementary group.  Use the depth-one and depth-two dual-prefix root packets,
together with their three-root Heisenberg enlargements and the fixed
elementary conjugacies between matching root positions.

Find a finite family of packet inclusions, conjugacies, central spectral
cuts, and restriction decompositions whose integer multiplicity matrix `B`
has rational dual certificates

```text
-e_pi=B^T y_pi+s_pi,
s_pi>=0,                                                  (LPC1)
```

for every packet type `pi` on which `z` acts nontrivially.

Equivalently, the nonnegative rational cone of multiplicity vectors
compatible with all selected depth-one/depth-two packet relations is
supported entirely on types on which `z` acts trivially.

Only a fixed finite packet diagram is permitted.  The certificate must list
the finite groups, their character tables, every inclusion or conjugacy map,
the resulting integer matrix `B`, and the exact rational vectors in `(LPC1)`.
Once listed, verification is finite rational arithmetic.

## Exact obstruction

Choose `D` divisible by the orders of all packet groups and place
`(D/|F|) lambda_F` at a packet group `F`.  Restriction to every subgroup is
`(D/|E|) lambda_E`; conjugacy preserves this profile; all central cuts are
realized by its actual isotypic summands.  Every type on which `z` acts
nontrivially therefore still has positive multiplicity in a zero-defect
profile.  Adding further finite prefix or Heisenberg packets of the same kind
cannot change this conclusion.

A viable certificate must constrain the intertwiner multiplicity spaces,
not merely their dimensions.  The matrix-coordinate formulation
`opnorm-leavitt-coarse-fine-return-row` asks one fixed return map to act
between designated supports on a common finite carrier.
