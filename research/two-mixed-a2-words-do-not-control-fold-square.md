---
rg: 2
id: two-mixed-a2-words-do-not-control-fold-square
kind: claim
title: The two symmetric mixed A2 words still leave the fold square free
invalidates:
  - sl3-fold-square-from-two-mixed-a2-words
artifacts:
  - research/dihedral-two-a2-fold-countermodel-proof.md
distinct_from:
  one-mixed-a2-word-does-not-control-fold-square: that M4 packet uses a nontrivial internal Pauli repair but violates the symmetric w23 chamber identity; this M2 packet satisfies both chamber identities by collapsing the two positive root slots.
  unbalanced-torus-and-swap-commutation-do-not-control-fold-square: that first diagonal packet omits both mixed closure requirements; this packet includes both.
  sl3-swap-extension-has-defect-only-fold-square-rigidity: that imposes the full arithmetic presentation, including rank-one conjugacy relations which forbid the root-collapse used here.
---

In the two-closure notation, impose all equations `(OMA1)--(OMA3)` from
`one-mixed-a2-word-does-not-control-fold-square` and also the symmetric mixed
identity

```text
W_23E_12W_23^*=[E_12,E_23]^(-1).                       (TMW1)
```

There is an exact assignment in `M_2` satisfying this entire package while,
for `V=HSH^*S`,

```text
Re tr(V^2)=-1/2,
||V^2-I||_2^2=3,
tr(QPQ-(QPQ)^2)=3/32.                                  (TMW2)
```

Thus adding the chamber mate of the first mixed `A_2` word does not control
the fold square.

The mechanism is exact and transparent: both positive root slots collapse
to the identity, both opposite-root/Weyl slots equal the swap reflection, and
the denominator is a rotation of order three.  The two torus closures are
then both the square of that rotation, so their product is the denominator.
Both mixed identities become `1=1`, but the fold remains the nontrivial
rotation square.

This is not a representation of the full lattice.  In particular it violates
the standard rank-one conjugacy equality

```text
W_12E_12W_12^*=B_21,                                   (TMW3)
```

whose two sides are respectively `I` and `S` in the packet.  Consequently
the next local seam is not a third positive-root commutator identity: it must
tie a Weyl slot back to its opposite root, or otherwise exclude the collapsed
root sector by a closed chamber relation.

DERIVATION
dihedral-two-a2-fold-countermodel-proof

