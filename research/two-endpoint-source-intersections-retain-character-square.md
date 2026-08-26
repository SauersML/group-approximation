---
rg: 2
id: two-endpoint-source-intersections-retain-character-square
kind: claim
title: The two endpoint source intersections retain a four-character twist square
artifacts:
  - research/two-endpoint-source-character-square-proof.md
  - experiments/endpoint_two_source_character_audit.py
distinct_from:
  endpoint-whitehead-signed-source-has-only-relative-hecke-overlap: that computes one endpoint intersection and its two-character zero-meet model; this combines both actor endpoints and all three exceptional detector classes.
  endpoint-detector-cell-retains-coboundary-gauge: that transports one complete detector cell through a three-scale endpoint braid; this proves that simultaneously using the `r=2` and `r=4` source intersections still does not fix its source frame.
  endpoint-whitehead-profile-has-maximal-gram-overlap: that leaves a regular `S_3` coboundary on six moved charts; this finds an independent finite character twist already on the two endpoint-source directions.
---

**ESTABLISHED TWO-ENDPOINT CHARACTER FENCE.**  Retain the actual signed
pair `(L_0,lambda_0)` and the endpoint-intersection subgroups

```text
K_r=L_0 intersect What_r L_0 What_r^(-1),    r in {2,4},
```

from `endpoint-whitehead-signed-source-has-only-relative-hecke-overlap`.
The exact abelianization audit gives

```text
|Hom(L_0,{+1,-1})|=256,
|Ann(K_2)|=4,                 |Ann(K_4)|=8,
|Ann(<K_2,K_4>)|=2.                              (TES1)
```

The last annihilator is nontrivial.  Let `xi_2` be the character negative
only on the displayed generator `x_24(1)` (`4 -> 2`), and let `xi_4` be
the character negative only on `x_45(1)` (`5 -> 4`).  Then

```text
xi_2|K_2=xi_2|K_4=1,
xi_4|K_4=1,                 xi_4|K_2 !=1.             (TES2)
```

Thus even imposing both endpoint intersection tables leaves the common
nontrivial twist `xi_2`.

More sharply, the four characters

```text
lambda_0,  lambda_0 xi_2,  lambda_0 xi_4,
lambda_0 xi_2 xi_4                                      (TES3)
```

form an exact endpoint square.  On their four character lines let
`What_2` flip the `xi_2` bit and let `What_4` flip the `xi_4` bit.  They
commute, as do endpoint Whiteheads on disjoint spare-coordinate pairs, and
`(TES2)` proves every required intersection relation.  If `Q_ab` is the
line indexed by `(a,b)`, then

```text
Q=Q_00,       What_2 Q What_2^(-1)=Q_10,
              What_4 Q What_4^(-1)=Q_01,              (TES4)
Q_00 Q_10=Q_00 Q_01=Q_10 Q_01=0.
```

Hence combining the `r=2` and `r=4` source intersections does not force
even one common positive fixed-frame subrange, much less two simultaneous
ones.

Adding all three exceptional detector classes does not remove this model.
For the deterministic representatives in `(MPF4)`, the exact character
table is

```text
lambda_0(g)=xi_2(g)=xi_4(g)=+1                       (TES5)
```

for every one of the three representatives.  More generally every nested
detector equation used here is a commutator equation, so multiplying an
`L_0` operator by either scalar character cancels from both sides.  Start
with any exact scoped endpoint detector/probe cell, take its four twists by
`1,xi_2,xi_4,xi_2xi_4`, and let the two endpoint Whiteheads permute the
four copies as in `(TES4)` while transporting the probe and return legs
chartwise.  All identities

```text
[g,u]=B,                  [A,B]=z                     (TES6)
```

and all signed-source intersection relations remain exact, while the four
source lines stay orthogonal.  The mark may act as `-1` on every copy, so
the fence persists on the marked source sector.

The only positive Grams supplied by this packet are the relative full
edges `What_r Q -> Q_(e_r)` in their moved frames.  Their intersections
with the fixed `Q` are zero in `(TES4)`, and all detector classes are
blind to the residual character square by `(TES5)`.  Therefore a valid
continuation must add an ordinary relation not invariant under these
character twists—equivalently, a fixed-frame mixed occurrence with a
nonzero cross Gram or proper range.  Intersecting more of the currently
named endpoint sources cannot provide it.

This is an exact scoped finite-source model, not a finite-dimensional
representation of the full Steinberg group.  No Property `(T)`, canonical
trace hypothesis, literature theorem, local computation, or Lean
compilation is used.

DERIVATION
two-endpoint-source-character-square-proof
