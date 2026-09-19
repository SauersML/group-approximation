---
rg: 2
id: leavitt-unit-internal-virtually-free-reflections-proof
kind: route
title: Build a common wandering cell by finite-factor and cyclic prefix ping-pong
target: leavitt-unit-internal-virtually-free-reflections
requires:
  - wandering-leavitt-corner-reflection-compiler
  - leavitt-cylinder-swaps-generate-thompson-in-el
---

Put `X={0,1}^N`.  Choose a finite dyadic clopen partition consisting of

```text
D,
A_j^+, A_j^-                         (1<=j<=r),
A_(i,g)                              (1<=i<=k, 1!=g in G_i).
                                                               (VFP1)
```

Every displayed set is nonempty.  The prefix-table group on `X` is a
subgroup of `U`.

## The finite factors

For a fixed `i`, put

```text
X_(i,1)=X minus union_(1!=g in G_i) A_(i,g),
X_(i,g)=A_(i,g)                       (g!=1).             (VFP2)
```

These are `|G_i|` nonempty clopen sets partitioning `X`.  Choose prefix-table
homeomorphisms `theta_(i,g):X_(i,1)->X_(i,g)`, with `theta_(i,1)=1`.
Transport the left regular action of `G_i` across these charts: on
`X_(i,g)`, let `h in G_i` act by

```text
theta_(i,hg) theta_(i,g)^(-1).                           (VFP3)
```

The finitely many pieces combine to a prefix-table unit, and `(VFP3)` is a
faithful action of `G_i`.  If `h!=1`, it sends the identity cell `X_(i,1)`
onto `A_(i,h)`.  The cell `X_(i,1)` contains `D` and every ping-pong domain
belonging to every other factor.

## The infinite cyclic factors

For `1<=j<=r`, choose a prefix-table unit `a_j` satisfying

```text
a_j(X minus A_j^-)=A_j^+,
a_j^(-1)(X minus A_j^+)=A_j^-.                           (VFP4)
```

Because `A_j^+` and `A_j^-` are disjoint, positive powers of `a_j` send `D`
and every other factor domain into `A_j^+`, while negative powers send them
into `A_j^-`.

## Free-product ping-pong

Every nonidentity syllable from a factor in `(VFR1)` sends `D` and all domains
belonging to the other factors into a domain assigned to that syllable.
Induction along a reduced word therefore puts the image of `D` inside the
domain assigned to its outermost syllable.  It is disjoint from `D`.  The
free-product ping-pong lemma now gives an embedding

```text
Q=F_r*G_1*...*G_k<=U.                                  (VFP5)
```

It also gives the stronger wandering statement.  If `q!=q'`, then

```text
qD intersect q'D
 =q(D intersect q^(-1)q'D)=empty.                       (VFP6)
```

Let `p=st` be the idempotent of `D`, where `ts=1`.  Equation `(VFP6)` says
that the conjugates `q p q^(-1)` are pairwise orthogonal.  The
wandering-corner reflection compiler therefore embeds `(VFR2)` in `U` and
proves `(VFR5)` and `(VFR6)`.

The actor `Q` is residually finite: free groups and finite groups are
residually finite, and finite free products of residually finite groups are
residually finite.  Hence `Q` is MF.  The compiler gives `(VFR3)` and the
MF-target bijection `(VFR4)`.  The full-radical group `U` has no nontrivial
maps to any of the other listed target classes, so the same factorization
proves all remaining instances of `(VFR4)`.

Finally, a finite generating set for `U` in the identity coordinate together
with finite generating sets for the factors of `Q` generates `W_Q`.  A fixed
nonidentity involution normally generates `U`; its conjugates under `Q`
normally generate every coordinate of the restricted base.  This proves the
finite-generation and one-word radical assertions.
