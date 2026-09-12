---
rg: 2
id: atlas-square-root-collision-forces-linear-core-rank
kind: claim
title: Collision forces linear row rank in the square-root two-matrix frame
refuted_by: atlas-square-root-collision-constant-term-is-zero
distinct_from:
  atlas-square-root-bridge-two-matrix-rank-reduction: that defines all thirteen residual polynomials and reduces a countermodel to their normalized ranks; this proves the first unconditional rank-density inequality for one of those polynomials.
  atlas-19243-relation-forces-s3-distance: that gives a Hilbert-Schmidt distance wall from an S3 commutant; this is a binary linear-rank inequality on the unipotent two-matrix chart.
  atlas-a4-19243-classical-collapse: that proves collision is nonidentity on every classical packet alignment; this uses only its nonidentity at the identity alignment to obtain a quantitative amplified rank bound.
---

REFUTED by `atlas-square-root-collision-constant-term-is-zero`.  The claimed
constant term is zero, not nonzero.  At the literal identity frame the four
second-chart collision letters generate an `S3`, their product is one, and
they all commute with the repeated first-chart involution.  Hence collision
evaluates to one.  Classical packet-collapse does not say otherwise: the
identity frame fails the packet, rather than collision.

The invalid statement was as follows.  On the square-root frame put

```text
A=E13 tensor X+E14 tensor Y,
rho=rank A=rank [X Y].                                (SCR1)
```

Let `P_c(X,Y)` be the collision polynomial from
`atlas-square-root-bridge-two-matrix-rank-reduction`.  If `Q` is the value
of collision at the identity alignment and

```text
c=rank_(F2)(Q-I_4),
```

then `c>=1` and

```text
rank P_c(X,Y) >= c s-8 rho >= s-8 rank[X Y].         (SCR2)
```

Consequently every sequence with `rank P_c(X_s,Y_s)=o(s)` satisfies

```text
liminf rank[X_s Y_s]/s >= c/8 >= 1/8.                (SCR3)
```

Thus the collision equation rules out sparse or sublinear-rank cores in the
growing-width outer-product construction.  A countermodel on this frame
must already place positive density in the unbridged `X,Y` chart before the
rank-one cyclic bridge is added.  This does not yet contradict matrix
generation or the twelve packet equations; it is the first exact
relation-specific density constraint on the surviving two-matrix system.

### Proof

At `X=Y=0` the two charts are identically aligned.  This alignment satisfies
the packet and q14, but collision is nonidentity by
`atlas-a4-19243-classical-collapse`; hence `c>=1`.  Amplification gives

```text
rank P_c(0,0)=rank((Q-I_4) tensor I_s)=cs.            (SCR4)
```

Changing from the identity chart to `I+A` changes it and its inverse by
rank `rho`.  Each conjugated second-chart syllable therefore changes by
rank at most `2rho`.  Collision has four second-chart syllables, so word
telescoping gives

```text
rank(P_c(X,Y)-P_c(0,0)) <= 8rho.                     (SCR5)
```

Now `rank B>=rank C-rank(B-C)` proves `(SCR2)`.  Finally, `A` maps the
third and fourth chart coordinates to the first by `X` and `Y`, so its rank
is exactly the rank of the horizontal concatenation `[X Y]`.
