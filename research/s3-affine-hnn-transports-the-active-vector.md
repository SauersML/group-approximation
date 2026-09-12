---
rg: 2
id: s3-affine-hnn-transports-the-active-vector
kind: claim
title: An affine endpoint HNN transports the complete S3 active vector without scalarizing its union
distinct_from:
  hnn-selector-chart-transport-preserves-mark-and-types: that transports a complete elementary-abelian type vector abstractly; this identifies the three active coordinates and gives a direct normalized-HS projection estimate for their nonlinear union.
  hnn-conjugacy-cannot-return-schur-morita-multiplicity: that rules out creating a scale change by conjugacy; the common-scale theorem shows no scale change is needed for these three coordinates.
---

Let

```text
D=<J,K,b> ~= (C_2)^3,          D'=<J',K',b'> ~= (C_2)^3
```

be two endpoint charts, and adjoin one stable letter `t` carrying the three
named generators to the primed generators.  In an exact representation,

```text
t P_(epsilon,delta) t^*=P'_(epsilon,delta)               (SAH1)
```

for all four marked atoms.  Consequently

```text
t A t^*=A',                  t X t^*=X'.                 (SAH2)
```

Neither `A` nor its reflection is a group word; `(SAH2)` follows by
transporting the three commuting involutions before evaluating the fixed
Boolean polynomial.

Quantitatively, suppose the two endpoint tables have first been exactified
and put

```text
e_J=||tJt^*-J'||_2,   e_K=||tKt^*-K'||_2,
e_b=||tbt^*-b'||_2.
```

Then fixed product telescoping gives

```text
||tAt^*-A'||_2 <= e_J+(e_K+e_b)/2,                       (SAH3)
||tXt^*-X'||_2 <= (e_J+e_K+e_b)/2.                       (SAH4)
```

The weighted `L1` discrepancy of the three common-scale active
multiplicities is therefore at most a fixed multiple of
`e_J+e_K+e_b`.  The HNN relations impose no commutation between the old and
fresh context selectors, and Britton embedding preserves every nontrivial
word in the base.

This closes the affine and local-scale parts of the active return.  It does
not create strict multiplicity loss: a finite graph made only from these
chart edges still has the regular stationary flow of
`finite-packet-graph-atlases-have-a-regular-stationary-flow`.
