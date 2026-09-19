---
rg: 2
id: stw20-two-coordinate-variable-mixing-tradeoff
kind: claim
title: Variable rank-one mixing cannot halve and centralize two independent coordinate fibres
distinct_from:
  asymptotically-clustered-diagonal-ah-has-uniform-gamma: that theorem mixes eigenmaps only when their early-stage evaluations are uniformly close; this calculation proves a sharp obstruction to extending the same mixing across a separated two-coordinate fibre.
  sublinear-eigenmap-metric-entropy-implies-uniform-gamma: that theorem groups maps inside shrinking metric balls; this shows why a continuous phase choice cannot remove the positive metric diameter between independent coordinates.
  stw99-problem-xx-villadsen-algebras-uniform-gamma: this is a local no-go for pointwise trace-halving two-block constructions and does not exclude general central projections in the uniform tracial ultrapower.
artifacts:
  - research/artifacts/stw20-two-coordinate-mixing-tradeoff-audit-2026-08-30.md
---

Let `X` be compact Hausdorff, let `h` be a real-valued continuous function
with oscillation `Delta>0`, and choose `x_-,x_+` with

```text
h(x_+)-h(x_-)=Delta.
```

For the two independent coordinate representation, put

```text
D(x,y)=diag(h(x),h(y)) in M_2.
```

Let `p:X times X -> M_2` be any continuous rank-one projection field.  At
the separated fibre `z=(x_-,x_+)`, define

```text
C = ||[p(z),D(z)]||,
E = |tr_2(p(z)D(z))-(1/2)tr_2(D(z))|.
```

Then the exact identity

```text
C^2+4E^2=Delta^2/4                                      (VM1)
```

holds.  In particular, exact mixed-trace halving at `z` forces
`C=Delta/2`, while `C->0` forces `E->Delta/4`.  Hence no sequence of
continuous, fibre-dependent rank-one projections can simultaneously have
uniformly vanishing commutators with `D` and uniformly vanishing pointwise
mixed-trace-halving error.

The same statement holds with `M_2` replaced by `M_2 tensor M_r` for
half-rank projections which commute with the constant copy
`1_2 tensor M_r`: such a projection is `p tensor 1_r`, and normalized traces
reduce the calculation to `(VM1)`.

Continuity is not used in the numerical identity; it merely shows that
allowing a continuously varying mixing phase does not help.  The result does
not rule out constructions whose errors are only small after integration
against the actual limit traces.
