---
rg: 2
id: schur-child-center-sign-flip-is-group-automorphism-proof
kind: route
title: Twist the last child generator by the marked central involution
target: schur-child-center-sign-flip-is-group-automorphism
requires:
  - raw-schur-generator-is-not-child-center
  - finite-schur-clifford-packet-flexible-hs-exactification
  - shared-overlap-controls-packet-multiplicity-vector
---

Write `q_*=q_(N+1)`. In the child presentation, `q_*` is an involution,
commutes with `J`, all selectors, and all old `q` generators, and has relations

```text
[p_i,q_*]=J^((e_t)_i).
```

Since `J` is a central involution, replacing `q_*` by `Jq_*` preserves its
square, all commuting relations, and every displayed commutator. Fixing the
generators of `A_f` therefore defines an endomorphism `theta_f` of `C_f`.
Applying it twice fixes `q_*`, so it is an involutive automorphism.

On selector sector `x`, `(RSC2)` gives

```text
Q_x=q_* product_j q_j^(v_j(x)).
```

The correction factor belongs to `A_f` and is fixed by `theta_f`. Hence
`theta_f(Q_x)=JQ_x` for every `x`; summing against the fixed central selector
idempotents proves `(SCA2)`. On `J=-1`, conjugation by the stable involution
`s` therefore interchanges the `+1` and `-1` central projections of `Q_f`.
Those projections, rather than the raw `q_*` eigenspaces, label the two
child-simple types. Thus `s` is a unitary equivalence between their isotypic
subspaces, proving exact equality of their multiplicities.

The semidirect product is finite because `C_f` is finite and `theta_f` has
order two. For an approximate table, fixed-presentation word telescoping
converts relator energy to a uniform all-pairs table defect. Flexible
finite-group exactification produces an exact `R_f` representation with
dimension-independent normalized-HS loss. Its paired multiplicities are
exactly equal by the previous paragraph. If this correction must be compared
with an independently exactified packet copy, polar alignment on the common
finite subgroup and `(OMV1)` convert the discarded Hilbert dimension into the
stated weighted type-vector error.
