---
rg: 2
id: marked-corner-cycle-needs-no-full-mass-concentration
kind: claim
title: A central marked-corner cycle decoder needs no comparison with the unmarked forbidden mass
distinct_from:
  global-marked-type-cycle-selector-decoder: that derives a global inequality against the full shared BCS forbidden mass under GTC5; this applies the same cycle calculation inside one common central-sign corner and uses the corner-localized BCS gap instead.
  forbidden-weighted-type-carrier-coverage-is-rank-rounding: that covers the marked forbidden mass but explicitly does not compare it with the full-space mass; this proves that the comparison is unnecessary for the central-sign nonhyperlinearity endpoint.
  central-sign-bcs-energy-decoder-implies-nonhyperlinear: that is the abstract terminal criterion once all BCS corner energy is decoded; this shows how marked rank rounding plus the global cycle's GTC4 supply its forbidden-energy part.
---

**ESTABLISHED ENDPOINT REFINEMENT.**  Let `y` be the common central
involution used by every exactified context packet, and put

```text
Q=(I-y)/2.
```

Assume the marked types are exhaustive in the negative sector, so for every
context `c`,

```text
Q=sum_(lambda in Irr_-(H_c))Q_(c,lambda).              (MCN1)
```

Let `F_c` be the forbidden projection of the original shared BCS tuple and
define

```text
E_forbid^Q=sum_c tr(F_cQ).
```

Suppose the ordinary base rows control the involution, shared-context, and
corner-reduction part of the BCS energy, and suppose the global cycle
actuator supplies `(GTC4)` for the analytic carriers obtained by trimming
`F_cQ_(c,lambda)`.

Then canonical matrix microstates of a group with nontrivial central mark
`y` have a fixed positive relator-energy floor.  No estimate comparing
`E_forbid^Q` with the forbidden mass on `I-Q` is required.

Indeed, `forbidden-weighted-type-carrier-coverage-is-rank-rounding` gives

```text
sum_(c,lambda)tr(P_(c,lambda))
 >=E_forbid^Q-o(1).                                    (MCN2)
```

The cyclic selector trace calculation and `(GTC4)` therefore make the
ordinary actuator words dominate `E_forbid^Q` with a fixed positive
coefficient.  On the other hand,
`corner-localized-non-ce-bcs-energy-gap`, applied to the same shared tuple
and the reducing projection `Q`, gives

```text
E_base^Q+E_forbid^Q>=beta_B^corner tr(Q).              (MCN3)
```

The base term is already paid by ordinary rows; if it is small, `(MCN3)`
forces marked forbidden mass, which `(MCN2)` and the cycle pay.  Canonical
microstates satisfy `tr(Q)->1/2`, so either case contradicts vanishing
presentation defect.

The common-central-sign hypothesis is load-bearing.  If the context marks
are unrelated analytic projections, `(MCN3)` cannot be applied to all of
them as one corner.  Likewise this does not prove `(GTC4)`: it removes only
the previously stated comparison with the **unmarked** forbidden mass.
