---
rg: 2
id: commuting-syndrome-domination-gives-a-rounder
kind: claim
title: Commuting syndrome projectors dominated by the energy, plus exactification, are a rounder
artifacts:
  - research/artifacts/qpcp-syndrome-rounding-audit-2026-08-25.md
  - research/artifacts/qpcp-joint-syndrome-support-2026-09-07.md
distinct_from:
  common-higher-rank-context-projections-are-syndrome-cylinders: that identifies which common projections of a higher-rank context deserve the name syndrome cylinder inside the microstate atlas; this assembles an already-given commuting family plus a domination inequality into the instrument of definition (CR1).
---

**ESTABLISHED.**  Let `W : H -> H_syn tensor H_data` be an isometry and let
`B_1,...,B_m` be **mutually commuting** projectors on `H_syn` (acting as
`B_a tensor I`).  Suppose

```text
W^* ( sum_(a=1)^m B_a ) W  <=  C sum_(a=1)^m h_a                (SD)
```

and suppose that after the joint measurement of the `B_a`, with

```text
S = { a : B_a reads 1 },                                        (EX0)
```

a CPTP exactifier returns a normalized state on `H` -- the pullback along `W`
is part of the hypothesis, not an afterthought -- satisfying

```text
h_a sigma_S = 0    for every a not in S.                        (EX)
```

Then `H` has a `C`-rounder in the sense of
`combinatorial-gap-and-rounder-give-energy-gap`.

**(SD) is not a strengthening of the cost clause.**  For self-adjoint `X, Y`
one has `X <= Y` iff `Tr(X rho) <= Tr(Y rho)` for every state `rho`, and
because the `B_a` commute they have a joint projective measurement whose
outcome is a genuine classical set with

```text
E|S| = sum_a Tr(B_a W rho W^*) = Tr[ W^*(sum_a B_a)W rho ].     (SD1)
```

So (SD) *is* the cost clause quantified over all inputs, written operator
side. The present construction obtains a joint classical label from commuting
projections. However, commutativity on an unrestricted dilation is not an
extra restriction on the input measurement: every joint POVM has a dilation
with commuting single-bit flag tests, as proved in
`joint-syndrome-support-characterizes-exactifiability`.
Locality and implementation bounds for the isometry, the local energy
neighborhoods, and (EX) for that same joint measurement remain substantive.

In particular, identical marginal effects `W^* B_a W` can have opposite
exactifiability verdicts; see
`identical-flag-marginals-can-disagree-on-exactifiability`.
This does not alter the sufficiency theorem, which assumes (EX) explicitly.

**Local form.**  It suffices to have, for each port `j`,

```text
W^* B_j W <= C_0 sum_(a in N(j)) h_a,                           (SD2)
```

with every term `h_a` lying in at most `R` of the neighbourhoods `N(j)`.
Evaluating (SD2) in the input state turns it into the local charge
hypothesis of `bounded-overlap-syndrome-energy-accounting` with
`q_j = Tr(B_j W rho W^*)`, `e_r = Tr(h_r rho)`, `L = C_0`, `D = R`; that
lemma then returns (SD) with `C = C_0 R`.  No separate incidence count is
needed in this region.
