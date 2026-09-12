---
rg: 2
id: sylvester-rank-functions-on-ternary-leavitt-units-kill-minus-one
kind: claim
title: Every Sylvester rank function on the ternary Leavitt unit group algebra kills one minus the central involution
refuted_by:
  - ternary-leavitt-units-have-a-nontrivial-char-three-rank-model
distinct_from:
  sylvester-rank-functions-on-leavitt-units-kill-two-root-defect: that is the binary statement over F_2, where there is no central involution and the defect is the two-root product; this is the ternary statement over F_3 about 1 - [z]
  ternary-leavitt-units-have-a-nontrivial-char-three-rank-model: that asks for a matricial rank model and refutes this; this is the abstract No branch, stronger than triviality of matricial models
  ternary-anti-central-unit-class-is-nonpositive: that is the counterexample, failure of the rank condition on S_-; this is only absence of Sylvester rank functions on S_-, which that implies, and they coincide exactly when ternary-anti-central-states-give-sylvester-rank-functions holds
artifacts:
  - research/artifacts/strategist-neg-counterexample-plans-2026-09-12.md
  - research/artifacts/ternary-leavitt-char-three-rank-model-gate-2026-09-12.md
---

**OPEN.** Let `G = L_(F_3)(1,2)^x`, `z = -1` and `S_- = eps_- F_3[G]` with `eps_- = (1 - [z])/2`.
Every Sylvester matrix rank function on `F_3[G]` has `rk(1 - [z]) = 0`.

**Equivalent forms** (artifact Section 4.4).
- `S_-` has no Sylvester matrix rank function `N` with `N(eps_-) = 1`.
  - A rank function with `rk(eps_-) = t > 0` gives `N(X) = rk(eps_- X)/t` on `S_-`.
  - Conversely `rk(X) = N(eps_- X)` extends a normalized `N` on `S_-`, because `eps_-` is central.
- `G` has no anti-central model in an abstract `F_3`-rank algebra. In one direction this is Corollary 7.2
  of the `w3-gate-char3` artifact (`S_-/ker N` is such a model). In the other, a model pulls back along
  `F_3[G] -> B`.

**What it gives and what gives it.**
- **It gives the matrix "No" branch.** It implies that every characteristic-three matrix rank model of `G`
  is trivial, so `ternary-leavitt-units-have-a-nontrivial-char-three-rank-model` fails. A nontrivial
  matrix model moves `z` and pulls back to `rk(1 - [z]) > 0`.
- **It follows from the counterexample.** `ternary-anti-central-unit-class-is-nonpositive` implies it, and
  so does the corner equation: no state means no rank function.
- **With (U1) it is the counterexample.** Together with `ternary-anti-central-states-give-sylvester-rank-functions`
  it gives `ternary-anti-central-unit-class-is-nonpositive`, through the route
  `ternary-counterexample-from-rank-kill-and-state-realization`.

*Verification by `w3-vf-linear` (2026-09-12), Section 25 of
`research/artifacts/w3-vf-linear-verification-2026-09-12.md` (1eec8d6307): PASS on both equivalences.
The claim itself stays OPEN.*
- *Normalization and extension: `X -> eps_- X` is a unital ring map because `eps_-` is central, and
  `1 - [z] = 2 eps_-` with `2` a unit.*
- *Abstract models: a model with `sigma(z) = -1` pulls back to a Sylvester function with value 1 on
  `1 - [z]`; the converse is Corollary 7.2.*

**Scope warning.** The landed characteristic-two triviality nodes (matrix-unit, unipotent-valued,
flag-preserving) and the hard R4 mechanisms are matricial, in characteristic two. None of them is
evidence here until it has been scope-checked for abstract rank algebras in characteristic three.

## Attempts

- 2026-09-12 `w3-strategist-neg`: opened after `w3-gate-char3` showed that the gate equivalences, the
  corner kill and the Haar law hold for abstract rank algebras (its artifact, Section 7).
