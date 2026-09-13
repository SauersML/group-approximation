---
rg: 2
id: simple-coefficient-crossed-products-dichotomy-proof
kind: route
title: Tarski gives an invariant trace or a paradoxical multiple, and the coinvariant lemma upgrades the multiple to proper infiniteness
target: simple-coefficient-crossed-products-dichotomy
requires: [rainone-type-semigroup-crossed-product-dichotomy, coinvariant-tarski-lemma-simple-dimension-groups]
---

Real rank zero and stable rank one give (SP), total projections, cancellation
of projections and Riesz refinement of `K_0(A)^+` (Zhang).  Stable rank one
makes `A` stably finite, so `K_0(A)^+ cap -K_0(A)^+ = 0`.  Simplicity makes
`alpha` minimal, and makes every nonzero projection full, so every nonzero
element of `K_0(A)^+` is an order unit.  Hence (R) and (U) of
`coinvariant-tarski-lemma-simple-dimension-groups` hold.  The crossed product
is simple because `alpha` is minimal and properly outer (as recorded in
Rainone, proof of Theorem 4.16).  Let `S = S(A, Gamma, alpha)`.

**Case A: `S` has a nontrivial state.**  Take `nu` with
`0 < nu(theta) < infinity` for some `theta`.  As in the proof of Rainone's
Theorem 4.21 (`(4) => (5)`) and Proposition 4.12, minimality makes `nu` finite
on all of `S`.  Composing with `K_0(A)^+ -> S` and extending gives a
`Gamma`-invariant positive homomorphism `beta: K_0(A) -> R`, which is faithful
by minimality.  Since `A` is exact with total projections, Theorem 4.13
(`(5) => (1)`) gives a `Gamma`-invariant faithful tracial state.  By
`(1) => (2) => (3)` there, the crossed product has a faithful tracial state and
is stably finite.

**Case B: `S` has no nontrivial state.**  Let `theta = [x]` be nonzero.  By
Tarski (Rainone, Theorem 4.11), `theta` is not completely non-paradoxical:
`(k+1) theta <= k theta` for some `k`.  By the coinvariant Tarski lemma,
`theta` is properly infinite.  So `S` is purely infinite, which is condition
(1) of Rainone's Theorem 4.21.  Its hypotheses hold here: unital, separable,
exact, total projections, cancellation, refinement, minimal and properly outer.
The unconditional implication `(1) => (3)` makes the crossed product purely
infinite.  That step goes through Theorem 4.16 and uses (SP), which real rank
zero provides.

**Exclusivity and the trace criterion.**  A purely infinite algebra is not
stably finite.  If `A` has an invariant tracial state (faithful, since `A` is
simple), Theorem 4.13 makes the crossed product stably finite, so Case B
cannot occur.  If the crossed product is stably finite, Case B is excluded, so
Case A holds and produces an invariant tracial state.
