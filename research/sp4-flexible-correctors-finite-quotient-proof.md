---
rg: 2
id: sp4-flexible-correctors-finite-quotient-proof
kind: route
title: Flexible correctors are finite-image representations, so they factor through congruence quotients
target: sp4-flexible-correctors-factor-through-finite-quotients
requires:
  - sp4-fd-unitary-reps-have-finite-image
  - deligne-universal-cover-lattice-is-non-rf-kazhdan
---

Fix `Gamma = Sp_(2g)(Z)`, `g >= 2`.

**(FQ1).**  A flexible correction uses genuine representations
`pi_n : Gamma -> U(D_n)` with `D_n < infinity`.  Each `pi_n` is therefore a
finite-dimensional unitary representation of `Gamma`, so by
`sp4-fd-unitary-reps-have-finite-image` its image is finite and `ker pi_n`
has finite index.  Thus `pi_n` factors through the finite quotient
`Gamma / ker pi_n`.  By the Bass--Milnor--Serre congruence subgroup property
(cited at statement level), every finite-index subgroup of `Gamma` contains
a principal congruence subgroup `Gamma(N)`, so `ker pi_n \supseteq Gamma(N_n)`
for some `N_n` and `pi_n` factors through `Sp_(2g)(Z / N_n)`.

**(FQ2).**  ("only if")  If `Gamma` is flexibly HS-stable, then by (FQ1)
every asymptotic homomorphism has a flexible correction by congruence-
quotient representations.  ("if")  Congruence-quotient representations are
genuine representations of `Gamma`, so a flexible correction by them is a
flexible correction; if every asymptotic homomorphism has one, `Gamma` is
flexibly HS-stable by definition.  Hence the equivalence.

**(FQ3).**  Consider the scalar twisted-sector mechanism of the target node
`sp2g-z-flexibly-hs-stable`: a would-be refutation supplies asymptotically
projective models with scalar cocycles `c_n` that are non-trivial yet
asymptotically trivial.  Rounding such a model to a genuine representation
`pi_n` (as flexible stability demands) requires, in the `2`-norm limit, that
the class `[c_n]` be realised by an honest finite-dimensional unitary
representation up to the corner.  By (FQ1) that representation factors
through `Sp_(2g)(Z / N_n)`, so `[c_n]` is pulled back from the Schur
multiplier `H^2(Sp_(2g)(Z/N_n), T)`, a finite abelian group (Schur
multipliers of finite groups are finite).  The Deligne class
`delta in H^2(Gamma, Z)` of infinite order, arising from
`pi_1(Sp_(2g)(R)) = Z`, is not pulled back from any finite quotient: if it
were, its finite cyclic covers would be residually finite, contradicting
`deligne-universal-cover-lattice-is-non-rf-kazhdan`.  Hence `delta` is
invisible to the correctors, which proves the localisation claim.  QED.

## Remark (no circularity)

The route does not assume `Gamma` is stable.  (FQ1) constrains any witness;
(FQ2) is a definitional equivalence given (FQ1); (FQ3) restricts where a
refuting cocycle can live.  None asserts existence or non-existence of a
correction, so the target `sp2g-z-flexibly-hs-stable` stays OPEN.
