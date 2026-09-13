---
rg: 2
id: induced-projective-absorption-breaks-classification-proof
kind: route
title: Dualize the absorption, identify induced duals with co-induced shifts, and add them to the Bernoulli part one by one
target: induced-projective-absorption-breaks-bernoulli-classification
requires:
  - stable-finiteness-failure-is-algebraic-bernoulli-absorption
  - coinduced-finite-subgroup-shifts-add-entropy-to-bernoulli
  - bernoulli-shifts-with-equal-base-entropy-are-isomorphic
artifacts:
  - research/artifacts/bernoulli-negative-induced-absorption-2026-09-12.md
---

Section 2 of `research/artifacts/bernoulli-negative-induced-absorption-2026-09-12.md`.

1. **Dualize.** By the duality in `stable-finiteness-algebraic-bernoulli-absorption-proof`, the module
   isomorphism becomes a measure conjugacy
   `(F_p^n)^G ≅ (F_p^n)^G × prod_i X_(Ind(Q_i))`.
2. **Induced duals are co-induced.** For `chi` in the dual of `Ind(Q) = F_p[G] ⊗_(F_p[F]) Q`, put
   `x(t)(q) = chi(t ⊗ q)`. Then `x(tf)(q) = chi(t ⊗ fq) = (f^-1 . x(t))(q)`, and the shift action matches.
   On a transversal `R` of `G/F`, `Ind(Q) = ⊕_(r in R) r ⊗ Q`, so Haar measure is the product of uniform
   measures on `X_Q = Hom(Q, F_p)`. So `X_(Ind(Q)) ≅ Coind(X_Q)` with `H(X_Q) = dim(Q) log p`.
3. **Add one summand at a time.** The Bernoulli part `(F_p^n)^G` has entropy `n log p > 0`. By Corollary D
   of `coinduced-finite-subgroup-shifts-add-entropy-to-bernoulli` (Theorem 1.1 if `|F_i| = 1`),
   `Coind(X_(Q_1)) × (F_p^n)^G` is a Bernoulli shift of base entropy `n log p + dim(Q_1) log p/|F_1|`.
   Iterating over `i` turns the right side of step 1 into `X_(n log p + rho log p)`, with `rho > 0` because
   some `Q_i != 0`.
4. **Supergroups.** Co-induce the isomorphism, as in part (d) of
   `bernoulli-entropy-counterexample-constraints`.

**Necessary conditions** (artifact Section 3), each by applying a functor to the hypothesis:
- `F_p[H] ⊗_(F_p[G]) -` for a sofic quotient `H`, using stable finiteness of `F_p[H]` (Elek–Szabó);
- the Hattori–Stallings trace, using `tr(AB) = tr(BA)` and the regular trace `dim Q_i` of an idempotent
  presenting `Q_i`.
