---
rg: 2
id: fpbs-fixed-price-iff-cost-lsc-at-bernoulli
kind: claim
title: A finitely generated group has fixed price exactly when cost is lower semicontinuous at the uniform Bernoulli measure along free ergodic shift measures
distinct_from:
  semicontinuous-invariants-blind-above-rokhlin-supremum: that shows a semicontinuous isomorphism invariant is monotone in base entropy and constant above the Rokhlin supremum; this takes cost, an invariant already constant on Bernoulli shifts, and shows that its lower semicontinuity at one Bernoulli point is equivalent to fixed price.
  fpbs-factor-invariance-equals-fixed-price: that is an algebraic reformulation through factor maps; this is a topological reformulation at one point of the space of shift measures, with a quantitative race form.
  fpbs-finite-alphabet-models-suffice-for-fixed-price: that reduces the test class to finite-alphabet free ergodic measures; this uses it and Seward's approximate Bernoulli models to concentrate the whole test class at the point lambda^G.
artifacts:
  - research/artifacts/fpbs-fixed-price-iff-cost-lsc-at-bernoulli-proof-attempt-2026-09-17.md
---

**OPEN.** A drafted proof is recorded as an attempt (see Attempts). It is not established because the
referee vote of lens 1 was lost; lenses 2 and 3 returned *survives*.

Let `G` be an infinite finitely generated group. For a finite set `L` with `|L| >= 2`, let
`lambda` be uniform on `L`, and let `F_G(L)` be the set of essentially free ergodic
`G`-invariant Borel probability measures on `L^G`, with the weak* topology. The following are
equivalent.

1. `G` has fixed price.
2. For every finite `L` with `|L| >= 2`, the cost map `nu -> C(nu)` on `F_G(L) ∪ {lambda^G}` is
   lower semicontinuous at `lambda^G`.
3. For every such `L`, that map is continuous at `lambda^G`.

**Upper semicontinuity is free.** On `F_G(L)`, `C(nu) <= C(lambda^G)` always holds by
Bernoulli maximality, so 2 and 3 are the same statement.

**Counterexample normal form.** If `G` fails fixed price, there are a finite `K`, a free
ergodic measure `nu_0` on `K^G` with `C(nu_0) <= C(lambda^G) - eta`, `eta > 0`, and shift
models `nu_n ∈ F_G(L)` of that one action with `|L| = |K| + 1` and `nu_n -> lambda^G`. With
`fpbs-clopen-certificate-cost-transfer`, every certificate `(Phi, l)` with
`c_l(Phi, nu_n) <= C(lambda^G) - eta/2` then satisfies the race inequality
`(M + |S|) TV_{W(Phi,l)}(nu_n, lambda^G) >= eta/2`. A counterexample is a family of cheap
certificates whose window grows faster than the models converge.

**Scope label.** Item 2 is a restatement of fixed price for finitely generated groups, not a
reduction to a weaker property. Its use is that it names one point of one compact space where
all the difficulty sits, and it blocks the whole class of window-local proofs
(`fpbs-window-local-cost-lower-bounds-fail-at-bernoulli`).

## Attempts

1. **Seward's approximate Bernoulli models put every finite-alphabet free action at `lambda^G`, and lower
   semicontinuity there gives the Bernoulli cost bound (2026-09-17).** Formerly the route
   `fpbs-fixed-price-iff-cost-lsc-at-bernoulli-proof` (requires
   [fpbs-finite-alphabet-models-suffice-for-fixed-price, seward-approximate-bernoulli-models-and-semicontinuity,
   abert-weiss-free-actions-weakly-contain-bernoulli, cost-is-constant-on-weak-equivalence-classes,
   fpbs-clopen-certificate-cost-transfer]); see
   `research/artifacts/fpbs-fixed-price-iff-cost-lsc-at-bernoulli-proof-attempt-2026-09-17.md`. Demoted on
   2026-09-17 after the referee audit: the vote of lens 1 was lost, so the full referee pass required for
   ESTABLISHED did not complete. Lens 2 (verdict 0fcd9e35) and lens 3 (verdict 3e997aca) returned *survives*,
   checking the Seward Corollary 6.1 application with trivial `K`, the Abert-Weiss plus monotonicity argument
   that makes upper semicontinuity automatic, the finite-alphabet descent, and the race inequality. No
   mathematical error has been reported. The premises `fpbs-finite-alphabet-models-suffice-for-fixed-price`
   and `fpbs-clopen-certificate-cost-transfer` were demoted for the same reason. Restore the route once a full
   referee pass survives.
