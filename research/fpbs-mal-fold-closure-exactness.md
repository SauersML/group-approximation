---
rg: 2
id: fpbs-mal-fold-closure-exactness
kind: claim
title: For a free action of F(a,b), the join of the orbit relation of K = <a, bab^-2> with b restricted to A relates w and bw exactly on the 2-of-3 fold closure of A
distinct_from:
  fpbs-weakly-bernoulli-fold-seeds-have-density-floor: that bounds the measure of seed sets with conull closure on the Bernoulli class; this is the combinatorial exactness of the closure for every free action, which that claim explicitly leaves out.
  fpbs-mal-odometer-product-actions-have-cost-two: that uses only the easy half (closure conull implies generation); this is the converse (generation implies closure conull).
artifacts:
  - research/artifacts/fpbs-fold-bootstrap-seeding-2026-09-17.md
  - research/artifacts/fpbs-chord-unfolding-length-floor-2026-09-18.md
  - experiments/fpbs-fold-bootstrap-2026-09-17/certify.py
  - experiments/fpbs-fold-bootstrap-2026-09-17/certify_out.txt
---

**ESTABLISHED** through `fpbs-mal-fold-closure-exactness-proof`.

Let `L = F(a, b)` act freely and p.m.p. on `(X, μ)`. Let `K = <a, c>` with
`c = b a b^{-2}`. For measurable `A ⊆ X`, put `R' = R_K ∨ b|_A` and
`D = { w : w R' b w }`. Let `cl(A)` be the closure of `A` under the rule
"if two of `w, a w, b w` are in the set, add the third".

**Claim.** `D = cl(A)`. In particular `R_K ∨ b|_A = R_L` iff `cl(A)` is
conull.

**Reading.**
- The inclusion `cl(A) ⊆ D` is Lemma 1.1 of the fold artifact, and it holds
  for every action.
- The inclusion `D ⊆ cl(A)` is Theorem 1.2 there. It uses freeness, through
  Stallings folds of coset hulls in the Cayley tree.
- §4 of `fpbs-chord-unfolding-length-floor-2026-09-18.md` re-derives the
  vertex types and folding rules from the core `Γ_K`.

This is the step that turns any seed-density floor for `σ_b` into a lower
bound on relative cost. The relative-cost reading of
`fpbs-weakly-bernoulli-fold-seeds-have-density-floor` depends on it, and so
does `fpbs-mal-graphing-b-length-weighted-floor`.
