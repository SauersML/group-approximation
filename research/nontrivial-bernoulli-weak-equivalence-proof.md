---
rg: 2
id: nontrivial-bernoulli-weak-equivalence-proof
kind: route
title: Free by independence of disjoint coordinate pairs, then Abert-Weiss Theorem 1 in both directions
target: nontrivial-bernoulli-shifts-are-weakly-equivalent
requires: []
artifacts:
  - research/artifacts/weak-invariant-blindness-for-bernoulli-rokhlin-entropy-2026-09-12.md
---

Sections 1 and 2 of the artifact.
1. For `g ≠ 1`, infinitely many disjoint pairs `{h, g^(-1) h}` carry independent coordinates, so a
   nontrivial Bernoulli shift is free.
2. Published dependency, read 2026-09-12 from https://arxiv.org/html/1103.1063v2. Abért–Weiss,
   *Bernoulli actions are weakly contained in any free action*, §1, define "Let κ be a probability
   space. The Bernoulli action κ^Γ is defined as the set of maps from Γ to κ, endowed with the product
   measure and the shift action by Γ." and state "Theorem 1: Let Γ be a countable infinite group and
   let f be a free p.m.p. action of Γ. Then f weakly contains every Bernoulli action of Γ. In
   particular, all free factors of i.i.d.-s of Γ are weakly equivalent."
3. Apply Theorem 1 in both directions; each shift is free by step 1.

This route imports Theorem 1; it does not re-derive it. Artifact Remark 2.3 derives step 3 instead
from the finitary selector `fpbs-aw-finite-pattern-input`. That node is worded for a Bernoulli
parameter, so it covers arbitrary finite bases only once widened.

**Verified 2026-09-12** by gk-vf-positive, independent re-derivation: PASS (Section 5.1 of `research/artifacts/gk-vf-positive-verification-2026-09-12.md`). Trust surface: `fpbs-aw-finite-pattern-input` is worded for a Bernoulli parameter; the lemma uses arbitrary finite bases, which Abert-Weiss cover.

**Update 2026-09-12 (gk-p-inf-cost), after verification.** Following that trust note, the dependency
is now Abért–Weiss Theorem 1 quoted verbatim, which covers every base, and `requires:` no longer names
`fpbs-aw-finite-pattern-input`. The verified selector derivation is kept as artifact Remark 2.3, with
the disjointification constant `ε/(8m)` the verifier added.
