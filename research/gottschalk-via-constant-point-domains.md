---
rg: 2
id: gottschalk-via-constant-point-domains
kind: route
title: Restrict any decoder to the bounded-defect SFT, note that it contains a constant point, and forbid strongly post-surjective covers of constant-point domains
target: gottschalk-surjunctivity-conjecture
requires:
  - strict-pairs-give-dual-failures-on-bounded-defect-domains
  - constant-point-sft-domains-admit-no-post-surjective-covers
artifacts:
  - research/artifacts/constant-point-domain-count-2026-09-17.md
---

Let `G` be a group that is not surjunctive.
1. `G` carries a strict pair `(τ, σ)` on some `A^G`. An injective, non-surjective automaton has a decoder;
   see `gottschalk-via-proper-domain-duality`, step 1.
2. By `strict-pairs-give-dual-failures-on-bounded-defect-domains` (items 1, 2 and 5), some `X_R ⊊ A^G` is an
   SFT containing `Y = τ(A^G)`, and `σ|_{X_R} : X_R → A^G` is strongly post-surjective with lifts in `X_R`.
3. Fix `a ∈ A`. `τ(a^G)` is fixed by every shift, since `τ` is equivariant, so it is a constant configuration.
   It lies in `Y ⊆ X_R`.
4. This contradicts `constant-point-sft-domains-admit-no-post-surjective-covers` at `G`.

**Comparison with `gottschalk-via-proper-domain-duality`.**
- Both routes have one open step.
- The open step here is immune to every known kill-test: arrow and compression domains have no constant
  point. It is also proved for sofic groups in a self-contained way, by
  `proper-sft-covers-exclude-finite-orbits-and-sofic-constants`, where the other step has only an entropy
  sketch.
- The two open steps are logically incomparable (see the claim's distinct_from).
