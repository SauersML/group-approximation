---
rg: 2
id: cover-pair-sections-force-fixed-point-surjectivity
kind: claim
title: A cover pair with a section maps its H-fixed points onto all H-fixed configurations, so constant-image deficiency kills every section, seed and de-colouring construction, and the free monoid carries a deficient constant-point cover pair although it is surjunctive
distinct_from:
  cover-pair-sections-localize-to-the-symmetric-locus: that shows a section exists iff some seed is exact on Sym_E; this names a necessary condition (fixed-point surjectivity, D_H empty) that no seed can meet on a deficient pair, and shows it is hereditary under morphisms of pairs.
  constant-point-sft-domains-admit-no-post-surjective-covers: that forbids constant-point cover pairs over groups; this does not decide it, but splits it into the fixed-point-surjective fragment (the only one the route uses) and the deficient fragment, and refutes its verbatim monoid analogue at a surjunctive monoid.
  proper-sft-domains-admit-no-dual-failures: that asks proper SI SFT domains to force pre-injectivity over groups; this shows its monoid analogue fails at the free monoid, so any proof must use inverses.
  proper-sft-covers-exclude-finite-orbits-and-sofic-constants: that excludes finite-orbit points on residually finite and sofic groups; this shows the same exclusion fails on the residually finite free monoid, at the absorbing zero of the Rees quotients.
  co-amenable-fixed-configurations-lie-in-injective-images: that places fixed configurations in images of injective automata; this concerns fixed points of domains of post-surjective covers and their images under sections.
artifacts:
  - research/artifacts/fixed-point-surjectivity-and-free-monoid-calibration-2026-09-18.md
  - experiments/free-monoid-cover-pair-2026-09-17/check.py
---

**ESTABLISHED (unreviewed)** by [[cover-pair-sections-force-fixed-point-surjectivity-proof]]. Everything is
elementary and self-contained.

**Setting.** `(X, F)` is a cover pair over `A^G`, as in `post-surjective-sft-covers-admit-scheduled-sections`.
For `H ≤ G`, the **deficiency** is `D_H = Fix(H) \ F(X ∩ Fix(H))`. The **constant deficiency** is
`D = A \ φ(C_X)`, where `φ(b) = f(b, ..., b)` on the constants `C_X` of `X`.

**F1 (every group).** A continuous equivariant section `s` forces `F(X ∩ Fix(H)) = Fix(H)` for every `H ≤ G`. So
`X` contains all constants and `φ` is a permutation of `A`. A seed exact at `1` on `Sym_E` already forces `D = ∅`.
- Why: `s(Fix(H)) ⊆ X ∩ Fix(H)`.

**F2 (heredity).** A deficiency pulls back along any morphism of pairs `(ρ, π)` with `π ∘ F' = F ∘ ρ` and `π` onto
`H`-fixed points. So none of the following repairs a deficiency:
- products with any cover pair;
- shears `(F(x) + ψ(y), y)`;
- restrictions to sub-SFTs;
- composites `(X ∩ F^-1X, F∘F)`;
- recodings.

**F3 (route bookkeeping).** The pairs `(X_R, σ)` that `gottschalk-via-constant-point-domains` feeds into CP have the
section `τ`, so `D_H = ∅` for all `H`. By Proposition C, the part of CP the route uses is equivalent to Gottschalk.
The deficient part is off-route.

**M (calibration).** The free monoid `M = {a,b}*` is surjunctive, cancellative and residually finite. It carries a
cover pair with a constant point: `X = {x : x(wb) = 0 ∀w} ⊊ {0,1}^M` and `F(x)(w) = x(wa)`.
- `X` is a proper, strongly irreducible SFT.
- `F` is strongly post-surjective with lifts in `X`, with `Φ = {a}`.
- `F` is onto and not pre-injective.
- The constant deficiency is `D = {1}`.

**Consequences.**
- Over `M`, the verbatim analogues of CP, PSD, the finite-orbit exclusion and `Gottschalk ⇒ CP` are all false.
- So any proof of CP, PSD, or `Gottschalk ⇒ CP` (needs 36774ad3 and 06d50d0e) must use invertibility of
  translations. On a deficient pair, every section, seed or `⟨e⟩`-coset-lift construction dies at a constant target
  `a^G` with `a ∈ D`.

**Not claimed.**
- No deficient cover pair over a group is known. One would be a counterexample to CP.
- The open question is sharp: does some (necessarily non-sofic) group carry a cover pair with `D ≠ ∅`?
