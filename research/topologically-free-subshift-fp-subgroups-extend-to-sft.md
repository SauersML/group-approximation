---
rg: 2
id: topologically-free-subshift-fp-subgroups-extend-to-sft
kind: claim
title: On a topologically free subshift, finitely presented subgroups of the full group extend to an SFT neighbourhood, and periodic approximations kill finitely presented infinite simple subgroups
distinct_from:
  fp-subshift-full-group-subgroups-extend-to-sft: That is the extension theorem for free subshifts; this proves it, with its simple-group corollary, under topological freeness, which allows points with nontrivial stabilizers.
  periodic-approximable-subshifts-host-no-fp-simple-group: That kills finitely presented infinite simple subgroups for free subshifts with periodic approximations; this extends item 1 there to topologically free subshifts.
artifacts:
  - research/artifacts/solve-fp-amenable-nonfree-hosts-2026-09-13.md
---

**ESTABLISHED** (direct proof: `topologically-free-subshift-sft-extension-proof`). It has not
been independently reviewed, and no novelty is claimed.

**Setting.**
- `Λ` is a finitely generated group, `A` a finite alphabet, and `X ⊆ A^Λ` a subshift with
  `(λ·x)(μ) = x(μλ)`.
- The action on `X` is **topologically free**: `Fix(λ)` has empty interior in `X` for every
  `λ ≠ e`.
- Points may have nontrivial stabilizers.

**Theorem.** Let `Γ = <g_1, ..., g_k> ≤ [[Λ ~ X]]` be finitely presented.
1. **Extension.**
   - There is a subshift of finite type `Y` with `X ⊆ Y ⊆ A^Λ`.
   - There are `hat g_i ∈ [[Λ ~ Y]]` extending the `g_i`.
   - Restriction to `X` is an isomorphism `<hat g_i> -> Γ`.
2. **Simple case.** If `Γ` is infinite and simple, then for every nonempty closed invariant
   `Z ⊆ Y`, `<hat g_i|_Z>` is trivial or isomorphic to `Γ` through the generators. Every
   `hat g_i` fixes every finite `Λ`-orbit in `Y` pointwise.
3. **Periodic approximations.** If `X` has (PA), as defined in
   `periodic-approximable-subshifts-host-no-fp-simple-group`, then `Γ` is not an infinite
   simple group.

**The one new observation.** Freeness entered the free-subshift proof only to make the formal
cocycle of a word that acts trivially on `X` identically `e`. Topological freeness already
does this: the formal cocycle is locally constant with values in stabilizers, and a nonempty
clopen set on which it equals `λ ≠ e` would lie inside `Fix(λ)`.

**Where freeness is still needed.** Theorem G (`fp-alternating-full-groups-of-free-subshifts-force-sft`)
also uses the uniform separation radius `R_1` for its rule 3-cycles. That fails at points with
short stabilizers. The artifact, Section 3, records the exact break.
