---
rg: 2
id: fp-minimal-crossed-products-have-no-homoclinic-pairs
kind: claim
title: Over any finitely generated acting group, a finitely presented crossed product of an infinite minimal subshift forces the subshift to have no homoclinic pairs, so every finite pattern is determined by its shell
distinct_from:
  sft-wall-rigidity-iff-idempotent-commutator-ideal: that is the case P = Z^2, where wall certificates are the first-order obstruction for SFTs; this proves the wall obstruction over every finitely generated group and turns homoclinic pairs of minimal subshifts into walls.
  positive-entropy-sft-crossed-products-are-not-fp: that kills positive entropy over Z^2 through ergodic pigeonholing; this kills a single homoclinic pair over any acting group, amenable or not, with no entropy or measure argument.
  labbe-shift-is-wall-rigid: that verifies wall rigidity for one Z^2 shift, killing finite clusters through entropy and a rotation factor; this derives the absence of finite clusters from finite presentation alone, over any group.
  fp-crossed-products-force-sft-over-any-group: that forces finite type; this is the next necessary condition, trivial homoclinic relation, and it uses that theorem for splicing.
  fp-crossed-products-force-connected-differences: concurrent independent derivation of the same wall obstruction (landed on another lane the same day); that states it as 2n-connectivity of every difference set and derives the minimal case from it, while this states the minimal-case conclusion directly and splices a homoclinic pair into a wall by recurrence. The two overlap essentially completely on infinite minimal subshifts; that one is the more general statement, since it constrains Δ(x,y) for all pairs, not only finite ones.
artifacts:
  - research/artifacts/fp-minimal-crossed-products-homoclinic-kill-2026-09-17.md
---

**ESTABLISHED (unreviewed).** Let `P` be a finitely generated group, `A` a finite alphabet, `X ⊆ A^P`
an infinite minimal subshift and `k` a field. Suppose `LC(X,k) ⋊ P` is finitely presented. Then:
1. **No homoclinic pair.** There are no `T_1 != T_2` in `X` differing on a finite set.
2. **Unique shell filling.** Let `r` be the SFT radius of `X`. For every finite `F ⊆ P`, any two points of
   `X` that agree on the shell `N_r(F) \ F` agree on `F`.

**Wall lemma (the engine, no minimality needed).** Let `ℓ` bound the monomial lengths of a finite set of
relators in the generators `e_a`, `u_s^(±1)`. Then no `T_1, T_2 ∈ X` agree on `M` and differ somewhere in
`I` and somewhere in `O`, for a partition `P = I ⊔ M ⊔ O` with `d(I,O) > 2ℓ`.

*Why.* Take the module `k[P] ⊗ k^2` where `e_a` reads `diag(T_1, T_2)` in the basis `(w_1, w_2)` on `I ∪ M`,
and in the basis `(w_1 + w_2, w_2)` on `M ∪ O`. Each relator only sees an `ℓ`-ball, which misses `I` or
`O`, so it acts as `ρ_(T_1) ⊕ ρ_(T_2)` and vanishes. But the idempotents at a site in `I` and a site in
`O` do not commute.

**Why it matters.** Any Cantor crossed-product host of
`decidable-group-algebras-have-fp-cantor-crossed-hosts` is simple, hence minimal, so it must be
shell-determined. Every construction that stores information in locally re-colourable cells dies at
finite presentation, over every acting group. This includes decorations of a rigid base by free local
bits, and strongly irreducible minimal SFTs. The quantitative consequences are in
`fp-minimal-crossed-products-have-shell-bounded-complexity`.

DERIVATION
fp-minimal-crossed-products-have-no-homoclinic-pairs-proof
