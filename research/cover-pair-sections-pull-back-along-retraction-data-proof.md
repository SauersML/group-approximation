---
rg: 2
id: cover-pair-sections-pull-back-along-retraction-data-proof
kind: route
title: Compose the new section with the retraction datum; induce cosetwise for the converse; recode A^G as (A^T)^H and induce back for the finite-index relaxation
target: cover-pair-sections-pull-back-along-retraction-data
requires:
  - post-surjective-sft-covers-admit-scheduled-sections
  - cover-pair-sections-localize-to-the-symmetric-locus
  - cover-pair-sections-force-fixed-point-surjectivity
artifacts:
  - research/artifacts/scheduled-sections-of-post-surjective-covers-2026-09-17.md
---

Conventions: `(g.x)(h) = x(g^-1 h)`, so `(g'^-1.x')|_G` reads `x'` on the left coset `g'G`, and restriction to `G`
commutes with the `G`-action.

**T1.** `s = β ∘ s' ∘ ι` is continuous and `G`-equivariant, since all three maps are, and lands in `X`. Then
`F ∘ s = F ∘ β ∘ s' ∘ ι = π ∘ F' ∘ s' ∘ ι = π ∘ ι = id`.

**T2, the pair.** Let `M ⊆ G` be the memory of `F`, `f` its local rule, `P` the forbidden patterns of `X`, and
`Φ ⊆ G` the lift constant. Put `X' = {x' : (g'^-1.x')|_G ∈ X for all g' ∈ G'}`. It is the SFT at `G'` with
forbidden patterns `P`. It is proper, and it contains `b^(G')` iff `b^G ∈ X`. Let `F'` have memory `M` and rule `f`.
Then `(g'^-1.F'(x'))|_G = F((g'^-1.x')|_G)`. Let `z'` differ from `F'(x')` on a finite `Ω`. Only finitely many left
cosets meet `Ω`. On each one, lift the finite change inside `X` within `Ω_c Φ`, where `Ω_c` is the part of `Ω` in
that coset. Since `Φ ⊆ G`, the lifts stay in their cosets and do not interact. So `F'` is strongly post-surjective
with lifts in `X'` and constant `Φ`.

**T2, the datum.** Write `G' = ⊔_(t ∈ T) G t` (right cosets, `1 ∈ T`). Set:
- `ι(z)(g t) = z(g)`, which is `G`-equivariant because `G` permutes each right coset `Gt` by left multiplication;
- `π(z') = z'|_G`;
- `β(x') = x'|_G ∈ X`.

Then `π ∘ ι = id`, and `F(x'|_G) = F'(x')|_G` because `M ⊆ G`. So T1 applies. For a product with `(Y, F_Y)` over
`B`, use `ι(z) = (ι z, c^(G'))` for a letter `c ∈ B`, together with `π ∘ pr_1` and `β ∘ pr_1`. For a recoding by a
conjugacy `θ`, compose `ι` with `θ` and `π` with `θ^-1`.

**T2, the converse.** Given a section `s` of `(X, F)`, define `s'(z')(g'h) = s((g'^-1.z')|_G)(h)` for `h ∈ G`.
- *Well defined.* If `g'' = g'k` with `k ∈ G`, then `(g''^-1.z')|_G = k^-1.((g'^-1.z')|_G)`. By equivariance of `s`,
  the value at `k^-1 h` is the same.
- *Section.* `s'` is continuous and `G'`-equivariant, and each coset reading lies in `X`, so `s'(z') ∈ X'`.
  Cosetwise, `F' ∘ s' = id`.

**T3.** Write `G = ⊔_(t ∈ T) H t` with `T` finite. Then `x ↦ x̂`, `x̂(h) = (x(ht))_(t ∈ T)`, is an `H`-equivariant
homeomorphism `A^G ≅ (A^T)^H`.
- *A strict map at `H`.* An `H`-equivariant section `s` becomes a continuous `H`-equivariant self-map of
  `(A^T)^H`. By Curtis–Hedlund–Lyndon it is a cellular automaton. It is injective, since `F ∘ s = id`. It is not
  surjective, since its image lies in the closed set `X̂ ≠ (A^T)^H`. So `H` is not surjunctive.
- *Back to `G`.* Induce an injective, non-surjective automaton `τ` on `B^H` (with `B = A^T`) to `B^G`: apply `τ` on
  every left coset `gH`, as in T2. The result is a `G`-automaton that is still injective and non-surjective. So `G`
  is not surjunctive.

For the symmetric locus: `H` carries the recoded pair, whose memory set lies in `H`. Theorem S of
`cover-pair-sections-localize-to-the-symmetric-locus` at `H` therefore only involves the sets `Fix(e)` with
`e ∈ H \ {1}`. Constants are `H`-fixed, so the conclusion `D = ∅` of
`cover-pair-sections-force-fixed-point-surjectivity` (F1 at `H`) still applies.

**Dying step for the class.** Proposition C (artifact of `post-surjective-sft-covers-admit-scheduled-sections`)
says that a section of a cover pair at `G` makes `G` non-surjunctive. So if `G` is surjunctive and `(X, F)` is a CP
counterexample at `G`, then `(X, F)` has no section. By T1, no pair with a retraction datum to `(X, F)` has one
either.
