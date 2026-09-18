---
rg: 2
id: frame-unit-symbols-can-vanish-without-a-grading
kind: claim
title: The rational symbols {λ, u} of an ungraded index-one frame unit can all vanish while [1] has infinite order and Q^x is detected in K_1, so no obstruction can come from the frame unit alone
distinct_from:
  isometric-shift-frames-over-uhf-bases-fail-the-k-budget: that kills graded index-one frames and leaves the ungraded ones open; this shows that for ungraded ones the frame unit's own symbols carry no obstruction, and moves the question to all units.
  graded-rings-with-degree-one-units-fail-the-k-budget: that is the graded dichotomy; the example here satisfies K_1 detection and has vanishing frame-unit symbols, so it admits no grading of the required kind.
  algebraic-closure-kills-rational-steinberg-symbols: that kills the rational symbols {λ, μ} through Q̄ and forces {λ, x} = 0 when Q̄ is central; this is about the symbols of the frame unit with rational λ.
artifacts:
  - research/artifacts/gq-gq-k2-q-rf-hosts.md
---

**ESTABLISHED (2026-09-18)** through `frame-unit-symbols-can-vanish-without-a-grading-proof`. Lane proof (gq-k2-q),
elementary, not independently reviewed. This settles the ungraded index-one question of
`isometric-shift-frames-over-uhf-bases-fail-the-k-budget` in the loophole direction (a), but only for the frame
unit. It does not give a finitely presented design.

## Statement

Let `B = U_n = ⊗_(k ∈ Z) M_n(Q)`, with `σ` the shift and `τ` the reflection `k ↦ −k` of tensor factors, so that
`τ σ τ^(-1) = σ^(-1)`. Let `R_1 = B[u^(±1); σ]`, the ring lamplighter of
`graded-rings-with-degree-one-units-fail-the-k-budget`.

1. **The doubled frame.** `θ(b) = τ(b)`, `θ(u) = u^(-1)` defines an automorphism of `R_1`. So
   `ρ(r) = diag(r, θ(r))` is a unital ring map `R_1 -> R = M_2(R_1)`. Put `B' = ρ(B) ≅ U_n` (matricial, unital,
   containing `Q`) and `U = ρ(u) = diag(u, u^(-1))`. Then `U` is a unit with `U^(-1) B' U = B'`: an index-one
   frame over `B'`.
2. **Its symbols vanish.** `{λ, U} = 0` in `K_2(R)` for every `λ ∈ Q^x`.
3. **The rest of the K-budget still holds.**
   - `[1_R]` has infinite order in `K_0(R)`.
   - `ker(Q^x -> K_1(R)) = {±1}`.
4. **So `R` has no grading with `U` in degree 1 and `B'` in degree 0.** Otherwise the dichotomy of
   `graded-rings-with-degree-one-units-fail-the-k-budget` would contradict items 2 and 3.
5. **The obstruction moves to another unit.** The unit `diag(u, 1)` has symbols `{λ, diag(u,1)}` generating an
   infinitely generated subgroup of `K_2(R)`, so `R` still fails the symbol budget and no `E_N(R)`, `N >= 3`, is
   finitely presented.

## Reading

- A symbol obstruction for index-one frames cannot be proved from the frame unit alone. It has to use the image of
  `K_1(Q) ⊗ K_1(R) -> K_2(R)`, the products of rational scalars with all units. Doubling moves `[u]` to `0` in `K_1`
  but leaves the class on `diag(u, 1)`.
- Heuristic (textbook Loday product, not re-read): for central `λ`, `{λ, x} = [λ]·[x]` depends only on `[x] ∈ K_1(R)`.
  So the symbols `{λ, u}` vanish exactly when `[u]` pairs to `0` with all rational classes. The example has
  `[U] = 0`.
- The live form of the K_2 half of `fp-simple-resolvent-ring-with-divisible-unit-class` for these designs is:
  the product `K_1(Q) ⋅ K_1(R)` must be finitely generated. When `Q̄ ⊆ Z(R)`, it must be `0`
  (`algebraic-closure-kills-rational-steinberg-symbols`, item 4).
- `R_1`, and so `R`, is not finitely presented: the commutation relations `[A_0, u^k A_0 u^(-k)] = 0` are infinitely many.
  The example calibrates the question. It is not a candidate host.
