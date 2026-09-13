---
rg: 2
id: generators-dense-iff-zero-rokhlin-entropy-proof
kind: route
title: Small-support generators give density at zero entropy, and distance to the trivial partition bounds entropy otherwise
target: generators-dense-iff-zero-rokhlin-entropy
requires:
  - seward-small-support-relative-generators
  - seward-per-group-rokhlin-entropy-of-bernoulli-shifts
---

Notation as in the target. `φ(t) = −t log t`, and `h_2` is the binary entropy.

**Item 1, `⇒`.** Let `α` be a generating partition. Then `h^Rok_G(X) <= H(α) = d^Rok(α, {X})`. So if generators
are dense, `h^Rok_G(X) < ε` for every `ε > 0`.

**Item 1, `⇐`.** Assume `h^Rok_G(X) = 0`. Fix `β = {B_1, B_2, ...} ∈ P_H(X)` and `ε > 0`.

*Step 1: small sets carry little of `β`.* For a Borel `R` of positive measure let `µ_R` be the normalized
restriction. Then

    µ(R)·H_(µ_R)(β) = Σ_i µ(B_i ∩ R) log(µ(R)/µ(B_i ∩ R)) <= Σ_i φ(µ(B_i ∩ R)).

`φ` increases on `[0, 1/e]` and `Σ_i φ(µ(B_i)) = H(β) < ∞`. Choose `N` such that `µ(B_i) <= 1/e` for `i > N` and
`Σ_(i>N) φ(µ(B_i)) < ε/8`. Then for `µ(R) <= r <= 1/e`,

    µ(R)·H_(µ_R)(β) <= N·φ(r) + ε/8.

Choose `r_0 <= 1/e` with `N·φ(r_0) < ε/8`, so the right side is below `ε/4` whenever `µ(R) <= r_0`.

*Step 2: a generator on a small set.* Choose `0 < r <= r_0` with `h_2(r) + r log 2 < ε/4`. Since
`h^Rok_G(X) = 0 < r·log 2`, `seward-small-support-relative-generators` (Theorem 2.3, trivial `F`,
`p̄ = (1/2, 1/2)`) gives a Borel pre-partition `γ = {A_0, A_1}` with `µ(A_0) = µ(A_1) = r/2` and
`σ-alg^red_G(γ) = B(X)`. Put `R = A_0 ∪ A_1` and

    α = { B_i \ R : µ(B_i \ R) > 0 } ∪ { A_0, A_1 }.

`α` is a partition that restricts to `γ` on `R`. By Lemma 2.2, `σ-alg_G(α) ⊇ σ-alg^red_G(γ) = B(X)`, so `α`
generates.

*Step 3: the distance.*
- `α` is determined by `β` and `ρ = {X \ R, A_0, A_1}`, so `H(α | β) <= H(ρ) = h_2(r) + r log 2 < ε/4`.
- Off `R` the atom of `α` determines the atom of `β`. So
  `H(β | α) = µ(A_0)·H_(µ_(A_0))(β) + µ(A_1)·H_(µ_(A_1))(β) < ε/2`, by Step 1 with `µ(A_j) <= r_0`.
- `H(α) <= H(β) + H(α | β) < ∞`.

So `d^Rok(α, β) < ε`.

**Item 2.** By item 1 of `seward-per-group-rokhlin-entropy-of-bernoulli-shifts`, a Bernoulli shift with finite
nontrivial base `κ` has Rokhlin entropy `min(H(κ), h^Rok_sup(G))`, which is `0` iff `h^Rok_sup(G) = 0`. If
`h^Rok_sup(G) = 0`, every free ergodic action has Rokhlin entropy `0`: those with finite Rokhlin entropy by
definition of the supremum, and those with infinite Rokhlin entropy do not exist, by item 2 of the same import
together with Corollary 7.7 quoted in `research/artifacts/rokhlin-entropy-self-copy-dichotomy-2026-09-12.md`
(S6). Item 1 then gives the three equivalences. Free ergodic actions on atomless spaces satisfy the
hypotheses of item 1.

**Item 3.** Step 2 changes `β` only on `R`, with `µ(R) = r <= ε` after shrinking `r`, and uses the two labels
`A_0, A_1` there. For a finite window `W`, the pattern of `α` on `W` differs from that of `β` only on
`∪_(w in W) w·R`, of measure at most `|W|·r`.
