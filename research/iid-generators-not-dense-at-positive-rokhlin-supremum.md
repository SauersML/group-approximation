---
rg: 2
id: iid-generators-not-dense-at-positive-rokhlin-supremum
kind: claim
title: On a nonamenable group with positive Rokhlin supremum, generating partitions and isomorphism joinings of Bernoulli shifts miss a neighbourhood of each i.i.d. structure carried by a small Bernoulli factor
distinct_from:
  bernoulli-classes-meager-on-central-locally-finite-hosts: that shows every Bernoulli conjugacy class is meager in the space of actions of a product host; this shows that inside one Bernoulli shift, and in its space of joinings, generating i.i.d. partitions and isomorphism joinings are not dense, on every nonamenable group with positive supremum.
  semicontinuous-invariants-blind-above-rokhlin-supremum: that shows semicontinuous invariants cannot separate Bernoulli shifts above the supremum; this shows that category arguments in the partition and joining spaces cannot produce the isomorphisms when the supremum is positive.
---

**ESTABLISHED (unreviewed)** by [[iid-generators-not-dense-at-positive-rokhlin-supremum-proof]].

**Setting.** `G` is countably infinite and nonamenable, with `s = h^Rok_sup(G) > 0` (`s = ∞` is allowed).
`(A, p)` and `(B, q)` are finite bases with `a = H(p) > 0` and `H(q) > 0`. Put `K = A × B`, `κ = p × q`,
`X = (K^G, κ^G)` with measure `µ`, and `r = min(H(κ), s)`. Let `𝒜` be the `G`-invariant σ-algebra generated
by the `A`-part of the coordinates, a Bernoulli factor with base entropy `a`. Let `(L, λ)` be a finite base
with `H(λ) > 0`.

1. **Sub-additivity bound.** For every countable generating partition `γ` of `X` and every partition
   `ξ ⊆ 𝒜`: `H(γ | ξ) ≥ H(γ | 𝒜) ≥ r − min(a, s)`.
2. **Small carriers.** Some partition `ξ ⊆ 𝒜` with labels in `L` has `G`-translates that are independent
   with distribution `λ`.
3. **Partition space.** Suppose `a < s`. Let `γ` be an `L`-labelled generating partition and
   `δ = µ(γ ≠ ξ)`, with `ξ` from item 2. Then `h_2(δ) + δ log(|L| − 1) ≥ r − a > 0`, where `h_2` is the binary
   entropy. So in the closed set `Ind_λ(X)` of `L`-labelled partitions with independent translates and
   distribution `λ`, the generating partitions are not dense.
4. **Joining space.** Let `J` be the compact space of joinings of `λ^G` and `κ^G` on `L^G × K^G`, and `ν_ξ`
   the law of `x ↦ ((g ↦ ξ(g^-1 x)), x)`. Suppose `a < min(H(λ), s)`. Then `ν_ξ` has a weak* neighbourhood
   that contains no joining in which the `L`-coordinates determine the `K`-coordinates. In particular it
   contains no isomorphism joining, and the factor maps from `L^G` onto `K^G` are not dense in `J`.

**Model tests.**
- `G = F_2`, `A = B = {0,1}` and `L = 4` points, all uniform. Item 4 is Bowen's Proposition 9.4 in
  Seward, arXiv:1804.05269v3: "the factor joinings from the Bernoulli shift (X_L,µ_L) to the equal-entropy
  Bernoulli shift (X_R,µ_R) do not form a dense set in the space of all joinings of µ_L with µ_R." That proof
  uses upper semicontinuity of Rokhlin entropy. Here sub-additivity and continuity of conditional entropy
  suffice. `ν_ξ` is ergodic, so the neighbourhood of item 4 also meets the ergodic joinings without meeting a
  factor joining.
- Amenable `G` fails the hypothesis, as it must. There an i.i.d. partition inside `𝒜` has base entropy at most
  `a`, so item 4 has no `λ` to apply to. For `Z` the residual factor theorem of Burton–Keane–Serafin (2000),
  quoted in Section 1 of arXiv:1804.05269v3, makes the factor joinings a dense `G_δ` among ergodic joinings
  when the entropies are equal. Proposition 9.4 there records that it fails for nonamenable groups.
- If `s = 0`, no `a` satisfies `0 < a < s`, and items 3 and 4 are vacuous.

**Reading for the problem.** On a group with `0 < s < ∞`, a proof of
`bernoulli-shifts-above-rokhlin-supremum-are-isomorphic` cannot be a Baire category argument over all
i.i.d. partitions of one shift, or over all joinings of two shifts. The sets such an argument would show to be
comeager are not dense. At `s = 0` the obstruction is empty; that case is posed as
`iid-generators-dense-at-zero-rokhlin-supremum`.
- By `bernoulli-shifts-with-equal-base-entropy-are-isomorphic`, every Bernoulli shift of finite base entropy
  `h` is isomorphic to one with base `A × B` for any split `h = a + H(q)`. So items 1–3 apply to every
  finite-entropy Bernoulli shift up to isomorphism.
- The space `J` depends on the chosen base, and item 4 is stated for the product base.

**Novelty (bounded check).** Sections 1, 9 and 10 of arXiv:1804.05269 and Section 1 of arXiv:1707.09573 were
read. Neither states items 1–4 beyond Bowen's `F_2` example.
