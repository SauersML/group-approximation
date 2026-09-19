---
rg: 2
id: two-v-not-haagerup-from-full-shift-normal-relative-t
kind: route
title: "An infinite normal relative-(T) subgroup of a subgroup of [[X]] ≤ 2V bounds every cnd function of 2V on an infinite set, so 2V is not Haagerup"
target: brin-thompson-2v-is-not-a-t-menable
requires:
  - full-shift-full-group-has-infinite-normal-relative-t-subgroup
  - full-shift-topological-full-group-embeds-in-2v
---

Suppose the two required claims hold. Then there are `Γ ≤ [[X]] ≤ 2V` and an infinite `H ⊴ Γ`
with `(Γ, H)` relative (T). Let `ψ` be any cnd function on `2V`. We show that `ψ` is bounded on
`H`. Then `ψ` is not proper, because `H` is infinite, so `2V` is not Haagerup.

1. **Quantitative projection.** Since `H ⊴ Γ`, there are, for `δ = 1/4`, a finite `Q ⊂ Γ` and
   `ε > 0` such that every unit vector `ξ` of every unitary representation of `Γ` with
   `max_{g∈Q} ‖gξ − ξ‖ ≤ ε` satisfies `‖ξ − Pξ‖ ≤ δ`. Here `P` is the projection onto the
   `H`-invariant vectors. This is Step 1 of `wobbling-normal-relative-t-locally-finite-proof`,
   which uses only normality and relative (T). In short: `P` commutes with `Γ` by normality, so a
   failure for every `(Q, ε)` gives, on the complements `(1−P)V`, a direct sum with almost
   invariant vectors and no `H`-invariant vector.
2. **Schoenberg.** For `t > 0`, `φ_t = e^{-tψ}` restricted to `Γ` is positive definite with
   `φ_t(1) = 1`. Its GNS triple `(π_t, V_t, ξ_t)` has `⟨π_t(g)ξ_t, ξ_t⟩ = e^{-tψ(g)}`, so
   `‖π_t(g)ξ_t − ξ_t‖² = 2 − 2e^{-tψ(g)}`. Take `t` small enough that this is at most `ε²` for all
   `g ∈ Q`.
3. **Bound on `H`.** Write `ξ = ξ_t = Pξ + η` with `‖η‖ ≤ 1/4`, so `‖Pξ‖² ≥ 1 − 1/16`. For
   `h ∈ H`, `π_t(h)Pξ = Pξ`. So
   `e^{-tψ(h)} = ⟨π_t(h)ξ, ξ⟩ = ‖Pξ‖² + ⟨π_t(h)η, ξ⟩ ≥ 15/16 − 1/4 > 1/2`.
   Hence `ψ(h) < (ln 2)/t` for every `h ∈ H`.

So no cnd function on `2V`, and hence on any `nV` with `n ≥ 2`, is proper. Here `2V ≤ nV`, and
the restriction of a proper cnd function to a subgroup is proper.
