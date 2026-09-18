---
rg: 2
id: deligne-commuting-parabolic-diagonal-singularity-proof
kind: route
title: Proof that Deligne normal forms put a Cantor set of singular points on every power of a generator commuting with a disjoint parabolic
target: deligne-forms-are-singular-on-commuting-parabolic-diagonals
requires:
  - artin-groups-mod-central-garside-power-are-continuous-automatic
  - prefix-replacement-actions-recode-into-germ-extensions-of-v
artifacts:
  - research/artifacts/gq-bh-bh-free-51-garside-and-mosher-thinness.md
---

Notation as in the claim. Write `P = A_{s,t}` and `I = {s, t, u}`.

## 0. Garside facts used (recalled, not re-derived)

Sources: Deligne 1972; Brieskorn--Saito 1972; Charney 1992; BBCMP §2.3.

- **(G1) Simples.** Simple elements are the positive lifts of the Coxeter group `W`.
  - `S(x)` and `F(x)` are the left and right descent sets.
  - For simples `x, y`: `pref(xy) = x` if and only if `S(y) ⊆ F(x)` (Charney 1992).
  - A word `x_1 ⋯ x_n` of simples with `x_i → x_{i+1}` for all `i`, containing no `Δ`, is the
    left-greedy normal form of its product.
- **(G2) Parabolics.** For `J ⊆ S`, the simples lying in `A_J^+` are the simples of `A_J`, and
  left-greedy normal forms of elements of `A_J^+` agree in `A_J` and `A`.
  - Since `u` commutes with `s, t`, we have `W_I = W_P × ⟨u⟩`.
  - So the simples of `A_I` are `x u^δ` with `x` simple in `P` and `δ ∈ {0,1}`.
  - `S(xu) = S(x) ∪ {u}` and `F(xu) = F(x) ∪ {u}`.
- **(G3) Dihedral branching.** `m_{st} ≥ 3`. So after a proper simple `x` of `P` ending in `s`,
  both `s` and `st` are admissible next letters with starting set `{s}`.
  - So the infinite chains `x` with `S(x_1) = {s}` form a Cantor set.
  - The chains that are not eventually periodic are uncountable and dense in it.

## 1. Lockstep (item 1)

Let `x_1 ⋯ x_n` be the `P`-normal form of `p` and let `m ≤ n`.
- `(x_i u) → (x_{i+1} u)`: `S(x_{i+1}) ∪ {u} ⊆ F(x_i) ∪ {u}`.
- `(x_m u) → x_{m+1}`: `S(x_{m+1}) ⊆ F(x_m)`.
- The product is `p u^m`, since `u` commutes with `P`, and no letter is `Δ`.

So by (G1) the word is the normal form, with `j = 0` in BBCMP's language and `p = 0` in `L̄`.
Hence:
- `ξ_x = lim_n NF(x_1 ⋯ x_n u^n) ∈ ∂L`;
- `ζ_{x,k} := (x_1u) ⋯ (x_ku) x_{k+1} x_{k+2} ⋯ = lim_n NF(x_1 ⋯ x_n u^k) ∈ ∂L`.

## 2. Phase shift (item 2)

`S(x_1) = {s} ⊆ F(s)` and `s → s`. So the `P`-normal form of `s^N x_1 ⋯ x_n` is
`s ⋯ s x_1 ⋯ x_n`, of length `N + n`. By §1, for `k ≥ N`:
- `NF(s^N x_1 ⋯ x_n u^n) = (su)^N (x_1u) ⋯ (x_{n-N}u) x_{n-N+1} ⋯ x_n`;
- `NF(s^N x_1 ⋯ x_n u^k) = (su)^N (x_1u) ⋯ (x_{k-N}u) x_{k-N+1} ⋯ x_n`.

By continuity of the action on `L ∪ ∂L`, letting `n → ∞`:
- `s^N ξ_x = (su)^N (x_1u)(x_2u) ⋯`;
- `s^N ζ_{x,k} = (su)^N (x_1u) ⋯ (x_{k-N}u) x_{k-N+1} x_{k-N+2} ⋯`.

## 3. Singularity over V after recoding (item 3)

Let `φ` be a coding of `∂L` by complete binary prefix codes on the follower-set graph, as in
`prefix-replacement-actions-recode-into-germ-extensions-of-v`. Two facts about `φ`:
- `φ` is injective, and `φ` of a path is the concatenation of its edge codes;
- a finite-state deterministic parse of an eventually periodic binary sequence is eventually
  periodic. So `φ^{-1}` of a rational point is eventually periodic.

Also, the follower set after a positive normal-form word depends only on its last letter.

Let `x` be not eventually periodic. Suppose `φ s^N φ^{-1}` agrees on a binary cylinder `[c]`
containing `φ(ξ_x)` with a prefix replacement `c w ↦ c' w`.

**The prefix exchange.** Put `α_k = (x_1u) ⋯ (x_ku)`. Choose `k ≥ N` with
`φ(α_k) = c r` for some word `r`, which is possible since `φ(α_k)` exhausts `φ(ξ_x)`. Let `q`
be the state after `α_k`. Then for every tail `η` admissible after `α_k`:

    φ(s^N(α_k η)) = γ · code_q(η),   where γ = c' r.                          (∗)

**Determining γ.**
- Put `η_1 = (x_{k+1}u)(x_{k+2}u) ⋯` and `β = (su)^N (x_1u) ⋯ (x_ku)`, so `|β| = k + N`.
- By §2, `s^N ξ_x = β η_1`. The state after `β` is again `q`, since `β` also ends in `x_k u`.
- So (∗) gives `γ · code_q(η_1) = φ(β) · code_q(η_1)`.
- If `|γ| ≠ |φ(β)|`, then `code_q(η_1)` equals a proper shift of itself, hence is eventually
  periodic. Then `η_1`, hence `x`, is eventually periodic, which is false.
- Therefore `γ = φ(β)`.

**The contradiction.** Apply (∗) to `η_2 = x_{k+1} x_{k+2} ⋯`, so that `α_k η_2 = ζ_{x,k}`.
- (∗) gives `φ(s^N ζ_{x,k}) = φ(β) code_q(η_2) = φ((su)^N (x_1u) ⋯ (x_ku) x_{k+1} ⋯)`.
- By §2 the true value is `φ((su)^N (x_1u) ⋯ (x_{k-N}u) x_{k-N+1} x_{k-N+2} ⋯)`.
- These two paths first differ at letter `k + 1`: `x_{k-N+1} u` against `x_{k-N+1}`.
  So they are distinct, and by injectivity of `φ` so are their codes.

So `s^N` is singular at `ξ_x` over `V`. ∎

**Over B.** Every element of `B` is locally a state-preserving prefix replacement, which `φ`
turns into a `V`-local map. So a point singular over `V` is singular over `B`. ∎

## 4. Cantor set (item 4)

Singular sets are closed: a point where the map agrees locally with the base group has a
whole neighbourhood of such points. By §3 the closed set `sing(s^N)` contains the points
`ξ_x` with `x` not eventually periodic. By (G3) these are dense in the Cantor set
`{ξ_x : S(x_1) = {s}}`, since `x ↦ ξ_x` is a homeomorphism onto its image. ∎

## 5. The finite-index remark

Suppose a structure on a finite-index subgroup `K` is built from `L` by tracking cosets, as in
BBCMP Theorem 2.12. Then `K` acts on a copy of `∂L` by restriction, and some `s^N` lies in `K`.
So §3 applies to it. The same holds for the two standard coset constructions for finite
extensions. The claim states this only as a remark: BBCMP Proposition 1.4(2) is used on main
without its proof, and nothing here depends on how that proof goes.

## Trust surface

- (G1)--(G3) are standard Garside theory, recalled.
- BBCMP §2.3 and Theorem 2.4 were read at source (p. 11).
- The recoding is from `prefix-replacement-actions-recode-into-germ-extensions-of-v`.
- Everything else is the explicit computation above.
