---
rg: 2
id: aanderaa-cohen-tower-subgroups-are-decidable-proof
kind: route
title: Normal forms K = T x| Z^2 with free factors on index sets, a good-subgroup Britton algorithm, a retraction lemma for products L·P', and a Nielsen basis change decide every associated subgroup of the Aanderaa–Cohen tower
target: aanderaa-cohen-tower-subgroups-are-decidable
requires: []
---

Notation is that of the target. For `X ⊆ Z²`, `F_X ≤ T` is the free factor on `{t(r, s) : (r, s) ∈ X}`.
Words in `x, y` are identified with `Z²`. Since `x, y` commute, `z^{-1} t(r, s) z = t((r, s) + z)`.

## 0. Two free-group facts

- **(F1) Normal form in `K`.** Every `k ∈ K` is uniquely `k = τ z`, with `τ ∈ T` a reduced word in the
  basis and `z ∈ Z²`. It is computable from any word.
- **(F2) Products of free factors.** For basis subsets `X, W`, a reduced word `τ` lies in `F_X F_W` iff
  it splits as `τ = u v` with the letters of `u` in `X` and those of `v` in `W`.
  - This is because a product `u v` of reduced words cancels only along a segment with letters in
    `X ∩ W`.
  - When `X` and `W` are decidable, a split is found by scanning, and it gives a witness.

## 1. Rung 1: the subgroups of `K`

- **Shape.** `K^{M,N}_{a,b} = F_{(a,b)+Λ} ⋊ Λ`, with `Λ = MZ × NZ` (Chiodo–Vyas §4.1 (7)).
- **Membership.** `k = τ z` lies in it iff `z ∈ Λ` and every letter of `τ` has index in `(a, b) + Λ`.
  This is decidable.
- **Isomorphisms.** `φ_i, ϕ_j` are computable on normal forms: `t(u, v) ↦` the moved index, and
  `x^M, y^N ↦` the prescribed powers.
- **Word problem.** Britton reduction in `K_M` is effective, so `K_M` has solvable word problem.
- **Products with free factors (P1).** Let `X` be `Λ`-invariant and `Y ⊆ Z²`. Then
  `(F_X ⋊ Λ)·F_Y ∋ τ z` iff `z ∈ Λ` and `τ ∈ F_X · F_{Y − z}`.
  - Proof: `(τ_1 z_1) τ_2 = τ_1 (z_1 τ_2 z_1^{-1}) z_1`, and conjugation by `z_1` shifts indices by
    `−z_1`.
  - By (F2), (P1) is decidable with a witness when `X` and `Y` are decidable.

## 2. The good-subgroup algorithm (G)

Let `G* = G *_{θ_k : D_k → D'_k}`, with stable letters `s_k` and `s_k^{-1} a s_k = θ_k(a)`. Let `L ≤ G` be
good, meaning `θ_k(L ∩ D_k) = L ∩ D'_k`. Then `L* = ⟨L, s_k⟩ ≅ L *_{θ_k|}` and `L* ∩ G = L`
(Chiodo–Vyas Lemma 3.2).

**Algorithm.** Given `w = g_0 s_{k_1}^{ε_1} g_1 ⋯ s_{k_n}^{ε_n} g_n` Britton-reduced, set `g'_0 = g_0`.
For `j = 1, …, n`:
- let `E_j = D_{k_j}` if `ε_j = 1`, and `E_j = D'_{k_j}` if `ε_j = −1`;
- decide whether `g'_{j−1} ∈ L E_j`, and if so pick `c_j ∈ E_j` with `g'_{j−1} ∈ L c_j`;
- put `g'_j = θ^{ε_j}(c_j) g_j`.

Then `w ∈ L*` iff every step succeeds and `g'_n ∈ L`.

**Proof.**
- *(⇐)* Moving each `c_j` through its stable letter rewrites `w` as `l_0 s_{k_1}^{ε_1} l_1 ⋯ g'_n`.
- *(⇒)* A reduced word of `L*` is Britton-reduced in `G*`: a pinch `s^{-1} l s` with `l ∈ L ∩ D` is
  already a pinch in `L*`.
  - Two reduced forms of one element have the same stable-letter sequence, and `g_0 ∈ l_0 E_1`.
  - A different choice `c_j` changes `g'_j` by left multiplication by `θ^{±}(L ∩ E_j) ⊆ L` (goodness).
    This affects neither the next test nor the last one. Induct on `n`.

**Effectiveness.** (G) is effective when:
- Britton reduction in `G*` is effective;
- membership in `L` is decidable;
- the tests `g ∈ L E` are decidable with witnesses.

## 3. Item 2: the machine subgroup

**`T_M = F_{H_0}` is good in `K` for `K_M`.**
- By (F1), `T_M ∩ K^{m,m}_{a_i,b_i} = F_{H_0 ∩ ((a_i,b_i)+mZ²)}`, and `φ_i` maps it to
  `F_{μ_i(H_0 ∩ ((a_i,b_i)+mZ²))}`, where `μ_i` is the move of quadruple `i`.
- *Inclusion "⊆".* A configuration `p ∈ H_0` in that residue class is not the halting configuration
  `(0,0)`. Quadruple `i` is its unique applicable quadruple, so `μ_i(p)` is its successor, which lies in
  `H_0`.
- *Inclusion "⊇".* Let `q ∈ H_0` with `q ≡ (c_i, 0)` for the lattice `m²Z × Z`. Write
  `q = (u m² + c_i, v)`. Then `u ≥ 0`, because `0 ≤ c_i < m²` and `q_1 ≥ 0`.
  - So `q = μ_i(p)` with `p = (u m + a_i, v m + b_i) ∈ N²`.
  - The machine at `p` applies quadruple `i`, so `p → q` and `p ∈ H_0`.
- The same holds for the quadruples of type L. So `T'_M = ⟨T_M, r_i, l_j⟩`, the subgroup of Chiodo–Vyas
  §4.1 (15)–(16), is good, and `T'_M ∩ K = T_M`.

**Membership `≤ H_0(M)`.** Run (G) with `L = T_M`.
- Membership in `L`: `τ z ∈ F_{H_0}` iff `z = 0` and every letter lies in `H_0`.
- The tests `g ∈ T_M E`, with `E = F_S ⋊ Λ'` an associated subgroup: `F_{H_0}` has no `Z²`-part, so
  `g = τ z ∈ F_{H_0}·(F_S ⋊ Λ')` iff `z ∈ Λ'` and `τ ∈ F_{H_0} F_S`.
  - Here `S` is the index set of the associated subgroup and `Λ'` its lattice.
  - This is decidable with a witness, by (F2).

**`H_0(M) ≤` membership.** `t(α, β) ∈ T'_M` iff `(α, β) ∈ H_0(M)` (Chiodo–Vyas (17)).

**`WP(G_M)`.**
- Britton's lemma for `G_M = K_M *_{T'_M}` needs only membership in `T'_M`.
- Conversely, `q^{-1} t(α, β) q = t(α, β)` iff `(α, β) ∈ H_0` (Chiodo–Vyas (19)).
- So `WP(G_M) ≡_T H_0(M)`.

## 4. Item 3: the subgroups `P` and `P'` of `H_1`

- **`H_1`.** It has solvable word problem, as a free product of `K_M`, `C × F(b)` and `Z`.
- **Membership in `P = F_{I × {0}}`.** The element must be a single `K_M`-syllable lying in `K` (Britton),
  with `z = 0` and letters in `I × {0}`. The set `I` of codes is decidable.
- **The group `Q`.** Put `Q = P * F(b) * ⟨d⟩ ≤ H_1`, where `F(b) = 1 × F(b)`. Then `h ∈ Q` iff:
  - its `K_M`-syllables lie in `P`;
  - its `(C × F(b))`-syllables have trivial `C`-coordinate, which uses `WP(C)`.
- **`Q` is free.** Its basis is `{t_α} ∪ {b_j} ∪ {d}`.
- **Nielsen change.** `t'_α = t_α w_α(b) d` gives another basis. The inverse substitution is
  `t_α = t'_α d^{-1} w_α(b)^{-1}`.
  - So `P' = ⟨t'_α⟩` is a free factor of `Q`.
  - `h ∈ P'` iff `h ∈ Q` and the rewrite of `h` in the new basis uses only letters `t'_α`.
- **Conclusion.** `ψ` and `ψ^{-1}` are computable, and `H_2` has solvable word problem.

## 5. Item 4: the subgroups `A, A_i, A_±` of `H_2`

Each has the form `⟨L, p⟩`, with `L` good in `H_1` for `H_2` (Chiodo–Vyas §4.2 (16), (19)):
- `L_A = ⟨t, x⟩ * F(b) * ⟨d⟩`;
- `L_i = ⟨t_i, x^m⟩ * F(b) * ⟨d⟩`;
- `L_+ = T'_M * F(b) * ⟨d⟩`;
- `L_- = T'_M * ⟨d⟩ * ⟨b_j c_j⟩`.

Run (G) in `H_2 = H_1 *_ψ`, with `E ∈ {P, P'}`.

**Membership in `L`.** Check the syllables:
- `K_M`-syllables in `⟨t, x⟩ = F_{Z×0} ⋊ ⟨x⟩` or in `⟨t_i, x^m⟩ = F_{(i,0)+mZ×0} ⋊ ⟨x^m⟩`, by §1; or in
  `T'_M`, by §3;
- `(C × F(b))`-syllables in `1 × F(b)`, or in `⟨b_j c_j⟩ = {(w(c), w(b))}`. Read `w` off the free
  coordinate and test `w(c)` against `WP(C)`.
- `d`-syllables automatically.

**Retraction lemma (for the tests `h ∈ L E`).** Let `ζ : H_1 → K_M` kill the other two factors. Put
`L_1 = ζ(L) ≤ L`, which is the `K_M`-part of `L`, and let `ψ_0 = id_P` if `E = P`, `ψ_0 = ψ` if `E = P'`.
- Then `ζ ∘ ψ_0 = id_P`, and `ψ_0(L_1 ∩ P) ⊆ L`.
- **Claim.** `h ∈ L E` iff `ζ(h) ∈ L_1 P` and `h ψ_0(c̄)^{-1} ∈ L`, where `c̄ ∈ P` is any witness with
  `ζ(h) ∈ L_1 c̄`.
- *(⇒)* If `h = l e`, then `ζ(h) = ζ(l) ζ(e)`, with `ζ(e) ∈ P`. So `ζ(e) = ȳ c̄` with `ȳ ∈ L_1 ∩ P`.
  Lifting, `e = ψ_0(ȳ) ψ_0(c̄)` with `ψ_0(ȳ) ∈ L`, so `h ψ_0(c̄)^{-1} = l ψ_0(ȳ) ∈ L`.
- *(⇐)* is clear.
- **Why `ψ(L_1 ∩ P) ⊆ L`.** `L_1 ∩ P` is generated by the `t_α` lying in `L_1`, a free-factor
  intersection by (F1). For such `α`:
  - `ψ(t_α) = t_α w_α(b) d ∈ L`, since `F(b), d ⊆ L` in the first three cases.
  - For `L_-`, `t_α ∈ T'_M` means `w_α(c) = 1` in `C`. Then `w_α(b) = w_α(bc) ∈ ⟨b_j c_j⟩`. This is the
    mechanism of Chiodo–Vyas (20).
- **`K_M`-level tests `k ∈ L_1 P`.**
  - For `L_1 ≤ K`: `k` must lie in `K`, and then (P1) applies with `Y = I × {0}`.
  - For `L_1 = T'_M`: run (G) in `K_M` for `L = T_M` on the element `k c^{-1}`. The final test becomes
    `g' ∈ T_M P`, which by (P1) means `z = 0` and `τ ∈ F_{H_0} F_{I×0}`. It is decidable with a witness.

All inputs of (G) are effective. So membership in `A, A_i, A_±` is decidable, and `H_3` has solvable
word problem. `∎`

## Where the hypotheses enter

- `WP(C)` enters in the `C`-coordinate tests of §4 and §5.
- `H_0(M)` enters only through `T_M = F_{H_0}` (§3 and the `A_±` tests).
- The rest is normal forms in `Z² * Z` and in free products.
