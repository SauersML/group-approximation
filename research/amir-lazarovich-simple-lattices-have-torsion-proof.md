---
rg: 2
id: amir-lazarovich-simple-lattices-have-torsion-proof
kind: route
title: One collapsed pair of generators spreads along untwisted y-moves to all of V(O_d), then to Z, so every finite quotient of Λ' is a quotient of (Z/2)²
target: amir-lazarovich-simple-lattices-have-torsion
requires: []
artifacts:
  - research/artifacts/gq-bh-bh-free-extensions-al-ymove-closure.md
  - research/artifacts/gq-bh-bh-free-extensions-cd3-sources.md
---

## Notation

- `ℓ = 2d − 1` and `V = V(O_d)`, the `(d−1)`-subsets of `[ℓ]`.
- `υ_i = (i, i+1)(i+2, i+3)`, with indices mod `ℓ`.
- **AL's explicit data:**
  - `A' = {5, 6, 7, 9, …, 2d−1}` and `K_0 = [ℓ] − A'`;
  - `A_j = K_0 − {j̄}`;
  - `B = K_0 − {8}`;
  - `C_i = {i, …, i+d−3} ∪ {1 or d}`;
  - `δ_B = (x_1 y_1)(x_2 x_3)`, `δ_{C_i} = γ_i = (y_i y_{i+1})(y_{i+2} y_{i+3})`,
    `δ_{A_j} = α_j` (which fixes `Y`), and `δ_D = id` otherwise;
  - `ζ_{y_i} = υ_i`.
- `φ: Λ' → G` is any homomorphism to a finite group. Write `D ≈ D''` for `φ(D) = φ(D'')`.

## Step 1: the pair-move lemma

The relators `z²`, `D²` and `z·D·δ_D(z)·ζ_z(D)` give `ζ_z(D) = z · D · δ_D(z)`. So
`φ(ζ_z D) = φ(z) φ(D) φ(δ_D z)`. If `D ≈ D''` and `δ_D(z) = δ_{D''}(z)`, then
`ζ_z D ≈ ζ_z D''`.

## Step 2: twisted points are fixed and contain 1

Let `T_i = {D : δ_D(y_i) ≠ y_i}`. From the data, `T_i` is `{B}` (only when `i = 1`)
together with the `C_j` with `i ∈ {j, …, j+3}`.
- Every element of `T_i` contains 1: `B ∋ 1`, and `C_j ∋ 1` in both cases of its definition.
- `υ_i` fixes every element of `T_i`: `supp υ_1 ⊆ B` is AL's (E3), and `supp υ_i ⊆ C_j` is
  (E4), which holds for `d ≥ 9` (artifact).
- **(∗)** Hence if `υ_i D ≠ D`, then `y_i` is untwisted at `D` and at `υ_i D`.

## Step 3: the seed pair

AL's construction gives a homomorphism `Γ → Λ'` with `x_i ↦ x_i` and `a_j ↦ A_j`. The
relator `x_i a_j x_{i'} a_{j'}` maps to the relator for `(z, D) = (x_i, A_j)`, since
`α_j(x_i) = x_{i'}` and `ξ_i(A_j) = A_{j'}` (AL's proof of their interlacing lemma). So
`φ ∘ ι` is a finite quotient of `Γ`, and (H) gives `A_j ≈ A_k`.

## Step 4: into the special-free region

Let `V_0 = {D : 1 ∉ D}`. By Step 2, `V_0 ∩ T_i = ∅` for every `i`.
- `ℓ ∈ A'`, so `ℓ ∉ A_j, A_k`.
- `υ_ℓ = (ℓ, 1)(2, 3)`, so `1 ∈ υ_ℓ A` iff `ℓ ∈ A`. Hence `P = υ_ℓ A_j` and
  `P' = υ_ℓ A_k` lie in `V_0`.
- `A_j, A_k ∉ T_ℓ`, which consists of `C`'s, so Step 1 applies and gives `P ≈ P'`.
- `|P ∩ P'| = |A_j ∩ A_k| = d − 2`.

## Step 5: `H_0 = ⟨υ_i : 2 ≤ i ≤ ℓ−3⟩` is `Alt(Ω)`, where `Ω = [2..ℓ]` and `|Ω| = 2d − 2 ≥ 16`

**Primitivity.** Take the windows `W_i = {i, …, i+4}` for `2 ≤ i ≤ ℓ−4`.
- `υ_i υ_{i+1}` is the 5-cycle `(i, i+1, i+3, i+4, i+2)`. So `K_i = ⟨υ_i, υ_{i+1}⟩` is
  transitive of prime degree on `W_i`, hence primitive there, and it fixes `Ω − W_i`
  pointwise.
- Let `Δ` be a block with points `p < q`.
  - **If `q − p ≤ 4`:** some `W_i` contains both. `Δ ∩ W_i` is a block of the primitive
    action of `K_i` on `W_i` with at least two points, so `Δ ⊇ W_i`.
  - **If `q − p ≥ 5`:** take `i = p`. `K_i` fixes `q ∉ W_i`, so `kΔ = Δ` for every
    `k ∈ K_i`, and `Δ ⊇ K_i p = W_i`.
- Consecutive windows meet in 4 points, so in either case `Δ = Ω`.

**Jordan's theorem.** A primitive group containing a `p`-cycle with `p ≤ |Ω| − 3` contains
`Alt(Ω)` (Wielandt, *Finite permutation groups*, 13.9; cited, not re-read). The generators
are even, so `H_0 = Alt(Ω)`.

## Step 6: `V_0` lies in one class `K`

- `H_0` fixes 1 and preserves `V_0`. `V_0` meets no `T_i`, so every letter of `H_0` is a
  legal pair move on `V_0 × V_0`.
- So `≈ ∩ V_0²` is `H_0`-invariant. It contains the Johnson-distance-1 pair `(P, P')`.
- `Alt(Ω)` is transitive on ordered pairs of `(d−1)`-subsets of `Ω` meeting in `d−2`
  points. `Sym(Ω)` is, and a transposition inside `P ∩ P'` fixes the pair.
- The Johnson graph `J(Ω, d−1)` is connected.

## Step 7: `K = V`

**Lemma L.** If `υ_i Q ≠ Q` and `υ_i Q ∈ K`, then `Q ∈ K`.
- By (∗), `y_i` is untwisted at `υ_i Q`.
- Pick `R ∈ V_0` with `υ_i(1) ∉ R`. Then `υ_i R ∈ V_0`, and `R ≈ υ_i Q`.
- Step 1 gives `υ_i R ≈ υ_i υ_i Q = Q`.

**Induction.** For `Q ∋ 1`, let `b(Q) = max{b : {1, …, b} ⊆ Q}`, so `b ≤ d − 1`.
- **`b = 1`.** `υ_1 Q ∌ 1`, so `υ_1 Q ∈ V_0 ⊆ K`, and `υ_1 Q ≠ Q`.
- **`b ≥ 2`.** Here `b ∈ Q`, `b + 1 ∉ Q` and `b + 3 ≤ d + 2 < ℓ`. So `υ_b Q` omits `b`,
  keeps `1, …, b−1`, and has `b(υ_b Q) = b − 1`.

Lemma L and induction put every `Q` in `K`. So `φ` is constant on `V`.

## Step 8: the tree side, and the conclusion

**The tree side.** Put `v = φ(D)`. Step 1's identity, read for `δ`, gives
`φ(δ_D z) = v φ(z) v`.
- A generic `D` (`δ_D = id`) shows that `v` commutes with every `φ(z)`. So `φ` is constant
  on the orbits of `⟨δ_D⟩` on `Z`.
- These orbits are all of `Z`:
  - the `α_j` generate `Γ`'s alternating local action on `X`;
  - `β` joins `x_1` to `y_1`;
  - `γ_i` joins `y_i` to `y_{i+1}`.
- So `φ(Λ') = ⟨φ(z), v⟩` is a quotient of `(Z/2)²`.

**Conclusion.**
- `FR(Λ') ⊇ Λ'^+`, and the reverse inclusion holds because `Λ'/Λ'^+` is finite.
- `DD' ∈ Λ'^+` is a nontrivial involution. Nontrivial because `Λ'` acts simply
  transitively on vertices (AL, Prop. "the lattice Lambda") and moves `x_0` to the
  opposite corner of a square. An involution because `[D, D'] = D² = 1`.
- A group with torsion has infinite cohomological dimension. ∎

**Trust surface.**
- Cited, not re-read: AL's construction and their Theorem A (`Λ` is simple), LLM's Lemma
  "Finite residual" and Radu's Theorem 5.5 (only for when (H) holds), and Jordan's theorem.
- Verified: the facts about AL's data used in Steps 2 and 4 by hand, and again by computer
  for `d = 9, …, 12` (artifact).
