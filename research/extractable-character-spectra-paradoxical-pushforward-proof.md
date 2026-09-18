---
rg: 2
id: extractable-character-spectra-paradoxical-pushforward-proof
kind: route
title: "Push the spectral law forward along the equivariant extraction to a probability measure on C that is almost invariant under h_1, h_2, h_3; three prefix moves make such a measure paradoxical"
target: extractable-character-spectra-carry-no-almost-invariant-vectors
requires:
  - cantor-integer-maps-central-growth-criterion
---

Notation is as in the target. Write `δ_v(η) = sup_B |v_*μ_η(B) − μ_η(B)|`.

**Step 1 (transport of almost invariance).**
- Step 8 of `cantor-integer-maps-central-growth-criterion-proof` gives `μ_{π(v)η} = v_*μ_η` and
  `δ_v(η) ≤ 2‖π(v)η − η‖`. (That step is textbook spectral theory and is repeated in the target
  claim's Theorem B.)
- Let `μ_η(𝔐) = 1` and put `ν = ∫_𝔐 p(χ) dμ_η(χ) ∈ Prob(C)`. This is well defined because `p` is
  Borel, so each `χ ↦ p(χ)(B)` is a Borel function with values in `[0,1]`.
- By equivariance and invariance of `𝔐`,

  ```text
  v_*ν = ∫ v_*p(χ) dμ_η = ∫ p(vχ) dμ_η(χ) = ∫ p d(v_*μ_η).
  ```

- For a Borel `B ⊆ C`, the function `f_B(χ) = p(χ)(B)` takes values in `[0,1]`. So
  `|v_*ν(B) − ν(B)| = |∫ f_B d(v_*μ_η − μ_η)| ≤ δ_v(η)`: split the signed measure by Hahn
  decomposition, and each part has mass at most `δ_v(η)`.

**Step 2 (three prefix moves make ν paradoxical).**
- Let `δ = max_i 2‖π(h_i)η − η‖`, and write `a = ν[00]`, `b = ν[01]`, `c = ν[10]`, `d = ν[11]`.
- `h_1^{-1}[00] = [0]`, so `|ν[00] − ν[0]| = |a − (a+b)| = b ≤ δ`.
- `h_2^{-1}[01] = [0]`, so `|ν[01] − ν[0]| = a ≤ δ`.
- Hence `ν[0] = a + b ≤ 2δ`. Since `h_3^{-1}[1] = [0]`, `ν[1] ≤ ν[0] + δ ≤ 3δ`.
- So `1 = ν(C) ≤ 5δ`, and `max_i ‖π(h_i)η − η‖ = δ/2 ≥ 1/10`.

This proves Theorem K.

**Step 3 (Corollary 1).**
- `𝔐` is `V`-invariant, so `E(𝔐)` commutes with `π(V)`, by `π(v)E(B)π(v)^{-1} = E(vB)`. It
  also commutes with `π(A)`, so it commutes with `π(G)`.
- Put `η' = E(𝔐)η`. If `η' ≠ 0`, then `η'/‖η'‖` has law carried by `𝔐`, and
  `‖(π(h_i) − 1)η'‖ ≤ ‖(π(h_i) − 1)η‖`.
- Theorem K gives `‖η'‖ ≤ 10 max_i ‖(π(h_i) − 1)η‖`, i.e.
  `μ_η(𝔐) = ‖η'‖² ≤ 100 max_i ‖(π(h_i) − 1)η‖²`.

**Step 4 (Corollary 2).**
- `E(𝔐)` commutes with `π(G)`, so `b' = E(𝔐)b` is a cocycle of the subrepresentation on
  `E(𝔐)H`, and `ψ_𝔐 = ‖b'‖²`.
- Apply Theorem A of `cantor-integer-maps-central-growth-criterion` to `b'`. This gives
  `ξ_j ∈ E(𝔐)P_jH`, `S' = Σ_j ‖ξ_j‖²`, and `sup_M ψ_𝔐(z^M) ≤ 4S'`.
- For every `J`, `ξ_{≤J} = Σ_{j≤J} ξ_j` lies in `E(𝔐)H`, and
  `‖(π(h_i) − 1)ξ_{≤J}‖ = ‖Σ_{j≤J} P_j b'(h_i)‖ ≤ ψ(h_i)^{1/2}`.
- By Theorem K applied to `ξ_{≤J}/‖ξ_{≤J}‖`, `‖ξ_{≤J}‖² ≤ 100 max_i ψ(h_i)`. Letting
  `J → ∞`, `S' ≤ 100 max_i ψ(h_i)`, so `sup_M ψ_𝔐(z^M) ≤ 400 max_i ψ(h_i)`.

**Step 5 (unions).**
- Let `(𝔐_n, p_n)` be extractions, and put `𝔑_n = 𝔐_n ∖ ∪_{m<n} 𝔐_m`. Each `𝔑_n` is
  `V`-invariant and Borel.
- `p = p_n` on `𝔑_n` is Borel and equivariant on `∪_n 𝔐_n`.

**Step 6 (how V acts on cylinder values).**
- Each `v ∈ V` has a finite partition `C = ⊔_i [s_i]` such that `v(s_i w) = t_i w` for all `w`,
  with `C = ⊔_i [t_i]`.
- For a word `w`, `v^{-1}[t_i w] = [s_i w]`, so
  `(vχ)([t_i w]) = χ(v^{-1}·1_{[t_i w]}) = χ([s_i w])`.
- Hence, for every `F : T → [0,∞)`, every `i` and every `d ≥ |t_i w|`,

  ```text
  Σ_{|u|=d, u⊒t_i w} F((vχ)([u])) = Σ_{|u'|=d−|t_i|+|s_i|, u'⊒s_i w} F(χ([u'])).     (◆)
  ```

- Any word `w` is either inside some `[t_i]` or splits as a finite disjoint union of cylinders
  `[t_i w']`.

**Step 7 (class (iii)).**
- Let `𝔐_F` be the set of `χ` such that `M_{F,d}(w) = Σ_{|u|=d, u⊒w} F(χ([u]))` converges, as
  `d → ∞`, to a finite `M_F(w)` for every `w`, with `M_F(∅) > 0`.
- It is Borel: countably many Borel coordinate functions, and the convergence conditions are
  countable.
- By (◆) and the splitting of cylinders, the conditions for `vχ` are shifts and finite sums of
  those for `χ`. So `𝔐_F` is `V`-invariant, and `M_F^{vχ}([t_i w]) = M_F^{χ}([s_i w])`.
- For `d > |w|`, `M_{F,d}(w) = M_{F,d}(w0) + M_{F,d}(w1)`, so `M_F(w) = M_F(w0) + M_F(w1)`. A
  finitely additive, finite, nonnegative function on the clopen algebra of the compact space
  `C` extends uniquely to a Borel measure: a clopen set is compact, so any countable disjoint
  clopen decomposition of a clopen set is finite, and countable additivity on the algebra is
  automatic. Call the extension `M_F^χ`.
- The identity above says `M_F^{vχ} = v_* M_F^χ`, and `M_F(∅)` is `V`-invariant. So
  `p(χ) = M_F^χ / M_F^χ(C)` is an equivariant Borel extraction.

**Step 8 (class (ii)).**
- Take `F(e(t)) = |t|` for `t ∈ (−1/2, 1/2]`. Since `χ([w]) = χ([w0])χ([w1])` and
  `|arg(xy)| ≤ |arg x| + |arg y|`, `M_{F,d}(w)` is nondecreasing in `d`. It is bounded when the
  phase variation is bounded, so it converges.
- If `χ ≠ 1`, some `χ([w]) ≠ 1`, and then `M_F(∅) ≥ M_{F,|w|}(∅) > 0`.
- So class (ii) is contained in `𝔐_F`. Its bounded-variation condition is `V`-invariant by (◆)
  and the splitting, so it is an extraction.
- For a finite signed measure `λ` and `χ_λ(f) = e(∫ f dλ)`: `|arg χ_λ([u])| ≤ |λ|([u])`, so the
  phase variation is at most `|λ|(C)`.

**Step 9 (class (i)).**
- `χ([w]) = χ([w0])χ([w1])`, so an active cylinder has an active child. Hence `N_d` is
  nondecreasing.
- If `N_d ≤ N` for all `d`, it is eventually constant, equal to some `N ≥ 1` when `χ ≠ 1`. From
  that depth on, each active cylinder has exactly one active child. This gives `N` points
  `x_1, …, x_N` (the infinite active branches), and every cylinder avoiding them at that depth
  has `χ = 1`.
- A locally constant `f` is constant near each `x_i`, so `χ(f) = Π_i χ([u_i])^{f(x_i)}` for
  deep cylinders `u_i ∋ x_i`. So `χ` is finitely atomic. Conversely, a finitely atomic character
  has `N_d` at most its number of atoms.
- By (◆), the active points of `vχ` are the `v(x_i)`. So `p(χ) = (1/N) Σ_i δ_{x_i}` is
  equivariant. It is Borel because each `x_i` is determined by countably many coordinate
  conditions. The class is `V`-invariant by (◆).

This proves all claims of the target.
