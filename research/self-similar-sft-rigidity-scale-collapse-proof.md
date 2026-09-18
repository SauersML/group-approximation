---
rg: 2
id: self-similar-sft-rigidity-scale-collapse-proof
kind: route
title: Pull macro idempotents back through the blocks of the substitution; block products recover them, so commutation cannot appear, and the scale map D' -> N(D'-2) is expanding
target: self-similar-sfts-are-quantum-rigid-iff-rigid-at-one-scale
requires:
  - sft-crossed-product-fp-iff-quantum-rigid
---

Notation as in the target. `|·|` is the `ℓ¹` norm on `Z^2`, and `⌊z/N⌋` is taken coordinatewise.

**(B)** For `z, w ∈ Z^2`: `|⌊z/N⌋ − ⌊w/N⌋| <= |z − w|/N + 2`. Each coordinate contributes at most `|z_i − w_i|/N + 1`.

## Item 1

Let `(M_c(Z))_{c ∈ A, Z ∈ Z^2}` be a `D'`-family on `W`, and define `E_a(z)` as in the target. Put `D = N(D' − 2)`.

- **(Q1)** `Σ_a E_a(z) = Σ_c M_c(Z) = I`. Also
  `E_a(z)E_b(z) = Σ_c [σ(c)_{pos} = a][σ(c)_{pos} = b] M_c(Z) = δ_{ab} E_a(z)`, using orthogonality of the `M_c(Z)`.
- **(Q2)** Let `|z − w| <= 2D`. By (B), `|Z(z) − Z(w)| <= 2D/N + 2 = 2D' − 2 <= 2D'`. So every `M(Z(z))` commutes with
  every `M(Z(w))` by macro (Q2), and hence `E(z)` commutes with `E(w)`.
- **(Q3)** Let `p` be a pattern on `B_D`, placed at `z`, that does not occur in `Ω`.
  - Every site `w ∈ z + B_D` has `|Z(w) − Z(z)| <= D/N + 2 = D'`, by (B). So the blocks meeting the window lie in the
    macro ball `Z(z) + B_{D'}`, whose `M`'s pairwise commute (distances `<= 2D'`).
  - Expanding each `E_{p(w)}(w)` and inserting `Σ_c M_c(Z') = I` at the remaining macro sites gives
    `∏_w E_{p(w)}(w) = Σ_q [σ(q) ⊇ p] ∏_{Z' ∈ Z(z)+B_{D'}} M_{q(Z')}(Z')`.
    The sum runs over macro patterns `q` on `Z(z) + B_{D'}` whose substituted image `σ(q)` agrees with `p` on the
    window.
  - If such a `q` occurs in `Ω`, say in `y ∈ Ω`, then `σ(y) ∈ Ω` contains `σ(q)` and hence `p`, a contradiction. So
    every `q` in the sum is forbidden on `B_{D'}`, and its product vanishes by macro (Q3).
- **Recovery of the macro family.** The `E(z)` with `z` in one block `NZ + [0,N)^2` are all combinations of the one
  orthogonal family `(M_c(Z))_c`, so they commute. Moreover
  `∏_{u ∈ [0,N)^2} E_{σ(c)_u}(NZ + u) = Σ_{c'} [σ(c') = σ(c)] M_{c'}(Z) = M_c(Z)`, since `σ` is injective.
  So every `M_c(Z)` is a polynomial in the `E`'s. If the `E`'s commuted, so would the `M`'s.
- **Periodicity.** If `M(Z + λ) = M(Z)` for `λ ∈ Λ`, then `E(z + Nλ) = E(z)` for `λ ∈ Λ`. ∎

## Item 2

- **Monotonicity.** A `D''`-family is a `D`-family for every `D <= D''`. (Q2) is weaker at `D`. For (Q3) at `D`: a
  pattern forbidden on `B_D` has only forbidden extensions to `B_{D''}`. Insert partitions of unity, which commute at
  scale `D''`, to write its product as a sum of vanishing `B_{D''}` products. Hence `D`-rigid implies `D''`-rigid.
- **Iteration.** Suppose some `D_0`-family `M` does not commute. Define `D_{k+1} = N(D_k − 2)`.
  - Since `D_0 > 2N/(N−1)`, we have `D_1 − D_0 = (N−1)D_0 − 2N > 0`. So `D_k` increases, and the differences
    `D_{k+1} − D_k = N(D_k − D_{k−1})` grow, so `D_k → ∞`.
  - By item 1, iterated, there is a non-commuting `D_k`-family for every `k`.
  - By monotonicity, `Ω` is not `D`-rigid for any `D >= r`. Choose `k` with `D_k >= D`: the `D_k`-family is a
    non-commuting `D`-family.
- **Conversely,** `D_0`-rigid gives rigidity at the scale `D_0 >= r`.
- **Finite presentation.** The last clause of item 2 is `sft-crossed-product-fp-iff-quantum-rigid`. ∎

## Item 3

Fixed-point tile sets `τ` with zoom `N`, in the sense of Durand–Romashchenko–Shen, *Fixed-point tile sets and their
applications*, J. Comput. Syst. Sci. 78 (2012); cited from the standard definition, not re-read here.
- Every `τ`-tile `c` has a macrotile `σ(c)`, an `N × N` block of `τ`-tiles.
- Macrotiles of tiles that match along an edge match along the corresponding macro-edge. So the substituted image of
  a `τ`-tiling is a `τ`-tiling: `σ(Ω) ⊆ Ω`.
- Different tiles have different macrotiles, since the macrotile encodes its colour: `σ` is injective.
- For Wang tiles `r = 1`, so `D_0 = max(1, ⌊2N/(N−1)⌋ + 1)`, which equals `3` for `N >= 4`. ∎
