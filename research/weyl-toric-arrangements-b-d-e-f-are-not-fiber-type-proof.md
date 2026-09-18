---
rg: 2
id: weyl-toric-arrangements-b-d-e-f-are-not-fiber-type-proof
kind: route
title: Test every rank-one projection with the Bibby--Delucchi disjointness criterion for B_n and D_n, and use non-supersolvable local lattices at the identity for D_n, E and F_4
target: weyl-toric-arrangements-b-d-e-f-are-not-fiber-type
requires:
  - euclidean-artin-toric-commensurability
---

Inputs from Bibby--Delucchi, arXiv:2202.11996v2 (read from the PDF):
- **Definition 3.4.1.** A fiber-type arrangement of rank `> 1` admits a fibration
  `p: M(A) -> M(A/Y)` along some admissible `Y`.
- **Lemma 3.2.4 and Theorem 3.3.1.** `p` is a fibration iff, for every `t ∈ M(A)` and
  all distinct `α, β ∈ A \ A_Y`, `(t + Y) ∩ H_α ∩ H_β = ∅`.
- **Theorem 3.4.3.** For essential `A`, fiber-type ⟺ supersolvable.
- **Corollary 4.4.13.** Supersolvability is the same for `A` in `Hom(Γ_1, G)` and in
  `Hom(Γ_2, G)` when `Γ_2 ⊆ Γ_1` has finite index. So by Theorem 3.4.3 the answer does
  not depend on `L`.
- **Remark 2.5.4.** If `P` is supersolvable, every interval `P_(≤x)` is a supersolvable
  geometric lattice.

Weyl toric arrangements are essential and irredundant.

## Step 0. Admissible directions, and the test

- Take `Γ = L*` (characters). Admissible `Y` correspond to primitive `λ ∈ Hom(Γ, Z)`:
  `Y = λ(C^×)`, and `c(α) = |λ(α)|`, so `A_Y = {α : λ(α) = 0}`.
- **Test.** Let `α, β ∈ A \ A_Y` be distinct, and `X` a connected component of
  `H_α ∩ H_β`. `X + Y` is an irreducible hypersurface.
  - If it lies in no `H_γ`, then `M(A) ∩ (X + Y)` is nonempty. Any `t` there has
    `t + Y ∋ t − y ∈ X`, so `(t + Y) ∩ H_α ∩ H_β ≠ ∅`, and `p` is not a fibration.
  - If `X + Y ⊆ H_γ`, then `H_γ ⊇ t + Y`, so `γ ∈ A_Y` and `H_γ ⊇ X`.
- **Summary (T).** `p` is a fibration only if every such `X + Y` lies in some `H_γ`
  with `γ ∈ A_Y`.

## Step 1. D_n (n >= 4) and B_n (n >= 3): no admissible direction works

Use `L = Z^n` (allowed for both, since `α(Z^n) ⊆ Z`), `v = e^(2πiu)`. Characters:
- D_n: `e_i ± e_j`;
- B_n: `e_i` and `e_i ± e_j`.

Each inversion `v_k ↦ v_k^(-1)` is an automorphism of `T` preserving `A`. It negates
`λ_k`.

1. **Pairs force |λ_i| = |λ_j|.** Suppose `λ_i ≠ ±λ_j`, so that `α = e_i − e_j` and
   `β = e_i + e_j` are both in `A \ A_Y`.
   - `H_α ∩ H_β = {v_i = v_j, v_i v_j = 1}` has the component
     `X_- = {v_i = v_j = -1}`.
   - A root `γ` with `H_γ ⊇ X_-` must lie in `Ze_i + Ze_j`, so `γ ∈ {±(e_i ± e_j)}`,
     or `γ ∈ {±e_i, ±e_j}` for B_n.
   - `H_(e_i) = {v_i = 1} ∌ X_-`, and `e_i ± e_j ∉ A_Y` by assumption.
   - So (T) fails. Hence `λ_i = ±λ_j` for all `i, j`, so `λ = ±(±1, …, ±1)`,
     primitive.
   - Using inversions, WLOG `λ = (1, …, 1)`, i.e. `Y` is the diagonal.
2. **The diagonal fails.** Now `A_Y = {e_i − e_j}`.
   - *D_n, n >= 4.* Take `α = e_1 + e_2`, `β = e_3 + e_4`. `X = H_α ∩ H_β` is a
     connected subtorus, and `X + Y = {v_1 v_2 = v_3 v_4}`. That is not any
     `{v_a = v_b}`, so (T) fails.
   - *B_n, n >= 3.* Take `α = e_1 + e_2` (`λ = 2`) and `β = e_3` (`λ = 1`). `X` is
     connected and `X + Y = {v_1 v_2 = v_3^2}`. That is not a root hypersurface, so (T)
     fails.
3. **Conclusion.** No projection of rank one is a fibration. By Definition 3.4.1 the
   arrangement is not fiber-type, for `L = Z^n` and hence (Theorem 3.4.3,
   Corollary 4.4.13) for every `L`.

**Checks** (the positive cases in part 2 of the target):
- *C_n.* `λ = e_n^*` works: the character `2e_i` has `H_(2e_i) = {v_i = ±1} ⊇ X_-`,
  and it lies in `A_Y`.
- *B_2.* `λ = (1,1)` works. The only transverse pairs share an index, and each gives
  `X + Y = {v_1 = v_2}`.
- *D_3.* `λ = (1,1,1)` works. All pairs `e_i + e_j` share an index.

## Step 2. Local lattices at the identity: D_n (n >= 4), E_6, E_7, E_8, F_4

**The identity layer.** The identity of `T_L` is a layer (a point), and so is the
identity component of every intersection of `H_α`. Near the identity, the exponential
map identifies these layers with the flats of the linear arrangement `{ker α : α ∈ Φ^+}`.
So `P_(≤ X) ≅ L(Φ)_(≤ exp^-1 X)`. In particular, for a parabolic subsystem
`Ψ = Φ ∩ span Ψ`, the layer `X_Ψ` has `P_(≤ X_Ψ) ≅ L(Ψ)`.

**Modularity criterion.** In a geometric lattice `L(Ψ)` of rank `r`, suppose a line
`ℓ = Cλ` (a coatom) is modular. Take hyperplanes `H_α ≠ H_β` not containing `ℓ`, and
`y = H_α ∩ H_β`, which has rank 2. Bibby--Delucchi Remark 2.3.2(2) gives
`rk ℓ + rk y = rk(ℓ ∨ y) + rk(ℓ ∧ y)`, i.e. `(r−1) + 2 = r + rk(ℓ ∧ y)`. So
`ℓ ∧ y = ℓ + y` is a root hyperplane. Equivalently,
`β(λ) α − α(λ) β` is proportional to a root.

1. **L(D_4) has no modular coatom.** Apply the criterion to `α, β = e_i ∓ e_j`: the
   combination is `∝ λ_j e_i − λ_i e_j`, which is a root only if `|λ_i| = |λ_j|`, or
   when one of `α, β` contains `ℓ`. So `λ = (±1, …, ±1)`. Then `e_1 + e_2` and
   `e_3 + e_4` give `∝ (1,1,−1,−1)`, which is not a root. Hence `L(D_4)`, and
   `L(D_n)` for `n >= 4`, is not supersolvable.
2. **D_n, E_6, E_7, E_8.** Each contains D_4 as a parabolic subsystem (a sub-diagram
   of its Dynkin diagram). So `P(A_Φ)` has an interval `≅ L(D_4)`, and by Remark 2.5.4
   `P(A_Φ)` is not supersolvable.
3. **F_4.** Roots are `±e_i`, `±e_i ± e_j` and `½(±1, ±1, ±1, ±1)`. `P_(≤ id) ≅ L(F_4)`.
   - The long roots `e_i ± e_j`, with the short roots `e_i, e_j` in their span, force
     the nonzero coordinates of `λ` to have equal absolute values. Up to `W(B_4)`,
     `λ = (1^k, 0^(4−k))` with `k ∈ {1, 2, 3, 4}`.
   - Each fails on an explicit pair:
     - `k = 1`: `(e_1+e_2, ½(1,−1,1,1))` gives `∝ (0,2,−1,−1)`;
     - `k = 2`: `(e_1+e_3, e_1+e_2)` gives `(1,−1,2,0)`;
     - `k = 3`: `(e_1+e_4, e_1+e_2)` gives `(1,−1,0,2)`;
     - `k = 4`: `(e_1, ½(1,1,1,1))` gives `∝ (3,−1,−1,−1)`.
   - None of these is proportional to a root. So `L(F_4)` is not supersolvable, and
     neither is `P(A_(F_4))`.

These conclusions agree with the classification of supersolvable Coxeter arrangements
(types A_n, B_n and rank at most 2; Barcelo--Ihrig 1999). That classification is not
used here: the D_4 and F_4 computations above replace it.

## Conclusion

Steps 1–2 give part 1 of the target. The positive checks in Step 1, together with
Fadell--Neuwirth for A_n (configurations of distinct points in `C^×`, modulo the
diagonal), give part 2. ∎
