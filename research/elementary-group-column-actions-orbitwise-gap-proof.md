---
rg: 2
id: elementary-group-column-actions-orbitwise-gap-proof
kind: route
title: Fixed sets of additive maps are subgroups, root-subgroup orbits are cosets, and a swap-counting argument finds one orbit point whose whole span is fixed
target: elementary-group-column-actions-have-orbitwise-gap
requires: []
artifacts:
  - research/artifacts/elementary-orbitwise-gap-any-finite-ring-2026-09-16.md
---

Direct proof, from the definitions only. Artifact §2 has the same proof with remarks.

**Notation.**
- `𝒜` is a unital ring, `W` a finite unital left `𝒜`-module (`1·w = w`, used in step 4), `n ≥ 2`, and `V = W^n`.
- `EL_n(𝒜) ≤ H ≤ GL_n(𝒜)`, `O` is an `H`-orbit, and `g : V → V` is additive.
- For `w ∈ W`, `w e_i` is the column with `w` in coordinate `i` and `0` elsewhere. For `S ⊆ W`, `S e_i = {w e_i : w ∈ S}`.
- `𝒜w = {aw : a ∈ 𝒜}`, an additive subgroup of `W`, and `L(x) = Σ_j 𝒜x_j`.
- `P = {v ∈ V : gv = v} = ker(g − id)` is an additive subgroup of `V`.
- `m = |O ∖ P|`, and we assume `m < |O|/(2n²)`.

**Proof.**

1. **Root cosets.** Fix `i ≠ j`. Since `E_ij² = 0`, `T_ij = {e_ij(a) : a ∈ 𝒜}` is a subgroup of `EL_n(𝒜) ≤ H`.
   - For `x ∈ V`, `e_ij(a)x = x + (a x_j) e_i`, so the `T_ij`-orbit of `x` is the coset `x + (𝒜x_j) e_i`.
   - `O` is `H`-invariant, so it is a disjoint union of `T_ij`-orbits.

2. **Coset lemma.** Let `S ≤ V` be a subgroup and `C = y + S` with `C ⊄ P`. Then `|C ∖ P| ≥ |C|/2`.
   - If `C ∩ P = ∅` this is clear.
   - Otherwise pick `p ∈ C ∩ P`. Then `C = p + S` and `C ∩ P = p + (S ∩ P)`, because `P` is a subgroup containing `p`.
   - `C ⊄ P` forces `S ⊄ P`, so `S ∩ P` has index at least `2` in `S`, and `|C ∩ P| ≤ |S|/2 = |C|/2`.

3. **Bad sets.** Let `B_ij ⊆ O` be the union of the `T_ij`-orbits in `O` that are not contained in `P`.
   - By step 2, `|B_ij| ≤ 2|B_ij ∖ P| ≤ 2m`.
   - If `x ∈ O ∖ B_ij`, then `x + (𝒜x_j) e_i ⊆ P`. Since `x ∈ P` and `P` is a subgroup, `(𝒜x_j) e_i ⊆ P`.

4. **Diagonal positions.** For `i ≠ j` put `s_ij = e_ij(1) e_ji(−1) e_ij(1) ∈ EL_n(𝒜) ≤ H`.
   - Applied to `x`, the three factors act from right to left.
     - First `x_i ↦ x_i + x_j`.
     - Then `x_j ↦ x_j − (x_i + x_j) = −x_i`.
     - Then `x_i + x_j ↦ (x_i + x_j) + (−x_i) = x_j`.
   - So `(s_ij x)_i = x_j`, `(s_ij x)_j = −x_i`, and the other coordinates are unchanged.
   - `s_ij` permutes `O`. Put `D_ij = s_ij^(−1)(B_ji)`, so `|D_ij| = |B_ji| ≤ 2m`.
   - If `x ∈ O ∖ D_ij`, then `z = s_ij x ∈ O ∖ B_ji`. Step 3 for the pair `(j,i)` gives `(𝒜z_i) e_j ⊆ P`, that is
     `(𝒜x_j) e_j ⊆ P`.

5. **Counting.** For each `j` choose `i(j) ≠ j`, which is possible because `n ≥ 2`. Put
   `E = ⋃_(i≠j) B_ij ∪ ⋃_j D_(i(j) j)`.
   - This is a union of `n(n−1) + n = n²` sets of size at most `2m`, so `|E| ≤ 2n²m < |O|`.
   - So some `x ∈ O ∖ E` exists. For this `x`, `(𝒜x_j) e_k ⊆ P` for all `j` and `k`:
     - for `k ≠ j` by step 3, since `x ∉ B_kj`;
     - for `k = j` by step 4, since `x ∉ D_(i(j) j)`.

6. **Conclusion.**
   - `P` is a subgroup, so `P ⊇ Σ_(j,k) (𝒜x_j) e_k = L(x)^n`.
   - Every `y ∈ O` is `y = hx` with `h ∈ H ⊆ M_n(𝒜)`, so `y_k = Σ_j h_(kj) x_j ∈ L(x)` for every `k`.
   - Hence `O ⊆ L(x)^n ⊆ P`, and `g` fixes `O` pointwise. ∎

**Orbitwise gap.**
- Every element of the image of `H` in `Sym(V)` is additive, so by the theorem it either fixes an orbit `O` pointwise
  or has `|Fix ∩ O| ≤ (1 − 1/(2n²))|O|`.
- For an `H`-invariant `Z ⊆ V`, the orbits of `H|_Z` are the `H`-orbits in `Z`, and each element acts on them as
  before. So the gap is kept.

**What is used.**
- Additivity of `g`: `P` is a subgroup, in steps 2, 3 and 6.
- `T_ij ≤ H` for all `i ≠ j`, hence `s_ij ∈ H`: steps 1, 3 and 4.
- `H ⊆ M_n(𝒜)`: step 6.
- Finiteness only through `|O| < ∞`.

No commutativity, semisimplicity or finiteness of `𝒜` is used.
