---
rg: 2
id: comb-tooth-tree-stages-rfd-via-li-shen
kind: route
title: The comb stages are RFD by Li–Shen Theorem 2 with matched multiplicities, then Exel–Loring for the free unitary
target: comb-tooth-tree-stages-are-residually-finite-dimensional
requires:
  - li-shen-amalgamated-rfd-criterion
  - exel-loring-free-products-of-rfd-algebras-are-rfd
artifacts:
  - research/artifacts/sk-rfd-amalgam-2026-09-14-part1.md
---

Notation as in the target: `V = U ⊕ M_d`, `e = (0,1)`, and `p ∈ M_r` of rank one with `r ≥ 2`, amalgamated over `C²` by `(0,1) ↦ e`, `(0,1) ↦ p`. Both maps `C² → V` and `C² → M_r` are unital embeddings, since `U ≠ 0` and `r ≥ 2`.

**Step 1: compatible embeddings.** `U` is separable and RFD, so it has a separating sequence of unital finite-dimensional representations `ρ_n: U → M_{D_n}`. Put `k_n = r·d·D_n` and `C^{k_n} = C^{(r−1)dD_n} ⊕ C^{dD_n}`.
- `q_1(u,m)_n = ρ_n(u)^{⊕(r−1)d} ⊕ (m ⊗ 1_{D_n})`. This is a unital *-homomorphism `V → M_{k_n}`, and `q_1: V → ∏_n M_{k_n}` is injective: `(u,m) ↦ 0` forces `ρ_n(u) = 0` for all `n`, so `u = 0`, and `m ⊗ 1 = 0`, so `m = 0`.
- `q_1(e)_n` is the projection onto the second summand, of rank `dD_n`, and `q_1(1−e)_n` projects onto the first, of rank `(r−1)dD_n`.
- `x ⊗ 1_{dD_n}` on `C^r ⊗ C^{dD_n}` makes `p ⊗ 1` and `(1−p) ⊗ 1` of ranks `dD_n` and `(r−1)dD_n`. Choose a unitary `W_n: C^r ⊗ C^{dD_n} → C^{k_n}` carrying `p ⊗ 1` onto the second summand and `(1−p) ⊗ 1` onto the first, and put `q_2(x)_n = W_n(x ⊗ 1)W_n^*`. This is unital, and injective since `M_r` is simple.
- So `q_1∘ψ_V = q_2∘ψ_{M_r}` on `C²`, coordinatewise.

**Step 2: amalgamated product.** `V` and `M_r` are separable and unital, and `C²` is finite-dimensional. By `li-shen-amalgamated-rfd-criterion` (Li–Shen Theorem 2), `V *_{C²} M_r` is RFD.

**Step 3: free unitary.** `C(T)` is commutative, hence RFD. By `exel-loring-free-products-of-rfd-algebras-are-rfd`, `(V *_{C²} M_r) *_C C(T)` is RFD.

**Step 4: rank ratio.** Every finite-dimensional representation of `M_r` is a multiple of the identity representation, so `rank(p) = dim/r`. Since `e = p` in the amalgamated product, `rank(e) : rank(1−e) = 1 : r−1` in every finite-dimensional representation.

**Step 5: extension.** Let `σ: V → B(H)` be finite-dimensional with `dim σ(1−e) = (r−1)·dim σ(e)`. Then `dim H = r·dim σ(e)`, so there are matrix units of `M_r` on `H` with `p ↦ σ(e)`. By the universal property of the full amalgamated free product, `σ` and this representation of `M_r` define a representation of `V *_{C²} M_r`. Any unitary on `H` extends it to `U^+`. Conversely, Step 4 forces the dimension equality.

**Induction.** If `U_1` is separable and RFD, each `U_{i+1} = ((U_i ⊕ M_{d_i}) *_{C²} M_{r_i}) * C(T)` is separable, unital and RFD.

**Model tests.**
- `U = C`, `d = 1`, `r = 2`: `V = C ⊕ C`, and `(C⊕C) *_{C²} M_2 ≅ M_2`, which is RFD.
- A hypothesis fails in Li–Shen Example 1 (a single irreducible representation per factor, forced ratios 1/2 and 1/3), which is not RFD. Our construction needs two independent multiplicities, which `V = U ⊕ M_d` provides.
