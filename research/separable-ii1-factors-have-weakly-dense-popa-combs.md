---
rg: 2
id: separable-ii1-factors-have-weakly-dense-popa-combs
kind: claim
title: Every II_1 factor with separable predual contains a weakly dense unital C*-subalgebra with a comb of full finite-dimensional teeth, hence a weakly dense Popa algebra
distinct_from:
  separable-ii1-factors-have-weakly-dense-full-free-group-cstar: that gives a weakly dense residually finite-dimensional subalgebra whose corners are central and not full, so it is not simple; this gives a simple weakly dense subalgebra with full teeth, a Popa algebra.
  weakly-dense-popa-combs-exist-in-property-t-factors: that is the open existence claim for some property (T) factor; this proves the comb in every separable II_1 factor, which implies it.
  comb-tooth-tree-stages-are-residually-finite-dimensional: that settles residual finite-dimensionality of the universal tooth-tree stages; this bypasses realizing those stages and builds the comb directly inside a hyperfinite subfactor.
artifacts:
  - research/artifacts/sk-popa-input2-2026-09-14-part1.md
---

**ESTABLISHED (unreviewed, sk-popa-input2, 2026-09-14)** by route `separable-ii1-factors-weakly-dense-popa-combs-proof`.

**Statement.** Let `M` be a II_1 factor with separable predual. There are unital C*-subalgebras `A_1 ⊆ A_2 ⊆ ⋯ ⊆ M` with `A = closure ⋃A_i` weakly dense in `M`, and projections `e_i ∈ A_{i+1}`, such that:
- **(C1)** `e_i` commutes with `A_i`, and `e_iA_ie_i` is a full matrix algebra;
- **(C2)** for nonzero `x ∈ A_i` some `j ≥ i` has `e_jxe_j ≠ 0`;
- **(C3)** each `e_i` is full in `A`.

By `finite-dimensional-combs-generate-popa-algebras`, `A` is a Popa algebra.

**Construction.**
- Inside a unital copy of `R = (⊗_iM_{r_i})''` with `Σ1/r_i < ∞`, the teeth are rank-one tensor projections `p_i`, and the fullness witnesses are the matrix units of the tensor factors.
- Each approximant `z_k` of a generating sequence is a unitary on the no-tooth region `g_k = ∏_{i≥k}(1−p_i)`, plus finite blocks on the regions where the first tooth after `k` is `m`.
- The blocks carry a scheduled separating family of finite-dimensional representations of a universal RFD algebra `W_i`, which gives separation.

**Consequence.** The Popa clause of Brown 2001 Question 3 holds for every separable II_1 factor, property (T) factors included.

**Model tests** (artifact §6):
- `M = R` gives a Popa algebra;
- with `Σ1/r_i = ∞` the approximants collapse into `R`;
- with trivial blocks separation fails;
- the Gamma firewall of sk-popa-lgx §2 and the Kazhdan corner constraints are not violated.

## Review
- **sk-verify-20 PASS-WITH-FIXES (2026-09-14, `research/artifacts/sk-verify-20-2026-09-14-part1.md`).**
  - **Re-derived by hand:**
    - the commutation lemma, (C1) and (C3);
    - the bound `‖z_k − y'_k‖_2 ≤ 4τ(1−g_k)^{1/2}`, from `g_k − x_k^*x_k = |(1−g_k)y'_kg_k|²` and `(1−t)² ≤ 1−t²`;
    - the splitting `1−b_k = Σ_{k≤m<i}R_{k,m}`;
    - the Li–Shen and Exel–Loring induction for `W_i`: the universal property of the amalgam, `0 < τ(b_k) < 1`, and compatible unital embeddings;
    - the reducing subspace `ℂ^{D_i}⊗ℂ^t` of the separation lemma and the norm chain that makes `q` isometric;
    - the comb criterion: simplicity and local quantization.
  - **Fixes:**
    - (F1) the schedule of §4 must be a partial map, with `c_k^{(m)} = R_{k,m}` at idle steps (at `m = 1` the dimension bound is 1);
    - (F2) scope: Brown–Dykema's relative WEP is not claimed, and it cannot hold in factors not embeddable in `R^ω`;
    - (F3) cite Brown's question as arXiv:math/0111286v3, §Questions, item 3;
    - (F4) the novelty wording stays "not found in a bounded search".
  - Consistent with firewall G and the corner lemmas O and S′.
