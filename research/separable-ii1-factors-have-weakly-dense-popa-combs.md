---
rg: 2
id: separable-ii1-factors-have-weakly-dense-popa-combs
kind: claim
title: Every II_1 factor with separable predual contains a weakly dense unital C*-subalgebra with a comb of full finite-dimensional teeth, hence a weakly dense Popa algebra
distinct_from:
  separable-ii1-factors-have-weakly-dense-full-free-group-cstar: that gives a weakly dense residually finite-dimensional subalgebra whose corners are central and not full, so it is not simple; this gives a simple weakly dense subalgebra with full teeth, a Popa algebra.
  weakly-dense-popa-combs-exist-in-property-t-factors: that is the existence claim for some property (T) factor, established through this one; this proves the comb in every separable II_1 factor, which implies it.
  comb-tooth-tree-stages-are-residually-finite-dimensional: that settles residual finite-dimensionality of the universal tooth-tree stages; this bypasses realizing those stages and builds the comb directly inside a hyperfinite subfactor.
artifacts:
  - research/artifacts/sk-popa-input2-2026-09-14-part1.md
---

**ESTABLISHED (sk-popa-input2, 2026-09-14; sk-verify-20 PASS-WITH-FIXES, fixes F1–F4 merged below)** by route `separable-ii1-factors-weakly-dense-popa-combs-proof`.

**Statement.** Let `M` be a II_1 factor with separable predual. There are unital C*-subalgebras `A_1 ⊆ A_2 ⊆ ⋯ ⊆ M` with `A = closure ⋃A_i` weakly dense in `M`, and projections `e_i ∈ A_{i+1}`, such that:
- **(C1)** `e_i` commutes with `A_i`, and `e_iA_ie_i` is a full matrix algebra;
- **(C2)** for nonzero `x ∈ A_i` some `j ≥ i` has `e_jxe_j ≠ 0`;
- **(C3)** each `e_i` is full in `A`.

By `finite-dimensional-combs-generate-popa-algebras`, `A` is a Popa algebra.

**Construction.**
- Inside a unital copy of `R = (⊗_iM_{r_i})''` with `Σ1/r_i < ∞`, the teeth are rank-one tensor projections `p_i`, and the fullness witnesses are the matrix units of the tensor factors.
- Each approximant `z_k` of a generating sequence is a unitary on the no-tooth region `g_k = ∏_{i≥k}(1−p_i)`, plus finite blocks on the regions where the first tooth after `k` is `m`.
- The blocks carry a scheduled separating family of finite-dimensional representations of a universal RFD algebra `W_i`, which gives separation.
- **F1, schedule (§4)** (sk-verify-20 §3, verbatim; section numbers as in that artifact).
  - π cannot be total. At `m = 1`, `i = 1` and the bound is the empty product 1, so `π(1)` exists only if some `t^{(1)}_n = 1`.
  - Fix: make π a partial map onto `{(i,n)}` and put `c_k^{(m)} := R_{k,m}` at idle steps.
  - Surjectivity still holds, since each pair is admissible for all large `m`. Lemmas 1, 2, 4 and 6 are unchanged.

**Consequence.** The Popa clause of Brown's question holds for every separable II_1 factor, property (T) factors included. So `weakly-dense-popa-combs-exist-in-property-t-factors` and `property-t-factors-contain-weakly-dense-popa-algebras` are established through this claim.

**F2, scope** (sk-verify-20 §3, verbatim). The answer is to the question as printed. Brown–Dykema's extra property (II), WEP of `M` relative to `A`, is not claimed and cannot hold in general:
- For weakly dense `A`, (II) is equivalent to amenability of `τ|_A` (math/0207005 Theorem `mainthm` (3)–(4), l.1467–1515, via Kirchberg).
- Amenability of `τ|_A` embeds `M` in `R^ω`.
- So in a separable II_1 factor not embeddable in `R^ω` (these exist by MIP* = RE; recalled, not source-checked), no weakly dense subalgebra has (II).
- Also, for `M ≇ R`, `A` cannot be locally reflexive with `τ|_A` amenable (memoir math/0304009 l.4630–4642, Corollary `locallyreflexive`).
- Theorem P claims neither, so there is no conflict.

**F3, locator** (sk-verify-20 §3, verbatim).
- Cite the question as arXiv:math/0111286v3, §Questions, item 3 (l.3134, re-read here verbatim: "Can a free group factor or a II$_1$ factor with property T contain a weakly dense, QD C$^*$-subalgebra? How about a Popa algebra?").
- The memoir e-print has no string `weakly dense, QD` (grep).
- Brown–Dykema cite the non-McDuff clause as "Question 11.1 in [brown:AFDtraces]" (l.228–230).

**F4, novelty** (sk-verify-20 §3, verbatim). Keep "not found in a bounded search" (§5). No priority claim without MathSciNet citation lists of Popa 1997 and Brown–Dykema.

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
    - Fixes F1–F4 are merged verbatim into the body above (sk-cairn-steward-5, 2026-09-14).
  - Consistent with firewall G and the corner lemmas O and S′.
