---
rg: 2
id: weakly-dense-popa-combs-exist-in-property-t-factors
kind: claim
title: Some II_1 factor with property (T), for instance L(G_X), contains a weakly dense unital C*-subalgebra with a comb of full finite-dimensional teeth
distinct_from:
  property-t-factors-contain-weakly-dense-popa-algebras: that asks for a weakly dense Popa algebra; this asks for the stronger, concrete comb structure, which gives one by finite-dimensional-combs-generate-popa-algebras.
  separable-ii1-factors-have-weakly-dense-full-free-group-cstar: that gives weakly dense RFD subalgebras with central, non-full corners; this asks for corners inside the algebra that are full and do not commute with later stages.
artifacts:
  - research/artifacts/sk-popa-lgx-2026-09-13-part1.md
---

**OPEN (sk-popa-lgx, 2026-09-13).** In the notation of `finite-dimensional-combs-generate-popa-algebras`, the claim is: there are a II_1 factor `M` with property (T) and a weakly dense unital C*-subalgebra `A = closure ⋃A_i ⊆ M` with a comb `(e_i)`.

**Necessary scale conditions** (established, unreviewed; see the artifact):
- in `M = L(Γ)` with Kazhdan pair `(S,ε)`, `τ(e_j) ≤ 4|S|ε^{-2}dist_2(λ(S),A_j)²` (`orthogonal-popa-corners-for-kazhdan-approximants-small-trace`), so the teeth vanish;
- `max_s dist(λ_s, A) ≥ ε/6` in norm (`kazhdan-generators-admit-no-norm-popa-corners`);
- any fullness witness has `Σ_l‖v_l‖² ≥ 1/τ(e_i)`.

## Attempts
- **Tooth tree with universal stages** (sk-popa-lgx, artifact part 1 §3). The plan, where it stands, and what is missing:
  - *Stages.* `U_{i+1} = ((U_i ⊕ M_{d_i}) *_{C²} M_{r_i}) * C(T)`:
    - the tooth `e_i = (0,1)` carries the compression `π_i`;
    - it is identified with a minimal projection of `M_{r_i}`, whose translates give fullness, with `r_i = 1/τ(e_i)`;
    - `C(T)` adds a free unitary approximant.
  - *Realization.* Realize `U_{i+1}` in `M` with big parts approximating a generating sequence on the complement of a shrinking tooth region. The tails of later teeth carry norming finite-dimensional representations of `U_j`, so `A_i ≅ U_i` and (C2) holds.
  - *Missing input 1:* residual finite-dimensionality of `U_{i+1}`. That is a full amalgamated free product over `C²` of an RFD algebra with a matrix algebra, with trace-compatible ranks `rank(e) : rank(1−e) = 1 : r_i − 1`. Brown–Dykema `thm:rfd` (arXiv:math/0207005) covers only `M_n *_D M_{n′}`.
    - **SETTLED (sk-rfd-amalgam, 2026-09-14; unreviewed)** by `comb-tooth-tree-stages-are-residually-finite-dimensional`.
    - Li–Shen Theorem 2 (Illinois J. Math. 56 (2012), p. 657, read at source): `A *_D B` is RFD iff `A` and `B` embed unitally in one product ∏M_{k_n} compatibly on `D`.
    - `V_i = U_i ⊕ M_{d_i}` carries independent multiplicities on its two summands, so the forced ratio `1/r_i` is reachable. By Exel–Loring, the free unitary keeps RFD.
    - A finite-dimensional representation of `V_i` extends to `U_{i+1}` iff `dim(1−e_i) = (r_i − 1)·dim(e_i)`. So missing input 2 reduces to scheduling these multiplicities consistently inside `M`.
  - *Missing input 2:* compatibility across stages. The tail representations of `U_i` chosen at stage `i` must extend to representations of all later `U_j` with the forced multiplicities.
  - *Missing input 3:* exact realization in `M` of the translate relations for `e_i` commuting with all later teeth. This forces later teeth to be invariant under the translating unitary.
  - Dies nowhere yet. It is unfinished.
- **Brown's basic construction and all its unitary twists: dead for property (T)** (artifact part 1 §2).
  - Suppose the connecting maps commute exactly with a matrix-unit system `{f^i_{ab}} ⊆ M_{n_i}`, `n_i ≥ 2`, on a projection `q_i` with `γ(1−q_i) → 0`. Then `v_i = Σ_aω^af^i_{aa} + (1−q_i)` is an exactly central sequence of unitaries with `‖v_i − γ(v_i)‖_2 → 1`, and every weak closure `π_γ(A)''` has property Gamma.
  - Brown's maps `x ↦ 1⊗diag(0,π(x)) + x⊗diag(1_{n−k},0)` are of this kind, and so are their conjugates by unitaries. A (T) factor has no property Gamma, so this mechanism cannot reach it.
  - Teeth of trace `→ 0` do not create central sequences, which is why the comb criterion is not blocked by this.
- **Tensor teeth in a hyperfinite subfactor (sk-popa-input2, 2026-09-14; unreviewed): a complete route.** Artifact `research/artifacts/sk-popa-input2-2026-09-14-part1.md`, claim `separable-ii1-factors-have-weakly-dense-popa-combs`, and route `weakly-dense-popa-combs-in-t-factors-from-separable-factors` into this node.
  - *Inputs 2–3 are bypassed, not scheduled inside universal stages.* The teeth `e_i = p_i` are rank-one tensor projections of `R = (⊗N_i)'' ⊆ M` with `Σ1/r_i < ∞`, and the fullness witnesses are the matrix units of `N_i`.
  - *Approximants.* `z_k` is a unitary on the no-tooth region `g_k = ∏_{i≥k}(1−p_i)` approximating a generating sequence, plus finite blocks `c_k^{(m)}` on the first-tooth regions `R_{k,m}`. So `z_k` commutes with every later tooth, and `e_jA_je_j = (⊗_{i<j}N_i)p_j`.
  - *Separation.* It goes through the universal RFD algebra `W_i = C*⟨M_{D_i}, v_k corner unitaries⟩` (Li–Shen, Exel–Loring). Scheduled blocks carry a separating family of its finite-dimensional representations, so `A_i ≅ W_i`.
  - *Status.* If this passes review, the claim holds for every separable II_1 factor, and this node can be marked established.
