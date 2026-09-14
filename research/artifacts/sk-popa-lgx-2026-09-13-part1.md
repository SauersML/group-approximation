# sk-popa-lgx part 1: rigidity of Popa corners, combs, and where the Popa clause stands for property (T) factors (2026-09-13)

Lane sk-popa-lgx. The problem is the Popa clause of Brown's Question 3 for property (T) factors, `property-t-factors-contain-weakly-dense-popa-algebras`. Plan: `research/artifacts/sk-popa-lgx-plan-2026-09-13.md`. Sources were read on MSI: `/scratch.global/sauer354/sk/sk-popa-lgx/{math_0111286,math_0207005,math_0304009}/src`.

## 0. Verdict
- **O, ESTABLISHED (unreviewed).** `kazhdan-generators-admit-no-norm-popa-corners`. In `L(Γ)`, for `Γ` infinite with Kazhdan pair `(S,ε)`, no finite-dimensional corner satisfies `max_s(‖[λ_s,p]‖ + dist(pλ_sp,B)) < ε/2`. So every C*-subalgebra with local quantization satisfies `max_s dist(λ_s, A) ≥ ε/6`. The proof is scale-free: normalized canonical vectors in the coarse bimodule.
- **S′, ESTABLISHED (unreviewed).** `orthogonal-popa-corners-for-kazhdan-approximants-small-trace`. Orthogonal Popa corners for 2-norm approximants `y_s`, at tolerance `η < ε/4`, have total trace `≤ 2(ε−4η)^{-2}Σ_s(‖a_sP‖_2² + ‖Pa_s‖_2²)`, where `a_s = λ_s − y_s`. On each corner the approximants are relatively bad: `‖a_sp‖_2 + ‖pa_s‖_2 ≥ (ε−4η)τ(p)^{1/2}`. This improves Lemma S (sk-free-5): no `η²` term, and orthogonal families are covered.
- **K, ESTABLISHED (unreviewed).** `finite-dimensional-combs-generate-popa-algebras`. An increasing union with a comb of full, commuting, simple finite-dimensional teeth that separate points is a Popa algebra. This reduces the Popa clause to building a weakly dense comb.
- **G, dead mechanism (§2).** Inductive limits whose connecting maps commute with matrix units on corners of trace → 1 give Gamma factors. Brown's basic construction and its unitary twists therefore never reach property (T).
- **OPEN.** `weakly-dense-popa-combs-exist-in-property-t-factors`, wired into the Popa clause by route `property-t-factor-popa-algebras-via-weakly-dense-combs`. The tooth-tree plan and its three missing inputs are in §3.

## 1. The two corner lemmas: the idea
- **Old route (Lemma S).** It measured almost-commutation in `L²(M) ⊖ C` through the spectral gap of the conjugation representation, so the corner's trace entered the estimate.
- **Here.** For a finite-dimensional corner `(p, B)` take `ζ = Σ_r τ(p_r)^{-1/2}Σ_{ij} ê^r_{ij} ⊗ ê^r_{ji} ∈ L²M ⊗ L²M`. Then:
  - `ζ` commutes exactly with `B`;
  - `‖ζ‖² = τ(p)`;
  - `‖aζ‖ = ‖ap‖_2` and `‖ζa‖ = ‖pa‖_2` exactly;
  - the conjugation representation of `Γ` on `ℓ²(Γ×Γ)` comes from the free action `(h,k) ↦ (gh, kg^{-1})`, so it is a multiple of the regular representation and has no invariant vectors.
- **Consequences.** A Kazhdan pair forces `max_s‖λ_sζ − ζλ_s‖ ≥ ε‖ζ‖`. With `‖yζ − ζy‖ ≤ 2(‖[y,p]‖ + dist(pyp,B))‖ζ‖`, this gives O at once and S′ after transfer. Full proofs are in the routes.
- **Popa algebras in `L(Γ)`:**
  - their local quantization corners never serve exact Kazhdan generators, by O;
  - for Kaplansky approximants the 2-norm defect must sit on the corners, and orthogonal families of corners carry total trace `O(δ²)`, by S′.

## 2. Dead mechanism G: Brown-type inductive limits give property Gamma
**Setting.** `A = lim(A_i, ρ_i)` with a tracial state `γ`. Suppose that for each `i` there are a projection `q_i ∈ A_{i+1}` and matrix units `{f^i_{ab}}_{a,b ≤ n_i} ⊆ q_iA_{i+1}q_i`, `n_i ≥ 2`, with `Σ_af^i_{aa} = q_i`, such that:
- `ρ_i(A_i)` commutes with `q_i`;
- `q_iρ_i(A_i)q_i` commutes with every `f^i_{ab}`;
- `γ(1 − q_i) → 0`.

**Claim.** `π_γ(A)''` has property Gamma. In particular it is not a property (T) factor.

**Proof.**
1. Put `ω = e^{2πi/n_i}` and `v_i = Σ_aω^af^i_{aa} + (1 − q_i)`, a unitary in `A_{i+1}`.
2. For `x ∈ A_j` with `j ≤ i`, the image `x_{i+1}` of `x` in `A_{i+1}` equals `q_ix_{i+1}q_i + (1−q_i)x_{i+1}(1−q_i)`, since it commutes with `q_i`. So `v_i` commutes exactly with `x_{i+1}`.
3. The `f^i_{aa}` are equivalent, so `γ(f^i_{aa}) = γ(q_i)/n_i`. Hence `γ(v_i) = γ(1−q_i) → 0` and `‖v_i − γ(v_i)‖_2² = 1 − |γ(v_i)|² → 1`.
4. `⋃_jA_j` is 2-norm dense in `π_γ(A)''` and `‖v_i‖ = 1`, so `‖[v_i, x]‖_2 → 0` for every `x ∈ π_γ(A)''`.
5. So `(v_i)` is a nontrivial central sequence and `π_γ(A)''` has property Gamma.
6. **Property (T) excludes Gamma.** A central sequence gives almost central unit vectors `(v_i − γ(v_i))/‖·‖_2` in the bimodule `L²(M) ⊖ C`. That bimodule has no nonzero central vector for a factor, which contradicts (T) in the Connes–Jones form. The definition is recalled, not re-read. ∎

**Brown's construction** (math/0111286 l.905ff) has connecting maps `x ↦ 1_E⊗diag(0_{n−k}, π(x)) + x⊗diag(1_{n−k}, 0_k)`. Take `q = 1⊗diag(1_{n−k},0)` and matrix units from `M_{n−k}`; the trace of `1−q` is `k/n → 0`. Conjugating the maps by unitaries `u ∈ A_{i+1}` transports `q` and `f` along. This is consistent with Brown's own remark that "Our constructions always give McDuff factors".

**Why combs escape G.** The teeth `e_i` of a comb commute with `A_i`, but their trace tends to `0`. So `e_i − τ(e_i)` has 2-norm `→ 0` and gives only trivial central sequences.

## 3. Positive plan: a tooth tree realizing a comb in a separable II_1 factor
Notation: `M` is the target factor, `(y_k)` a generating sequence each repeated infinitely often, `W_i ⊇ W_{i+1}` shrinking tooth regions with `τ(W_i) → 0`, and `g_i = 1 − W_i`.

**Stage `i → i+1`**, abstractly:
- **Tooth.** `V_i = U_i ⊕ M_{d_i}` with `e_i = (0,1)` and compression `π_i`, an irreducible finite-dimensional representation of `U_i`.
- **Fullness.** Identify `e_i` with a minimal projection of `M_{r_i}`. Its translates `w_i^le_iw_i^{-l}`, `l < r_i`, are orthogonal and sum to `1`. Take `r_i = 1/τ(e_i)`, which the trace inequality forces up to a constant.
- **Approximant.** A free unitary `z_{i+1}`.
- **Result.** `U_{i+1} = (V_i *_{C²} M_{r_i}) * C(T)`.

**Realization in `M`.**
- Big parts on `g_{i+1}` approximate `y_{κ(i+1)}` in 2-norm, as in T1.
- The own region of `e_i` (the part of `e_i` outside later teeth) is translated by `w_i` into `g_{i+1}`.
- Each later tooth `e_j` (`j > i`) carries a finite-dimensional representation `σ_j` of `U_j`. All generators introduced up to stage `j` act block-diagonally on `e_j` through `σ_j`.
- Consistency on overlaps `e_j ∧ e_i = 1_{M_{d_i}} ⊗ f′` is automatic from the relation `e_iU_ie_i = π_i(U_i)`.
- If the `σ_j` are norming for each `U_i`, the realization is faithful on `U_i`. So `A_i ≅ U_i` and (C2) holds; (C1) and (C3) hold by the relations.
- The simplicity, QD and local quantization of `A` then follow from K.

**Missing inputs, in order of risk.**
1. **RFD of `U_{i+1}`.** A full amalgamated free product over `C²` of an RFD algebra with `M_{r_i}` must be residually finite-dimensional, with representations in which `rank e : rank(1−e) = 1 : r_i − 1`. Brown–Dykema `thm:rfd` covers `M_n *_D M_{n′}` with trace-compatible embeddings. The general RFD case over finite-dimensional amalgams was not located at source.
2. **Extension across stages.** Tail representations of `U_i` chosen at stage `i` must extend to `U_j` for all `j > i`. Since each later stage only adds generators and the relations above, this reduces to 1 plus multiplicities.
3. **Exact translate relations in `M`.** `w_i` must commute with every later tooth. So later teeth are unions of `w_i`-translates, which is compatible with the traces but has to be scheduled.

**Status.** Unfinished. No step fails. The scale conditions of O and S′ are necessary and are respected by the plan, because the teeth have trace `→ 0`.

## 4. Bounded novelty and credit
- **Read at source:**
  - Brown math/0111286: §Questions item 3; `thm:basicconstruction` l.872ff; `thm:arbitraryMcDuff` l.2741.
  - Brown–Dykema math/0207005: introduction; `thm:rfd` l.409ff; `thm:RBR` l.557ff.
  - Brown's memoir math/0304009, grep for Popa's questions: l.373, l.4315 and l.6076 concern unique traces, not this clause.
- **Corner lemmas O and S′.** The coarse-bimodule canonical vector is the standard tool behind "property (T) factors are not approximately finite-dimensional". I found no statement for Popa corners. The novelty search here was the main grep plus the sources above; earlier web searches are in sk-free-5 part 1 §5.
- **K is elementary and likely folklore.** No priority is claimed.
- **G.** Brown remarks that his constructions give McDuff factors. G shows the same holds for all unitary twists; no priority is claimed.
