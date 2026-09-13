# Review of swarm 6: analysis, soficity and C*-algebra claims landed after 17:00

Lane `swarm6-reviewer-analysis`, 2026-09-12 (swarm 7). This is an adversarial review of
the ESTABLISHED claims that swarm 6 landed after about 17:00 in analysis, soficity
and C*-algebras. The tip read was b04b42d61.

Verdicts:
- **PASS:** correct as stated.
- **GAP:** a missing step or an overstatement that this review does not fill.
- **FAIL:** false, or the proof does not work.

A citation is marked "source re-read" only when this lane read the statement from
the paper itself.

**Skipped, because a verdict already exists** (in
`research/artifacts/review-swarm4-2026-09-12.md` unless noted):
- §35.1 `leavitt-pair-vertex-rounding-is-nonhyperlinearity`;
- §35.2 `kazhdan-rank-rounding-fails-over-every-field`;
- §38.2 `kazhdan-kernel-isotypic-sectors-extend-within-kernel-closure`;
- §38.3 `bounded-multiplicity-kazhdan-sectors-miss-leavitt-cover-defect`;
- §38.4, the UCT and Cartan claims of 2558a1877;
- §29.5 `o2-zp-cartan-fixing-iff-rokhlin-uct-ascent`;
- §34.1 `gardella-rokhlin-actions-preserve-uct`;
- §34.4, the Sp(2,1) claims of c48a38ab6;
- §21, Thompson's V and the Cuntz groupoid;
- §31, the flexible HS claims;
- §12 of `research/artifacts/review-swarm5-2026-09-12.md`, the stw01 claim.

This lane's own line-by-line reading of the first four agreed with those verdicts
before they landed.

---

## 1. `ultrapower-comparison-with-rank-density-divides-projections`: PASS

Route: `ultrapower-comparison-rank-density-division-proof`, artifact
`research/artifacts/tw-invisible-gamma-support-gap-2026-09-12.md` §3. No
literature is imported. Every step was re-derived here.

- **Step 1 (represent).**
  - A projection `p ∈ M_k(A^U)` lifts to positive contractions `p_m`.
  - By Cauchy–Schwarz, `sup_τ τ(p_m − p_m²)` is bounded by a multiple of the uniform
    2-norm of `p_m − p_m²`, and that norm tends to 0.
  - Correct.
- **Step 2 (select).**
  - `τ ↦ τ(p_m)/n` is continuous and affine with values in `[0, k/n] ⊆ [0, k]`, so
    RD_b applies.
  - For a positive contraction, `0 ≤ b − b² ≤ 1` gives `τ((b − b²)²) ≤ τ(b − b²)`. So
    `(b_m)` has vanishing uniform 2-norm defect, and `e'` is a projection.
  - For a limit trace `σ = lim_U τ_m`, `σ(e') = lim_U τ_m(p_m)/n = σ(p)/n`.
  - Correct.
- **Step 3 (peel).** For `j ≤ n − 2`, the projection `p − (e_1 + … + e_j)` has
  profile `(n − j)σ(e') ≥ σ(e')` on every limit trace. So PC gives a subprojection
  `e_(j+1) ~ e'`. Correct.
- **Step 4 (remainder).**
  - `r = p − Σ_(i<n) e_i` has profile `σ(e')`. PC gives `w` with `w*w = e'` and
    `ww* ≤ r`.
  - Suppose a positive `x ∈ M_k(A^U)` vanishes on every limit trace but is nonzero.
    A positive lift has `lim_U sup_τ τ(x_m) > 0`, and a maximizing trace at each
    index defines a limit trace that is positive on `x`. So `x = 0`.
  - Hence `r = ww*` and `r ~ e'`. Correct.
- **Step 5 (assemble).**
  - Put `w_i* w_i = e'` and `w_i w_i* = e_i` for `i ≤ n`, with `e_n = r`.
  - `E_ij = w_i w_j*` are matrix units with `Σ E_ii = p`, giving a unital
    `M_n ⊆ p M_k(A^U) p`.
  - Correct.
- **Hidden hypotheses.**
  - Simplicity, separability and non-elementarity are stated but never used.
  - PC is assumed only for limit traces, and every trace the proof uses is a limit
    trace. No tracial state of `A^U` beyond the limit traces is needed.
- **Consistency.** This is the corner form of §4.1 of
  `research/artifacts/toms-winter-tracial-ultrapower-comparison-2026-09-12.md`,
  which passed in `research/artifacts/review-toms-winter-ultrapower-comparison-2026-09-12.md`.
  PC replaces strict comparison, and the matrix size is fixed.
- **Independent agreement.** §39.3 of `review-swarm4-2026-09-12.md` also passes this
  claim. The two readings were made separately.

## 2. `strict-comparison-with-rank-density-gives-support-projections`: PASS

Route: `strict-comparison-rank-density-support-projections-proof`. Artifact:
`research/artifacts/tw-support-gap-crux-2026-09-12.md` §1 (lane `tw-support-gap-crux`,
b04b42d61). Read at 44267adad. The only imports are Rørdam's lemma and the trace
identity, both standard.

- **Step 0 (constants).**
  - `T(A)` is compact because `A` is unital.
  - Every tracial state of a unital simple algebra is faithful on `M_k(A)`. So `c = min_τ τ(a)` satisfies
    `0 < c ≤ k`.
  - Correct.
- **Step 2 (rank gap).** Re-derived with `δ = ε/4` and `η = εcδ/8`.
  - `t − t² ≥ δ/2` on `[δ, 1−δ]` gives `μ_τ((δ,1−δ)) ≤ 2η/δ`. Markov gives `μ_τ([1−δ,1]) ≤ τ(q)/(1−δ)`.
  - `(1−ε)/(1−ε/4) ≤ 1 − 3ε/4`, because `(1−3ε/4)(1−ε/4) = 1 − ε + 3ε²/16`.
  - `4η/δ = εc/2`. So `d_τ((q−δ)_+) ≤ τ(a) − εc/4 < τ(a) ≤ d_τ(a)`, strictly at every trace, which
    is the form of strict comparison assumed.
  - Correct.
- **Step 3 (comparison).**
  - `‖(q−δ)_+ − rar*‖ < δ` and Rørdam's lemma give `d·rar*·d* = (q−2δ)_+`.
  - With `c_0 = dra^{1/2}`, `c_0*c_0` lies in `closure(a^{1/2} M_k(A) a^{1/2}) = her_A(a)`.
  - Correct.
- **Step 4 (transport).**
  - `ψ(c_0c_0*) = φ(q)`. Both `ψ` and `ψ − ψ²` vanish at 0, so the trace identity applies.
  - `φ` takes values in `(0,1)` only on `(2δ, 1−2δ)`, where `t − t² ≥ δ`. So `τ(b − b²) ≤ η/(4δ) = εc/32`.
  - `φ(t) ≥ t − 4δ` on `[0,1]`, checked on each of the three pieces. So
    `τ(b) ≥ τ(q) − εk ≥ τ(a) − 3εk`, using `η ≤ εk`.
  - Correct.
- **Known cases.**
  - `M_n`: RD_b fails, because near projections have traces near `(1/n)Z`. The theorem says nothing there.
  - Jiang–Su `Z`: RD_b holds through order zero maps `M_N → Z` with `τ(φ(1)) → 1`, and `Z` has uniform
    Gamma. The conclusion holds.
  - `C([0,1])` with `a = id`: `γ = 1/4`, and both faithfulness and strict comparison fail.
  - All consistent.
- **Hidden hypotheses: none.** The artifact's "no nuclearity, dimension or Gamma hypothesis" is accurate.
  - Unitality is used for compactness of `T(A)` and for `τ(1_k) = k`.
  - Simplicity is used for faithful traces.
  - Strict comparison is used once, at size `k`, against `a`. RD_b is used once, at size `k`.
  - Separability, exactness and non-elementarity are unused. Non-elementarity is forced by RD_b anyway.
  - Strict comparison is stated against `T(A)`, not quasitraces. For non-exact `A` this is stronger than
    the quasitrace form. That is the node's hypothesis, not a defect.
- **Subsumption scan.** Source re-read: Lin arXiv:2301.09250v2, Theorem 1.1 and the definition labelled
  `DOT`, from the TeX source on MSI. For exact `A`, the theorem is also a corollary of Lin.
  - RD_b and strict comparison make the rank map surjective (§3 below).
  - Lin's Theorem 1.1 covers σ-unital, non-elementary, simple algebras with strict comparison that are not
    purely infinite. For these, surjectivity of `Γ` is equivalent to tracial approximate oscillation zero,
    and either implies stable rank one.
  - The definition asks, for each `a ∈ Ped(A⊗K)_+`, for contractions `b_n ∈ Ped(Her(a))_+` with
    `ω(b_n) → 0` and `‖a − b_n‖_{2,QT} → 0`.
  - If `sup_τ (d_τ(b) − τ(f_{1/m}(b))) < ε'`, then `e = f_{1/m}(b) ∈ her(a)` has
    `τ(e − e²) ≤ d_τ(b) − τ(e) < ε'` and `τ(e) ≥ τ(b) − k/m`. So oscillation zero gives `γ_A ≡ 0`.
  - For non-exact `A`, Lin's rank map lands in functions on quasitraces, while RD_b controls only traces.
    That case is not visibly covered.
  - The node asserts no novelty, so no correction is needed.

## 3. `toms-winter-holds-on-tlfnd-rank-density-locus`: PASS as a proof; the locus is covered by known results

Route: `toms-winter-tlfnd-rank-density-locus-proof`. Artifact: the same file, §2. Read at 44267adad.

- **The five steps.** Each cited claim's hypotheses are among the standing ones.
  - **PC.** `strict-comparison-compares-ultrapower-projections` (exact, unital, simple, non-elementary,
    strict comparison). PASS in `review-toms-winter-ultrapower-comparison-2026-09-12.md`.
  - **PD.** §1 above, and review-swarm4 §39.3.
  - **TSP.** §2 above.
  - **Gamma.** `uniform-gamma-iff-tracial-support-projections-and-division` (b). Review-swarm4 §39.3 passes
    it conditionally on CETW Theorem 4.6 and Vaccaro Proposition 1.6.
  - **Z-stability.** `uniform-gamma-algebras-satisfy-toms-winter`, CETW Theorem A. PASS as an import in
    review-backlog-3 §23.
  - Correct.
- **Source re-read.** Vaccaro arXiv:2604.24682v2, TeX source on MSI.
  - Definition 1.5 (`def:loc_fin_nucdim`): for every finite `F ⊂ A_1` and every `ε` there is a subalgebra `B`
    with `dim_nuc B < ∞`, and each `a ∈ F` has some `b ∈ B_1` with `‖a − b‖_{2,T(A)} < ε`. This matches the
    node.
  - Theorem B (`thm_main:sr1_gamma`): "Let A be a separable, simple, unital, non-elementary, stably finite
    C*-algebra with stable rank one and tracially locally finite nuclear dimension. Then A has uniform
    property Γ." This matches the artifact's quotation.
- **RD_b is equivalent to surjectivity of the rank map.** This holds for unital, separable, simple, exact `A`
  with strict comparison. Re-derived here.
  - **(⟹)**
    - Edwards writes a strictly positive lsc affine `f` as `sup f_n`, with continuous affine `f_n` and
      `min_τ (f_{n+1} − f_n) > 0`.
    - RD_b gives `q_n` with profile `f_n` and defect `< η_n`.
    - Since `|1_{(1/2,1]}(t) − t| ≤ 2(t − t²)` on `[0,1]`, `x_n = (q_n − 1/2)_+` has rank within `3η_n` of
      `f_n`.
    - Choose `6η_n < min(f_{n+1} − f_n)`. Strict comparison makes `[x_n]` increasing, and the supremum has
      rank `f`.
  - **(⟸)**
    - Take `f: T(A) → [0,k]` and `η`, and put `f'' = (1 − η/2k)f + η/8`. It takes values in `(0,k)` and is
      within `5η/8` of `f`.
    - Surjectivity gives `y` of rank `f''`. Strict comparison gives `y ≾ 1_k`, so each `(y − ε)_+` is Cuntz
      equivalent to some `z ∈ M_k(A)_+`.
    - Lower semicontinuity and compactness of `T(A)` give a single `ε` with `d_τ(z) > f'' − η/8` for every `τ`.
    - Put `w = z/‖z‖`. The same argument gives a single `n` with `τ(w^{2/n}) > f'' − η/4`.
    - Then `q = w^{1/n}` has `|τ(q) − f| < η` and `τ(q − q²) ≤ d_τ(z) − τ(w^{2/n}) < η/4`.
- **Consequence: Corollary 2 is a corollary of known results.** On this locus:
  - strict comparison gives surjectivity (the ⟹ direction above);
  - Lin's Theorem 1.1 (source re-read) gives stable rank one;
  - Vaccaro's Theorem B gives uniform Gamma, since a unital simple algebra with a trace is stably finite;
  - CETW Theorem A gives Z-stability.

  The artifact's §3 left this relation "not checked".
- **Scope sentence overstated.** The node says: "The new part is tracially-but-not-norm locally finite nuclear
  dimension." That part already follows from Lin, Vaccaro and CETW.
  - Vaccaro (TeX line 305) also records that no nuclear algebra without locally finite nuclear dimension is
    known. So that part of the locus may be empty.
  - A forward correction of this bullet is already in the shared working tree, but it is not on main at
    44267adad. It cites a draft §40 of review-swarm4 and gives the (⟹) argument. This review agrees with it
    and leaves the node to that lane.
- **Verdict.** PASS on the mathematics, with the Scope novelty sentence overstated. The node itself asserts
  no novelty.

## 4. `theorem-e-congruence-projections-vanish-at-regular-trace`: PASS, with two wording notes

Route: `theorem-e-congruence-projections-vanish-at-regular-trace-proof`. Artifact:
`research/artifacts/nh-h1-theorem-e-instance-2026-09-12.md` (c6067895f). Node landed in 1d9a1ceda. Read at
44267adad. Items 1–4 are self-contained, and the imported distortion bound of Remark 4 is unused.

- **Item 1, Theorem 1(a): fixed vectors.**
  - `‖A‖_2² = m^{-2} Σ_{i,j} τ(σ(k_i^{-1}k_j)) = 1/m` uses only `τ∘σ|Γ = δ_e`. Then
    `τ(p_K) = τ(Ap_K) ≤ m^{-1/2} τ(p_K)^{1/2}`.
  - In coordinates, Cauchy–Schwarz gives `|tr((1 − σ_n(k_i))p_n)| ≤ ε·tr p_n`, and `‖A_n‖_2² → 1/m` uniformly
    in `p_n`.
  - For `p_prof`: `R_+` is Noetherian, so it has countably many finite-index ideals, and the trace is normal.
    Hence `τ(∨_I p_Γ(I)) ≤ Σ_I τ(p_Γ(I)) = 0`.
  - Test: in a sofic permutation model on `Γ/N_n`, the `Γ(I)`-fixed subspace has dimension
    `[Γ : Γ(I)N_n] ≤ [Γ : Γ(I)]`. Its normalized dimension tends to 0, as predicted.
  - Correct.
- **Item 2, Theorem 1(b): the threshold κ/√|S| follows for each pair `(S, κ)`.**
  - `1 − ⟨λ(T)ξ,ξ⟩ = (2|S|)^{-1} Σ_s ‖λ(s)ξ − ξ‖² ≥ κ²/(2|S|)`, because the sum dominates the maximum. So
    `spec λ(T) ⊆ [−1, c]` with `c = 1 − κ²/(2|S|)`.
  - `τ∘σ|Γ = δ_e` makes the moments of `T` in `M` equal those of `λ(T)`. So
    `lim_U tr 1_[c+η,1](T_n) = 0`.
  - For a unit `v ∈ V_n`, `⟨T_n v,v⟩ ≥ 1 − ε²/2`, since each of the `|S|` terms is at most `ε²`. Min-max gives
    `dim V_n` eigenvalues `≥ 1 − ε²/2`, and `1 − ε²/2 > c` is exactly `ε < κ/√|S|`.
  - **Generating-set dependence.** The statement takes one `(S, κ)` at a time, where `κ` is the ℓ² Kazhdan
    constant of `S` for `λ_Γ` alone.
    - No uniformity over generating sets is claimed or used.
    - The threshold is lossy, because the sum is bounded by the maximum twice, but it is not wrong.
    - `S` need not be symmetric, since `T_n` is symmetrized.
  - `S = F_I` with `κ = κ_I` is valid: `λ_Γ|Γ(I)` is `[Γ:Γ(I)]` copies of `λ_Γ(I)`, which has no invariant
    vectors because `Γ(I)` is infinite.
- **Item 4, Theorem 1(c): proved, not assumed.** "Roundings have asymptotically regular traces" is a theorem
  about whatever roundings exist.
  - A Kazhdan set generates the group, so each `g` is a fixed word in `F`. Hence `‖σ_n(g) − π_n(g)‖_2 → 0`.
  - Padding changes normalized traces by `o(1)`. So `tr π_n(g) → δ_e(g)`.
  - The fixed-mass bullet reruns (a) with `ε = 0` on elements of `e_12(I)`. The root-ideal bullet is the case
    `g = e_12(f)`.
  - The artifact files this as "established under (H1)" (§5), and the node states it conditionally. The (H1)
    Attempts bullet "Any rounding has…" is the same universally quantified statement.
  - Consistent.
- **Item 3, Corollary 2(ii): profinite models.**
  - `p_Γ(I)` increases as `I` shrinks, and it commutes with `σ(Γ)` because `Γ(I)` is normal.
  - On that corner `σ` is an exact representation of `Γ/Γ(I)`.
  - HS-stability of finite groups and trivial padding give defect `≤ 2(1 − τ(p_Γ(I)))^{1/2} + o(1)`. A
    diagonal choice then gives (H1) with `n' = n`.
  - Correct.
- **Wording note 1: "exactly".**
  - Corollary 2(ii) proves sufficiency: `τ(p_prof) = 1` implies (H1).
  - "Exactly" adds that fixed-subspace projections capture only `τ(p_prof)` of the mass. That part is
    informal, because "the route" is not a formal object.
  - The node needs only what is proved: `τ(p_prof) = 0` at the regular trace, and zero almost-invariant mass
    at fixed levels.
- **Wording note 2: non-uniform constants.**
  - The node's sentence after item 4 cites `uniform-kazhdan-fails-for-linear-theorem-e-pair`. Lubotzky–Yao
    gives non-uniformity over the generating sets of each `Γ(I_n)` separately, so that reading is right.
  - The artifact's Proposition 3(3) says instead that "`κ_(I_n)` are not uniform in `n`". The citation does
    not give that, since large generating sets can keep the constants bounded below.
  - The point survives: `κ ≤ √2` for any infinite group (test `δ_e`), so `κ/√|F_(I_n)| → 0` whenever
    `|F_(I_n)| → ∞`.
  - Proposition 3(3) is labelled a standard estimate and is not one of items 1–4.
- **Scope against `hs-stable-vertex-rounding-for-every-model`.**
  - (H1) quantifies over trace-preserving `σ: G → U(∏_U M_n)`, so every vertex restriction has regular trace.
  - Hence the fixed-level route is void for every model (H1) concerns, and keeping (H1) OPEN is right.
  - The `distinct_from` entry and the (H1) Attempts bullet agree with this.
  - No forward correction is needed.
