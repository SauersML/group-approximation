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
- **Cross-check with `review-swarm4-2026-09-12.md` §40.4 (8cf12afc4): agreement, no disagreement.**
  - §40.4 also passes this claim. Its one check is the estimate `|d_τ((q − 1/2)_+) − τ(q)| ≤ 2τ(q − q²)`, which
    §3 below uses for rank surjectivity. This claim's own proof does not use it.
  - The line-by-line reading above was made separately.
  - §40.4 does not assess the artifact's "no nuclearity, dimension or Gamma hypothesis" remark. The
    hidden-hypotheses bullet above is the only check of it.

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
  - The forward correction is now on main (8cf12afc4). At c43a30d2e the Scope says the tracially-but-not-norm
    case "is also a corollary of known results". It gives the (⟹) argument with the same `6η_n` choice, cites
    review-swarm4 §40, and asserts no novelty. It agrees with the argument above, and no further edit is needed.
- **Cross-check with review-swarm4 §40.4 (8cf12afc4): agreement, no disagreement.**
  - §40.4 reaches the same verdict: PASS, subsumed by Lin, Vaccaro and CETW.
  - §40.4 took the Lin and Vaccaro statements from the graph's citation nodes and did not re-extract them. This
    section re-read Lin Theorem 1.1, Vaccaro Definition 1.5 and Vaccaro Theorem B from the TeX sources, so the
    subsumption now rests on a source check.
  - Two points are not in §40.4:
    - the (⟸) direction, so on this locus RD_b is equivalent to surjectivity, not only sufficient for it;
    - Vaccaro's remark that no nuclear algebra without locally finite nuclear dimension is known.
  - The Theorem's "finite nuclear dimension" conclusion also comes from step 5. The import node's statement
    includes it, and review-backlog-3 §23 passes that statement.
- **`comparison-forces-tracial-support-projections`: correctly OPEN** (agreeing with §40.4).
  - It assumes projection comparison by limit traces, not strict comparison of `A`.
  - §2's proof uses strict comparison in `A` (Rørdam's lemma at size `k`), and Lin's Theorem 1.1 needs it too.
    Neither route applies.
  - The node's own real-rank-zero attempt names its missing step as the converse of CCEGSTW Proposition 7.2.
  - At c43a30d2e its only `requires:` consumer is `lfnd-locus-gamma-via-support-projections`.
  - **Wording note.** "Every unital Toms–Winter counterexample on this locus would refute it" is now vacuous,
    because this section's claim shows there is no such counterexample. The node's Attempts bullet already
    says so, and no edit is needed.
- **Verdict.** PASS on the mathematics. The Scope novelty sentence was overstated at 44267adad and is corrected on
  main by 8cf12afc4. The node itself asserts no novelty.

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
- **Cross-check with review-swarm4 §40.5 (8cf12afc4): agreement, no disagreement.**
  - §40.5 checks items 1, 2 and 4, and item 3 in outline only. Item 3 is checked in full above.
  - For item 1 it uses `T = X^*X/m` with `X = Σ_i σ(k_i)`, so `τ(T) = 1` and `Tp = mp`. That is a different
    computation giving the same bound `τ(p) ≤ 1/m`.
  - §40.5 does not raise the two wording notes above. They stand.

## 5. The mixed-level root group `K_i` (lane `nh-ki-kazhdan`, 44267adad)

Read at 44267adad. None of these files changed by fdf10525a.

**Subsumption scan** at fdf10525a, over `research/*.md`.
- Patterns searched: strong grading, root-graded, Kazhdan subset, Nagao, mixed-level, `SL_2(F_q[`, `E_2(F_q[`,
  `GL_2(k[`, and Bruhat–Tits tree.
- No node outside this commit asserts property (T), or its failure, for `K_i` or any mixed-level subgroup.
- Earlier mentions:
  - the open question in the Attempts of `laurent-vertex-rounds-for-every-model`;
  - the same question in `hs-stable-vertex-rounding-for-every-model` (see §5.4);
  - inline uses of Nagao's theorem, with no node of its own, in `support-thirteen-from-no-inverse`,
    `dykema-heister-juschenko-bounded-rank-direct-finiteness`, `leavitt-rank-three-support-group-is-virtually-free`
    (and its proof), and the artifact `leavitt-rank-three-no-inverse-2026-08-18`. These use Nagao's decomposition;
    none states it as a claim, so the new import duplicates nothing.
  - the Baum–Connes nodes on `E_2(F_q[x^(±1)])` acting on products of Bruhat–Tits trees. That is a different group.
- The other "strong grading" or "strongly graded" hits are about graded rings, for example `1 = Σ s_i s_i*` lying in
  `O_1 O_(-1)`:
  - `bh-steinberg-hosts-2026-09-12`;
  - `nekrashevych-completions-contain-their-coefficients-proof`;
  - `leavitt-tensor-powers-are-not-left-coherent` and its proof;
  - `simple-inputs-have-fp-elementary-leavitt-tensor-hosts`;
  - two headings in `review-swarm4-2026-09-12.md`.
- No `review-*.md` file mentions the new ids.

### 5.1 `strongly-root-graded-groups-have-kazhdan-root-unions` (import): PASS

Source re-read: Ershov–Jaikin-Zapirain–Kassabov, arXiv:1102.0031. The TeX `2014gradedT0310.tex` was fetched with
curl on MSI and the passages were read.

- **Part (a)** is `thm:main2` (TeX 689–694), verbatim.
- **Grading** (TeX 2240–2253): "a collection of subgroups `{X_α}` of `G`, called root subgroups", with (i) generation
  and (ii) the commutator condition for `α ∉ R_(<0) β`, with `a, b >= 1`. This matches the node.
- **Strong** (TeX 2316–2335): the grading is strong at `(γ, Φ_f)`, for `γ ∈ C_f`, if
  `X_γ ⊆ < X_β : β ∈ Φ_f, β ∉ Rγ >`. It is strong if it is strong at every such pair. This matches the node.
- **The A_2 core.** The core of `{α, β, α+β}` is `{α+β}` (TeX 2055–2056). This matches the node.
- **Part (b)** follows from Observation `Kazhrat` (TeX 951–961).
  - The source gives (ii) `√2 κ_r <= κ(G,B;S) <= 2 κ_r` for normal `B`, and (iii) `κ(G,S) >= κ(G,B) κ_r(G,B;S)`.
  - `κ_r` is read as in the citation route; the passage defining it was not printed here.
  - (b)(i) is (iii), with `κ_r >= 1/C`.
  - (b)(ii) is (ii), with `κ_r >= μ/2`. The set of admissible ratios is closed, so the bound is attained. The node's
    "S finite" is not needed.
- **Ideal root subgroups are allowed.**
  - The definition takes arbitrary subgroups. It asks for no ring, no parametrization and no isomorphism type.
  - The source's introduction (TeX 699–705) makes the same move the route makes: an `A_(n−1)`-graded group is also
    strongly `A_2`-graded, reading matrices as "3×3 block-matrices with blocks of uneven size".

### 5.2 `mixed-level-root-group-is-kazhdan-in-rank-at-least-five`: PASS

Route `mixed-level-root-group-is-kazhdan-in-rank-at-least-five-proof`. Re-derived line by line.

- **(★).** `eps_xy + eps_yz = [x=3] + [y=2] + [y=3] + [z=2] = eps_xz + [y=2] + [y=3]`. Correct.
- **Step 1.** Expanding the four factors gives `[e_xy(a), e_yz(b)] = e_xz(ab)` for distinct `x, y, z`. Correct.
- **Step 2 (grading).**
  - The blocks exist because `|J| = r − 2 >= 3`.
  - `X_XY` is abelian and lies in `K`.
  - `[e(M), e(N)] = e(MN)` uses `M^2 = N^2 = NM = 0`, where `NM = 0` because `Z ≠ X`. The entries lie in `I_xz`
    by (★).
  - Roots sharing a block give commuting groups, and opposite roots impose no condition. So condition (ii) holds for
    every ordered pair, including `(X,Y), (Z,X)` by inversion.
  - Generation: correct.
- **Step 2 (strongness).**
  - The six Borel sets are `{(X,Y), (Y,Z), (X,Z)}` over ordered triples of distinct blocks, each with core `(X,Z)`.
  - With `y ∈ Y ∩ J`, Step 1 writes each `e_xz(I_xz)` as a commutator in `< X_XY, X_YZ >`. This works for every
    triple, because each block meets `J`.
  - This is strong in EJZK's sense (§5.1).
- **Step 3 (fine root groups).**
  - **Column type.** The map is a homomorphism because `z ∉ {x, p}` and `w ↦ t^([z=2]) w` is `R`-linear, with `t`
    central. The images `e_xp(R)` and `e_px(R)` are full, since `x, p ∈ J`. Also `t^([z=2]) R = I_xz = I_pz`.
  - **Row type.**
    - The row model composes as `(v,g)(u,h) = (u + vh, gh)`.
    - `g ↦ (g^T)^(-1)` preserves `EL_2(R)`, because `e_12(a)^T = e_21(a)`, and it carries `R^2` to `R^2`. So the
      relative constant transfers.
    - The images `e_zp(R)`, `e_pz(R)`, `e_xz(I_xz)` and `e_xp(I_xp)` lie in `K`.
  - **The roots (2,3) and (3,2).**
    - The commutators have levels `I_2p = I_p3 = R` and `I_3p = I_p2 = (t)`.
    - `e_p3(±1)` and `e_p2(±t)` lie in `S`.
    - The unitary bound `||[a,b]v − v|| <= 2||av − v|| + 2||bv − v||` holds.
  - `C = r^2 (4/μ + 2)`. Correct.
- **Step 4.** `κ(K, S) >= κ_0 / C > 0` by (b)(i). A finite Kazhdan set is the source's definition of (T). Correct.
- **Tests.**
  - `t` a unit: `K = EL_r(R)`, which has (T) for `r >= 3`. Consistent.
  - `t = 0`: `K = < e_cd(R) : c ≠ 3, d ≠ 2 >`.
    - The proof still runs, with `X_32` trivial.
    - `K` maps onto `EL_J(R)`, which has (T) since `|J| >= 3`.
    - Consistent.
  - `r = 4`: there are no three blocks meeting `J`, and §5.3 shows the conclusion fails for `d >= 2`.
- **Hypotheses used.**
  - Commutativity of `R` is used for the central `t` in Step 3.
  - Finite generation of `R` enters through `elementary-linear-semidir-pair-relative-t`, which supplies the finite
    `S_0`, and so through the finiteness of `S`. That import passed as a known result in
    `review-backlog-2-2026-09-12.md` §26, where its source was not re-read.
- **Display check.**
  - The node's levels match `eps_cd`: row 3 and column 2 at `(t)`, the corner `(3,2)` at `(t^2)`, and `(2,3)` full.
  - They match the definition of `K_i` in the laurent node's Attempts (node lines 57–60 at 44267adad).
- **Wording notes.**
  - The node says the EJZK criterion "does apply when some root subgroups are proper ideals, provided each level ideal
    is the product of two levels through a full index". The criterion needs no such condition. The condition is what
    makes this particular grading strong.
  - Step 3 says "By part (b) of the grading claim, `R^2` is normal in `P`". Normality is elementary. Part (b) gives
    only the consequence drawn from it.
  - The Use paragraph says the laurent reduction "then gives the converse Laurent direction on `St_r(L)` for every
    `r >= 5`". That reduction is an Attempts bullet of the OPEN node `laurent-vertex-rounds-for-every-model`. It is not
    reviewed here, and this verdict covers property (T) of `K(R, t)` only.
- **Novelty.** The claim is a direct instance of `thm:main2` with the coarsening from EJZK's introduction. The node
  claims no novelty.

### 5.3 `mixed-level-root-group-is-not-kazhdan-in-rank-four`: PASS; Nagao not re-read

Route `mixed-level-root-group-is-not-kazhdan-in-rank-four-proof`. It requires the new import
`polynomial-gl2-over-a-field-is-a-nontrivial-amalgam` and `property-t-implies-property-fa` (Watatani, not re-read).

- **Item 1 (onto E_2).**
  - `φ` kills every generator with `eps >= 1` and sends the rest onto `e_cd(F_q[y])`.
  - `P` is a subgroup, because the conditions `g e_2 = e_2` and `e_3^T g = e_3^T` are preserved by products and
    inverses. It contains the generators.
  - For `a, b ∈ {1, 4}`, `(gh)_ab = g_a1 h_1b + g_a4 h_4b`, since `g_a2 = 0` and `h_3b = 0`. So `ρ` is a homomorphism.
  - `eps_14 = eps_41 = 0`, so `ρ` hits `e_12(F_q[y])` and `e_21(F_q[y])`.
  - Correct.
- **Item 2 (no (T)).**
  - `E` is infinite and `GL_2(F_q)` is finite.
  - `e_12(1)` and `e_21(1)` are unipotent with different eigenlines, so `E` lies in no conjugate of `B(F_q[y])`.
  - `E` therefore fixes no vertex. The action has no inversions, so `E` fixes no point.
  - Watatani's theorem and passage of (T) to quotients finish the argument. Correct.
  - **Independent of Nagao.**
    - `F_q[y]` is discrete in `F_q((1/y))`, so `E` is discrete in `SL_2(F_q((1/y)))`.
    - Vertex stabilizers of the Bruhat–Tits tree are compact open. So each meets `E` in a finite group, and the
      infinite group `E` fixes no vertex.
    - `SL_2` acts on the tree without inversions, so `E` fixes no point.
    - This uses only the Bruhat–Tits tree (Serre, *Trees*, II.1), not the amalgam.
- **Item 3 (q = 2).**
  - `F_2[y]^× = {1}`, so `E_2 = SL_2 = GL_2` over `F_2[y]`.
  - Abelianization preserves pushouts.
  - `B(F_2) = < e_12(1) >` maps to the sign in `GL_2(F_2)^ab ≅ Z/2`, and to `1 ∈ F_2[y]`. The quotient is
    `≅ (F_2[y], +)`, which is infinite.
  - Correct.
  - Test at `r = 4`, where `J = {1,4}`. The only commutator routes to `(1,4)` pass through index 3 or index 2, and
    both give only level `(x_i)`: `[e_13(a), e_34(x_i b)] = e_14(x_i ab)` and `[e_12(x_i a), e_24(b)] = e_14(x_i ab)`.
    So the full root group `e_14(R_+)` is not killed in `K_i^ab`, which is consistent with item 3. Under the corner
    map it becomes `e_12(F_q[y])`.
  - Unlike item 2, item 3 needs Nagao's decomposition itself.
- **Source status.**
  - From MSI, Springer returned an HTML page for *Trees* (magic bytes `<!DOC`).
  - The citation route records that a Crossref query from MSI did not locate a copy of Nagao's paper.
  - So Nagao's theorem is "source not re-read". The recorded form is the textbook one (Serre, *Trees*, II.1.6).
- **Display check.** The title and items 1–3 match the route. The Consequences bullets match the laurent correction.

### 5.4 The correcting bullet on `laurent-vertex-rounds-for-every-model`: PASS

- **What it changes.** The appended bullet (13 lines):
  - retracts the Attempts claim "`K_i` has FINITE abelianization for `r ≥ 4`" at `r = 4`, `q = 2`;
  - narrows "follows from property (T) of `K_i` (`r ≥ 4`)" to `r >= 5`.
- **Correct by §5.2 and §5.3.**
  - The false sentence in the original bullet is "the full-ring part is elementary of rank `≥ 2`". At `r = 4` the full
    part is the `{1,4}` corner.
  - The original's commutator identities for the confined directions are fine.
- **What stays open.** The bullet keeps the `St_r(L) → Δ` descent OPEN.
- **Stale question elsewhere (recommendation only, not edited).**
  - `hs-stable-vertex-rounding-for-every-model` (line 77 at fdf10525a) still asks "is the mixed-level root group `K_i`
    Kazhdan for `r >= 4`?" and recommends it as the sub-target.
  - It is a question, not an assertion, so nothing false is claimed.
  - A forward note there would help: yes for `r >= 5`; no for `r = 4`, `d >= 2`; `r = 4`, `d = 1` undecided.

## 6. The trace kernel of Ozawa's block corona (lane `quasitrace-k-stable`, 894cc2bb4, e43f7dafa)

Read at 4e7e23aa0, after the lane's commits dbfb32741 (artifact), 894cc2bb4, e8a9c2cfa and e43f7dafa. The local
copies match the blobs there, and none of these files changed between 4e7e23aa0 and c644a7c66.

**Subsumption scan** at 4e7e23aa0, over `research/*.md` and `research/artifacts/*.md`.
- Patterns: `property (S)`, `Ortega–Perera`, `0903.2917` (13 files); `unique maximal ideal`, `unique proper maximal`,
  `Boutonnet`, `1908.07812`, `no (nonzero) unital quotient` (11 files).
- Outside this lane's files:
  - `sl3z-ozawa-corona-trace-kernel-is-stable` is OPEN, and it is the stronger target.
  - The `opr-*` nodes import other Ortega–Perera–Rørdam results: the CFP/RR0 dichotomy, the refinement monoid and
    properly infinite splits. None states Prop 4.5 or anything about `K`.
  - The other first-pattern hits are also about other results or algebras:
    - `ex-open-status-2026-09-12` has a log line on the `ex-rr0-dichotomy` OPR imports;
    - `stw74-property-sp-cu-stability-audit-2026-08-30` discusses property (S) for `D`;
    - `rr0-simple-algebras-have-corona-factorization` cites OPR for the CFP.
  - `stw74-weak-omega-obstruction-proof` and `stw99-lxxvi-residually-stably-projectionless-audit-2026-09-05` say "no
    nonzero unital quotient" about other algebras (`D`, `Her(a)`).
  - Four nodes match only the Boutonnet–Houdayer name or arXiv number:
    - `character-rigidity-equals-hyperfinite-hs-stability`;
    - `hnn-route-is-relative-commutant-collapse`;
    - `relative-commutant-collapse-for-sl2-pair`;
    - `sl3-collapse-via-carrier-character-rigidity`.

    Grepping for the maximal-ideal wording hits only the two `stw` files.
- So no established node already proves either new statement.

### 6.1 `sl3z-ozawa-corona-trace-kernel-is-unique-maximal-ideal`: PASS

Route `sl3z-ozawa-corona-kernel-unique-maximal-ideal-proof`. Artifact §1: Prop 1.1 and Cor 1.2.

- **Source re-read.** Boutonnet–Houdayer, arXiv:1908.07812v2. The TeX was fetched on MSI; quotes render the markup.
  - Notation, first item (TeX 230): "Let G be any connected semisimple Lie group with finite center and no nontrivial
    compact factor, all of whose simple factors have reak rank at least two." "reak" is the source's typo for "real".
  - Corollary D (`lettercor`, label `main rep`, TeX 294–300): "Let G be as in the notation and assume moreover that G
    has trivial center. Let Γ < G be any irreducible lattice. Then for any weakly mixing representation π … the left
    regular representation λ_Γ is weakly contained in π." Item (i) makes `τ_Γ ∘ Θ_{π,λ}` the unique tracial state of
    `C*_π(Γ)`, and item (ii) makes `ker Θ_{π,λ}` its unique proper maximal ideal.
  - Proof of (ii): for a proper ideal `I` with quotient map `α`, "the unitary representation ρ … is weakly contained in
    π and hence weakly mixing by Lemma [lem:(T)]". Then `λ ≺ ρ`, `β : A/I → C*_λ(Γ)` is well defined,
    `Θ_{π,λ} = β ∘ α`, and `I ⊂ ker Θ_{π,λ}`.
  - Lemma `lem:(T)` (TeX 1164), for a countable infinite property (T) group: "if π is weakly mixing and if ρ is weakly
    contained in π, then ρ is also weakly mixing".
  - Artifact Prop 1.1 does not use that lemma. It gets weak mixing of the representation of `A/J` from the absence of
    finite-dimensional representations of `A`. Both routes are sound.
  - Node lines 35–37 and artifact lines 34–36 say "trivial centre and no compact factor, all of whose simple factors
    have real rank at least 2", with `Γ` an irreducible lattice. They drop only "finite center", which trivial center
    implies, and the word "nontrivial".
  - `SL(3,R)` has trivial center: a real `λ` with `λ³ = 1` is `1`. So `SL(3,Z) < SL(3,R)` is covered.
- **Hypotheses used.**
  - Let `J` be a proper ideal. A faithful representation of `A/J` has no finite-dimensional subrepresentation, because
    that would be a finite-dimensional representation of `A`, and `kazhdan-block-algebras-contain-their-block-ideal`
    (ESTABLISHED) excludes those.
  - So the representation is weakly mixing, Corollary D makes `q` factor through `A/J`, and `J ⊆ K`.
  - The input "no finite-dimensional representation" is where the corona differs from `C*(Γ)`.
- **Tests.**
  - **Full `C*(Γ)`.** The trivial representation is finite-dimensional, so it is not weakly mixing. `C*(Γ)` has many
    maximal ideals, from the finite quotients of `Γ`. So the hypothesis is load-bearing.
  - **`C*_r(Γ)`.** `K = 0`, and item 1 becomes simplicity of `C*_r(SL(3,Z))`. That agrees with Corollary D for
    `π = λ`.
- **Cor 1.2.** Re-derived.
  - (a) If `J ∩ K = 0`, then `J` is proper, so `J ⊆ K` and `J = 0`.
  - (b) A unital quotient `K/J` gives a central projection. The kernel of the corresponding quotient of `A` is a proper
    ideal, so it lies in `K`, which forces `A = K`. That contradicts `K ≠ A`. Correct.
- **Display check.** Items 1–3 match Prop 1.1 and Cor 1.2(a), (b).
- **Wording note.** The phrasing of Cor 1.2(c), `J + K ∈ {K, A}`, is awkward. The content is "every closed ideal lies
  in `K` or equals `A`".

### 6.2 `sl3z-ozawa-corona-trace-kernel-has-property-s` (OPEN) and route `sl3z-ozawa-block-qt-via-kernel-property-s`: PASS on the equivalent form and on the route

- **Source re-read.** Ortega–Perera–Rørdam, arXiv:0903.2917v4, `main.tex` on MSI.
  - Quotes below render the TeX markup; the words are the source's.
  - **`F(A)`** (TeX 1086–1088): "all positive elements a in A for which a = ae for some positive element e in A (that
    can be taken to be a contraction)".
  - **Definition** (`defi`, TeX 1094–1098): "A C*-algebra A is said to have property (S) if for every a∈F(A) there
    exists b∈A^+ such that a⊥b and a≺_s b."
    - `≺_s` (`defi`, TeX 300–303): "x is stably dominated by y, written x<_s y, if the equivalent conditions (i)–(iii)
      in Proposition [stable_comparison] hold". The remark at TeX 309–310 restates (ii) as "there exists k∈N such
      that (k+1)x≤ky".
    - This matches the node's statement and the artifact's §2 Definitions.
  - **Lemma `lema00`:** "Let A be a separable C*-algebra with property (S). Then A has no non-zero unital quotients."
  - **Prop 4.5** (`prop1`, TeX 1209): "Let A be a separable C*-algebra. Then A has property (S) if and only if A has
    no non-zero bounded lower semi-continuous 2-quasitrace and no non-zero unital quotient." Its proof says the "if"
    part is contained in the proof of [HRW, Theorem 3.6].
  - **Numbering.**
    - Every environment shares the `lem` counter, numbered within sections.
    - In section 4 the order is `defi` 1094, `lem` 1108, 1126, 1171, `prop` 1209, `corol` 1245, `prop` 1271, `prop`
      1318, `corol` 1360.
    - That gives 4.1–4.9, so `prop1` is 4.5, Cor 4.6 is the `M_n` permanence, and `prop2` is 4.7.
- **The lsc qualifier.** OPR 4.5 names "bounded lower semi-continuous" 2-quasitraces; the node drops "lsc".
  - The equivalence still holds. Its only-if proof starts from "a non-zero bounded 2-quasitrace" with no lsc
    assumption, and the "if" direction needs only the lsc ones.
  - `K` is separable because `A` is, and it has no unital quotient by 6.1. So the equivalent form is correct.
- **Route.** Re-derived.
  - Let `τ` be a bounded 2-quasitrace on `A`. It restricts to one on `K`, and (S) for `K` (with Cor 4.6 for `M_2(K)`)
    kills it.
  - So every quasitrace of `A` vanishes on `K`.
  - `sl3z-ozawa-block-qt-linearity-iff-corona-kernel-invisible` (ESTABLISHED) then gives the target.
  - "Logically contains `sl3z-ozawa-block-qt-via-stable-kernel`" is right, because OPR §4 (TeX 1104–1105) says "It is
    easy to see that every stable C*-algebra has property (S)."
- **Why-it-matters bullets.**
  - The 4.7 bullet is used as OPR state it: `Cu` has ω-comparison, and the algebra is hereditary in `A ⊗ 𝒦`, applied
    to `K ⊗ e_11`.
  - The converse is marked "not settled", which is honest.

### 6.3 Artifact Props 2.1–2.3 and Remark 2.4: PASS

- **Prop 2.1.** (ii)⇒(i) is OPR 4.5 "if" together with Cor 1.2(b). (iii)⇒(ii) is not claimed.
- **Prop 2.2.** Stable implies (S). With ω-comparison, (S) implies stable, by OPR 4.7 with `D' = K ⊗ e_11`.
- **Prop 2.3, the one-translate criterion.** Steps 1–5 re-derived.
  - Parameters (artifact lines 148–157):
    - `h = 0` on `[0, ε/4]`, `h = 1` on `[ε/2, ∞)`, linear between;
    - so `h(t) = t·k(t)` with `sup k ≤ 2/ε`, attained at `t = ε/2`;
    - `δ < ε²/6`, `y = uau*` and `b = (1 − h(a)) y (1 − h(a))`.
  - Key estimate: `‖y h(a)‖ ≤ ‖ya‖·‖k(a)‖ < 2δ/ε`. Each of the three terms of `b − y` is at most that, so
    `‖b − y‖ < 6δ/ε < ε`.
  - It feeds Hjelmborg–Rørdam Prop 2.2, as OPR's proof of 4.7 quotes it: "for every a∈B^+ and every ε>0 there exists
    b∈B^+ such that (a−ε)_+≾b and (a−ε)_+⊥b". `K` is separable, hence σ-unital.
  - An earlier nit on (O4) is withdrawn: the quote does have `a ∈ B^+`.
- **Tests.**
  - **`𝒦~ ⊃ 𝒦`.** Shift unitaries give the translates, and `𝒦` is stable.
  - **`M_n`.** The criterion is vacuous there.
  - **`C[0,1] ⊃ C_0(0,1]`.** Unitaries of a commutative algebra fix `a`, so the criterion fails. That is consistent,
    since `C_0(0,1]` has a unital quotient and is not stable.
- **Source not re-read.** Kirchberg–Rørdam Lemma 2.2 and the Hjelmborg–Rørdam paper itself. Only OPR's quotation of HR
  2.2 was read.
- **Remark 2.4.** It leaves open whether the rank-one parabolic projections lie in `B`, and the node's Attempts
  bullet says the same.
