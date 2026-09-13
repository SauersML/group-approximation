# Toms–Winter on Bauer simplices: rank density is tracial divisibility of the unit (2026-09-12)

Lane `ex-toms-winter` (EX swarm).

**Task.** Decide `stw99-problem-xviii-toms-winter-conjecture` either way, building on the
support-gap and W*-bundle nodes landed earlier on 2026-09-12.

**Outcome.** Nothing here proves or refutes Toms–Winter. Nothing here is reviewed.
1. **Theorem 1 (central step functions).** Let `A` be unital and separable, with `T(A)` a
   nonempty Bauer simplex. If the unit is tracially `N`-divisible for arbitrarily large `N`
   (Definition 1.1), then `A` has bounded rank density (RD_b). No comparison, nuclearity,
   simplicity or dimension hypothesis is used.
2. **Theorem 2 (equivalences).** Let `A` be unital, simple, separable, nuclear and
   non-elementary, with Bauer `T(A)`, tracially locally finite nuclear dimension (tlfnd) and
   strict comparison. These are equivalent:
   - (a) `A ≅ A ⊗ Z`;
   - (b) uniform property Gamma;
   - (c) RD_b;
   - (d) for every `N`, a unital `*`-homomorphism `M_N → A^U`;
   - (e) the unit is tracially `N`-divisible for arbitrarily large `N`.
3. **Corollary 3 (shape of a counterexample).** A unital Toms–Winter counterexample with
   Bauer simplex and tlfnd has a tracially indivisible unit. It contains no unital simple
   infinite-dimensional C*-subalgebra with a unique trace (`Z`, UHF algebras, irrational
   rotation algebras), and no unital `Z_{n,n+1}` for large `n`.
4. **The crux on this locus** is the open `strict-comparison-forces-tracially-divisible-unit`.
   It is an existence question for one element, the unit, with constant trace profile.
   Unit rigidity occurs in simple nuclear algebras without strict comparison (Dadarlat,
   Hirshberg, Toms and Winter).

## Sources and what was read

- **Ozawa.** N. Ozawa, *Dixmier approximation and symmetric amenability for C*-algebras*,
  arXiv:1304.3523. MSI copy `/projects/standard/hsiehph/sauer354/lit/tw-bundle-hunter/1304.3523.txt`.
  - Lines 100–182. The uniform 2-norm `‖a‖_{2,S} = sup_{τ∈S} τ(a*a)^{1/2}`. The completion
    `A^u`, "the C*-algebra of the norm-bounded uniform 2-norm Cauchy sequences, modulo the
    ideal of the uniform 2-norm null sequences". `N = (⊕_{τ∈S} π_τ)(A)''`, the center-valued
    trace `ctr`, and "A^u coincides with the closure A^st of A in N with respect to the strict
    topology". The affine center `Z(Aff(S))`.
  - **Theorem 3**: "there is a unital ∗-homomorphism θ: B(∂S) → Z(N) with ultraweakly dense
    range such that θ(â) = ctr(a) and τ(θ(f)a) = ∫ f(λ)λ(a)dμ_τ = ∫ f â dμ_τ for every a ∈ A
    and τ ∈ S. … In particular, A^st ∩ Z(N) = {θ(f) : f ∈ Z(Aff(S))}."
  - Line 156: "When ∂S is closed (i.e., when S is a Bauer simplex), one has Aff(S) = C(∂S) and
    Z(Aff(S)) = C(∂S). However in general, the center Z(Aff(S)) can be trivial."
  - Lines 620–662 (Section 4: `‖a‖_{2,S} = sup over ∂S`, Lemma 10) and 730–760 (Section 5).
- **Vaccaro.** A. Vaccaro, arXiv:2604.24682v2, MSI copy lines 60–135 and 240–330.
  - Theorem B (lines 89–91): separable simple unital non-elementary stably finite, stable
    rank one and tlfnd give uniform property Γ.
  - Lines 105–114: "it is not known whether nuclear C∗-algebras that do not have locally
    finite nuclear dimension exist".
  - Definitions 1.1–1.3.
- **DHTW.** M. Dadarlat, I. Hirshberg, A. S. Toms, W. Winter, *The Jiang–Su algebra does not
  always embed*, arXiv:0712.2020. Read in full (4 pages) from the MSI copy in
  `lit/ex-toms-winter/`.
  - Theorem: "There is a unital simple nuclear infinite dimensional C∗-algebra (in fact, an
    AH algebra) into which the Jiang-Su algebra does not embed unitally."
  - The limit admits no unital `*`-homomorphism from `Z_{3,4}`. Its blocks are
    `(e_j ⊕ f_j)(C((S²)^{m(j)}) ⊗ K)(e_j ⊕ f_j)` with rank-one projections `e_j, f_j`.
- **Standard, not re-read.** The Winter–Zacharias structure theorem for order zero maps
  (`φ = hπ`, and `φ^{1/2} = h^{1/2}π` is order zero). Order zero lifting (projectivity of
  `C_0((0,1]) ⊗ M_N`). The barycentre formula on Bauer simplices.

## 0. Conventions

- `A` is unital and separable, and `S = T(A)` is a nonempty Bauer simplex with extreme boundary
  `K`, compact and metrizable. `μ_τ` is the representing measure of `τ`.
- Continuous affine functions on `T(A)` are exactly the affine extensions of `C(K)`, with
  `f(τ) = ∫_K f dμ_τ`.
- For `λ ∈ K`, write `λ` also for its normal extension to `N`, `‖x‖_{2,λ} = λ(x*x)^{1/2}`, and
  `‖x‖_{2,u} = sup_{λ∈K} ‖x‖_{2,λ}`.
- Traces on `M_k(A)` are unnormalized. RD_b is as in
  `ultrapower-comparison-with-rank-density-divides-projections`. `A^U` is the uniform tracial
  ultrapower.

**Definition 1.1.** The unit of `A` is *tracially `N`-divisible* if for every `ε > 0` there is a
c.p.c. order zero map `φ: M_N → A` with `τ(φ(1)) > 1 − ε` for all `τ ∈ T(A)`.
- This holds iff there is a unital `*`-homomorphism `M_N → A^U`.
- (⇐) Lift by projectivity; Fact 0 of `research/artifacts/tw-invisible-gamma-support-gap-2026-09-12.md`
  gives `lim_U sup_τ τ(1 − φ_m(1)) = 0`.
- (⇒) `‖1 − φ_m(1)‖²_{2,u} ≤ sup_τ τ(1 − φ_m(1))`, so the induced order zero map sends `1` to `1`
  and is a `*`-homomorphism.

**Lemma 1.2.** Let `φ: M_N → A` be c.p.c. order zero, `h = φ(1)` and `e_j = φ(e_jj)`. Then the
`e_j` are pairwise orthogonal, `Σ_j e_j = h`, and every tracial state `τ` satisfies
`τ(e_j) = τ(h)/N` and `τ(e_j − e_j²) = τ(h − h²)/N`.

*Proof.* Write `φ = hπ` with `π` a `*`-homomorphism commuting with `h`. Then
`φ(x)φ(y) = hφ(xy)`, which gives orthogonality, and `e_j² = h²π(e_jj)`.
- Put `v_j = φ^{1/2}(e_1j)` and `w_j = φ(e_1j)`, both in `A`.
- Then `v_j*v_j = e_j`, `v_jv_j* = e_1`, `w_j*w_j = e_j²` and `w_jw_j* = e_1²`.
- Traciality gives `τ(e_j) = τ(e_1)` and `τ(e_j²) = τ(e_1²)`. Summing, `τ(h) = Nτ(e_1)` and
  `τ(h²) = Nτ(e_1²)`. ∎

## 1. Theorem 1

**Theorem 1.** Let `A` be unital and separable with `T(A)` a nonempty Bauer simplex. If the
unit of `A` is tracially `N`-divisible for arbitrarily large `N`, then `A` has RD_b.

*Proof.*

*Step 0 (one matrix size).* Let `f: T(A) → [0,k]` be continuous affine.
- Put `f_r = min(max(f|_K − (r−1), 0), 1) ∈ C(K,[0,1])` for `r = 1, …, k`, extended affinely.
- Then `Σ_r f_r = f`. Realize each `f_r` in `A` with error `η/k`, and take the direct sum in
  `M_k(A)`. So assume `k = 1` and `f ∈ C(K,[0,1])`.

*Step 1 (a divided unit).* Fix `η ∈ (0,1)`.
- Choose `N ≥ 8/η` for which the unit is tracially `N`-divisible, and `φ` with
  `τ(1 − h) < η/8` for all `τ`. Let `e_j` be as in Lemma 1.2.
- For `λ ∈ K`: `λ(e_j) ≤ 1/N`, and `Σ_j λ(e_j − e_j²) = λ(h − h²) ≤ λ(1 − h) < η/8`.

*Step 2 (central step functions).*
- Choose a partition of unity `φ_1, …, φ_I ∈ C(K,[0,1])` such that `f` varies by less than
  `η/4` on the support of each `φ_i`. Pick `λ_i` in the support of `φ_i` and put
  `r_i = ⌊N f(λ_i)⌋ ∈ {0, …, N}`.
- For `j = 1, …, N` put `ψ_j = Σ_{i : r_i ≥ j} φ_i ∈ C(K,[0,1])` and `z_j = θ(ψ_j)`.
- By Theorem 3 and the Bauer property, `z_j ∈ A^st ∩ Z(N)`, and `λ(z_j a) = ψ_j(λ)λ(a)` for
  `a ∈ A` and `λ ∈ K` (take `τ = λ`, so `μ_λ = δ_λ`).
- Put `B = Σ_j z_j e_j`. Since the `z_j` are central contractions and the `e_j` are orthogonal:
  - `0 ≤ B ≤ h ≤ 1`;
  - `B − B² = Σ_j (z_j − z_j²)e_j + Σ_j z_j²(e_j − e_j²)`.

*Step 3 (estimates at extreme traces).* Fix `λ ∈ K` and let `I_λ = {i : φ_i(λ) > 0}`.
- For `i ∈ I_λ`, `|f(λ_i) − f(λ)| < η/4`. So `|r_i/N − f(λ)| < η/4 + 1/N`, and any two such
  `r_i` differ by less than `Nη/2 + 1`.
- `0 < ψ_j(λ) < 1` forces `min_{I_λ} r_i < j ≤ max_{I_λ} r_i`. That happens for fewer than
  `Nη/2 + 1` indices `j`.
- **Defect.** `λ(B − B²) = Σ_j (ψ_j − ψ_j²)(λ)λ(e_j) + Σ_j ψ_j(λ)²λ(e_j − e_j²)
  ≤ (1/4N)(Nη/2 + 1) + η/8 ≤ η/8 + η/32 + η/8 < η/3`.
- **Profile.** `Σ_j ψ_j = Σ_i φ_i r_i`, so `λ(B) = (λ(h)/N) Σ_i φ_i(λ) r_i`.
  - The average `Σ_i φ_i(λ) r_i/N` lies in `[0,1]` and within `η/4 + 1/N ≤ 3η/8` of `f(λ)`.
  - `|λ(h) − 1| < η/8`. So `|λ(B) − f(λ)| < η/2`.

*Step 4 (back into `A`).*
- Since `A^u = A^st`, each `z_j` is the uniform 2-norm limit of a norm-bounded sequence in `A`.
  Take real parts and apply a polynomial uniformly close to `t ↦ min(max(t,0),1)` on the bounded
  spectral range. For polynomials `p` and elements of norm at most `C`,
  `‖p(x) − p(y)‖_{2,u} ≤ L_p(C)‖x − y‖_{2,u}`. This gives positive contractions `c_j ∈ A`
  with `‖c_j − z_j‖_{2,u} < η/(12N)`.
- Put `b = Σ_j e_j^{1/2} c_j e_j^{1/2} ∈ A`. Then `0 ≤ b ≤ Σ_j e_j ≤ 1`.
- Since `e_j^{1/2} z_j e_j^{1/2} = z_j e_j`, `‖b − B‖_{2,λ} ≤ Σ_j ‖c_j − z_j‖_{2,λ} < η/12`.
- So `|λ(b) − λ(B)| < η/12`. Also `|λ(b − b²) − λ(B − B²)| ≤ 3‖b − B‖_{2,λ} < η/4`, from
  `b² − B² = b(b − B) + (b − B)B` and Cauchy–Schwarz.
- Hence `λ(b − b²) < 7η/12` and `|λ(b) − f(λ)| < 7η/12` for every `λ ∈ K`.

*Step 5 (all traces).* `b` and `b²` lie in `A`, so for `τ ∈ T(A)`,
`τ(b − b²) = ∫_K λ(b − b²)dμ_τ ≤ 7η/12` and `|τ(b) − f(τ)| ≤ ∫_K |λ(b) − f(λ)|dμ_τ ≤ 7η/12`. ∎

**Remarks.**
- **Where Bauer is used.** Only through `θ(C(K)) ⊂ A^st ∩ Z(N)`. In general
  `A^st ∩ Z(N) = θ(Z(Aff(T(A))))`, and the affine center can be trivial. Non-Bauer simplices
  were not examined.
- **Why no comparison is needed.** The pieces `z_j e_j` commute exactly, so the defect is
  computed by functional calculus. Comparison is only used afterwards, to move projections.
- **Relation to CETW Corollary 3.2 (credit).** CETW (arXiv:1912.04207, Section 3, read on MSI,
  lines 642–740) show that on Bauer simplices it suffices "to tracially divide the unit in an
  approximately central fashion": uniform Γ holds iff for each `n` there are central projections
  `p_1, …, p_n ∈ A^ω ∩ A'` summing to `1` with `τ(p_i) = 1/n` for all limit traces. Their
  Question 3.5 asks the same for general Choquet simplices. Theorem 1 is the non-central
  analogue of that mechanism: a non-central tracial division of the unit gives near projections
  of every continuous profile, but not Gamma.
- **Where the hypothesis holds.**
  - Unital limits of `M_{n_i}(C(X_i))` with `n_i → ∞`.
  - Algebras with a unital simple infinite-dimensional unique-trace subalgebra (Lemma 3.1).
  - Algebras with unital `Z_{n,n+1}` for arbitrarily large `n` (Lemma 3.2).

## 2. Theorem 2

**Theorem 2.** Let `A` be unital, simple, separable, nuclear and non-elementary, with `T(A)`
a nonempty Bauer simplex, tlfnd and strict comparison. Then (a)–(e) of the Outcome are
equivalent.

*Proof.*
- **(e) ⟹ (c).** Theorem 1.
- **(c) ⟹ (b).** Each step is an established claim.
  1. Strict comparison gives PC in every `M_k(A^U)` (`strict-comparison-compares-ultrapower-projections`).
  2. PC and RD_b give PD (`ultrapower-comparison-with-rank-density-divides-projections`).
  3. Strict comparison and RD_b give TSP (`strict-comparison-with-rank-density-gives-support-projections`).
  4. TSP, PD and tlfnd give uniform Gamma (`uniform-gamma-iff-tracial-support-projections-and-division`, part (b)).
- **(b) ⟹ (a).** CETW Theorem A (`uniform-gamma-algebras-satisfy-toms-winter`).
- **(a) ⟹ (d).** `Z` has a unique trace and `π_{τ_Z}(Z)'' ≅ R`. Kaplansky density and order
  zero lifting give c.p.c. order zero `φ_m: M_N → Z` with `τ_Z(1 − φ_m(1)) → 0`.
  - Every trace of `A ⊗ Z` restricts to `τ_Z` on `1 ⊗ Z`.
  - Transport `1 ⊗ φ_m` through `A ⊗ Z ≅ A` and apply Definition 1.1.
- **(d) ⟹ (e).** Trivial. ∎

**A second chain for (c) ⟹ (b).**
- RD_b gives rank density, through the spectral estimates of
  `rank-density-is-quadratic-trace-selection`.
- Strict comparison then gives purity (`rank-density-and-strict-comparison-give-purity`).
- Lin's pure dichotomy gives stable rank one, as recorded on
  `stw27-strict-comparison-non-pure-algebra-exists`; not re-read.
- Vaccaro's Theorem B gives uniform Gamma from stable rank one and tlfnd.

This corroborates (c) ⟹ (b). It also shows that `toms-winter-holds-on-tlfnd-rank-density-locus`
follows from Lin, Vaccaro Theorem B and CETW. That settles the relation to rank surjectivity
left unchecked there: under strict comparison RD_b gives purity, hence stable rank one, hence
surjectivity (Thiel).

**On tlfnd.** Locally finite nuclear dimension implies tlfnd. Vaccaro records that no nuclear
algebra without locally finite nuclear dimension is known. So among known nuclear algebras,
this locus is the Bauer-simplex case of Toms–Winter.
