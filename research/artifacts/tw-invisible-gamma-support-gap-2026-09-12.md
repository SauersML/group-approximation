# Tracial support gap: an ultrapower invariant beyond projections that detects failure of uniform Gamma (2026-09-12)

Lane `tw-invisible-gamma-failure`.

**Task.** Decide `gamma-failure-invisible-to-projection-comparison`. Either find
an invariant beyond projections that detects failure of uniform property Gamma
in the uniform tracial completion, or prove that strict comparison forces
uniform Gamma in a new case.

**Outcome.** The claim is not decided. This artifact proves three statements
and uses them to cut the claim down on one locus.

1. **Theorem 1.**
   - (a) Uniform Gamma implies two ultrapower properties: tracial support
     projections (TSP) and projection division (PD).
   - (b) Under tracially locally finite nuclear dimension, TSP and PD together
     give uniform Gamma.
   - TSP is a single-element existence property with a finite-stage form, the
     support gap `γ_A(a)`.
2. **Theorem 2.** Projection comparison in the tracial ultrapower (PC), together
   with bounded rank density (RD_b), gives PD.
3. **Corollary 3.**
   - A positive support gap certifies failure of uniform Gamma. It is not a
     comparison certificate, so `strict-comparison-compares-ultrapower-projections`
     does not blind it.
   - On the locus of tracially locally finite nuclear dimension with RD_b, the
     witnesses to the claim are exactly the algebras with PC and some positive
     support gap.
   - So `(Q_tr)` there is equivalent to "PC forces TSP"
     (`comparison-forces-tracial-support-projections`).

**On the suggested positive case.** Poulsen-simplex AH algebras with Toms-type
doubling maps are already covered: `simple-ah-strict-comparison-is-z-stable`
makes every unital simple AH algebra with strict comparison Z-stable, whatever
its trace simplex, and Z-stability gives uniform Gamma. No new cell there.

## Sources and what was read

- **CETW.** J. Castillejos, S. Evington, A. Tikuisis, S. White, *Uniform property
  Gamma*, arXiv:1912.04207. Pages 14–28 were read from the arXiv PDF.
  - Definition 4.1 (CPoU).
  - Definition 4.2: A is uniformly McDuff if there is a unital embedding
    `M_n → A^ω ∩ A'` for each `n`.
  - Remark 4.3(ii).
  - Lemma 4.4.
  - Theorem 4.6: for separable nuclear `A` with no finite-dimensional quotients
    and `T(A)` nonempty and compact, CPoU, uniformly McDuff and uniform
    property Gamma are equivalent. The implication (ii)⇒(iii) is proved on
    page 20 through (4.19).
  - Theorem 5.5 (Winter): tracial `m`-almost divisibility plus locally finite
    nuclear dimension gives uniform Gamma.
  - Question 3.5 and Question 5.8.
  - A text copy of the PDF is on MSI at
    `/projects/standard/hsiehph/sauer354/lit/toms-winter/1912.04207.txt`.
- **Vaccaro.** A. Vaccaro, *Stable rank one, tracial local homogeneity and
  uniform property Gamma*, arXiv:2604.24682v2. Pages 1–12 were read from the
  arXiv PDF, and the MSI text copy `2604.24682.txt`, lines 281–529, confirms the
  statements.
  - Definition 1.2 (uniformly McDuff).
  - Definition 1.3: `a ∈ A_{1,+}` is tracially almost divisible if for every `n`
    and `ε` there is a c.p.c. order zero `φ: M_n → closure(aAa)` with
    `τ(φ(1_n)) ≥ τ(a) − ε` for all `τ ∈ T(A)`. The algebra is tracially almost
    divisible if every `a ∈ M_m(A)_{1,+}` is, for all `m`.
  - Definition 1.5: tracially locally finite nuclear dimension (tlfnd).
  - Proposition 1.6: (1) uniformly McDuff implies (2) tracially almost
    divisible, for separable simple unital non-elementary `A` with `T(A) ≠ ∅`.
    Under tlfnd, (2) implies (1).
  - Lemma 2.1 and Proposition 2.2: real rank zero of `A^U` gives tracial almost
    divisibility. The proof uses real rank zero twice, once for an approximate
    unit of projections in `closure(aA^Ua)` (2.3) and once for Zhang's division
    lemma (2.8).
  - Theorem 2.3.
- **Standard fact.** C.p.c. order zero maps from `M_n` lift through surjective
  *-homomorphisms. This is Winter's Proposition 1.2.4, used exactly this way in
  the proof of Vaccaro's Proposition 1.6.
- Winter's Lemma 5.11 (Invent. Math. 2012) was not re-read. It enters only
  through Vaccaro's Proposition 1.6.

## 0. Conventions

- **The algebra.** `A` is unital, simple, separable, nuclear and
  non-elementary, with `T(A) ≠ ∅`. Traces on `M_k(A)` are unnormalized,
  `τ ⊗ Tr_k`.
- **The ultrapower.** `A^U` is the uniform tracial ultrapower along a free
  ultrafilter `U`, and `M_k(A)^U = M_k(A^U)`.
- **Limit traces.** `σ = lim_U τ_m`.
- **Hereditary pieces.** For `a ∈ M_k(A)_{1,+}` write `her_A(a) = closure(a M_k(A) a)`.
  Write `her(a)^U` for the image of `ℓ^∞(her_A(a))` in `M_k(A^U)`. It is a
  C*-subalgebra, and `b y b ∈ her(a)^U` whenever `b ∈ her(a)^U` and `y ∈ M_k(A^U)`.

**Fact 0.** Let `x = [(x_m)] ∈ M_k(A^U)` be self-adjoint. Then
`lim_U sup_τ τ(x_m) = sup_σ σ(x)` over limit traces, since maximizing traces
exist at each `m`. If `x ≥ 0` and `σ(x) = 0` for every limit trace, then
`x = 0`, because `‖x‖²_{2,u} ≤ ‖x‖ · sup_σ σ(x)`.

## 1. Definitions

- **(TSP) tracial support projections.** For every `k`, every
  `a ∈ M_k(A)_{1,+}` and every `ε > 0`, there is a projection `p ∈ her(a)^U` with
  `σ(p) ≥ σ(a) − ε` for every limit trace `σ`.
- **Support gap.** For `a ∈ M_k(A)_{1,+}`,

  ```text
  γ_A(a) = inf over positive contractions b ∈ her_A(a) of
           max{ sup_τ τ(b − b²),  sup_τ (τ(a) − τ(b)) }.
  ```

- **(PD) projection division.** For all `k, n`, every projection
  `p ∈ M_k(A^U)` admits a unital *-homomorphism `M_n → p M_k(A^U) p`.
- **(PC) projection comparison**, as in `tracial-projection-comparison-forces-uniform-gamma`.
  For every `k`, projections `p, q ∈ M_k(A^U)` with `σ(p) ≤ σ(q)` for all limit
  traces satisfy `p ≾ q`.
- **(RD_b) bounded rank density.** For every `k`, every continuous affine
  `f: T(A) → [0, k]` and every `η > 0`, there is a positive contraction
  `b ∈ M_k(A)` with `sup_τ |τ(b) − f(τ)| < η` and `sup_τ τ(b − b²) < η`.
  This is the quadratic selection form of rank density
  (`rank-density-is-quadratic-trace-selection`), with the matrix size held
  fixed.

**Lemma A (finite-stage form).** For `a ∈ M_k(A)_{1,+}`, TSP holds for `a` iff
`γ_A(a) = 0`. When `γ_A(a) = 0` the projection can be chosen with `σ(p) ≥ σ(a)`.

*Proof.*
- (⇐) Choose positive contractions `b_m ∈ her_A(a)` whose defect and deficit are
  both below `1/m`, and put `p = [(b_m)]`. Since `0 ≤ b − b² ≤ 1/4` gives
  `(b − b²)² ≤ (b − b²)/4`, we get `‖p − p²‖²_{2,u} ≤ lim_U sup_τ τ(b_m − b_m²)/4 = 0`.
  So `p` is a projection in `her(a)^U`, and `σ(p) = lim τ_m(b_m) ≥ σ(a)`.
- (⇒) Lift `p` to a self-adjoint sequence in `ℓ^∞(her_A(a))`. Clip it with
  `f(t) = min(max(t, 0), 1)`; since `f(0) = 0`, the clipped `b_m` stay in
  `her_A(a)`, and `[(b_m)] = f(p) = p`. By Fact 0, `lim_U sup_τ τ(b_m − b_m²) = 0`
  and `lim_U sup_τ (τ(a) − τ(b_m)) ≤ ε`. Hence `γ_A(a) ≤ 2ε` for every `ε`. ∎

**Sanity check (non-simple, not a witness).** In `C([0,1])` take `a = id`.
- **The bound.** Let `b ∈ C_0((0,1])` have defect `D = sup (b − b²) < 1/4`.
  Then `b` never takes values in the open middle interval where `t − t² > D`.
  Since `b(0) = 0` and `[0,1]` is connected, `b ≤ r(D) ≤ 2D`, and the deficit
  at `x = 1` is at least `1 − 2D`. So `γ(a) ≥ 1/4`.
- **The point.** TSP is a genuine regularity condition. It concerns existence
  inside the hereditary subalgebra of one element.

## 2. Theorem 1

**Theorem 1.** Let `A` be as in Section 0.
- (a) If `A` has uniform property Gamma, then TSP and PD hold. Equivalently,
  `γ_A(a) = 0` for every `a` and PD holds.
- (b) If `A` has tracially locally finite nuclear dimension, then TSP and PD
  imply uniform property Gamma.

*Proof of (a).*

*Step 1 (McDuff).* By CETW Theorem 4.6 there is a unital *-homomorphism
`Φ_0: M_N → A^U ∩ A'` for each `N`. Put `Φ = diag_k(Φ_0): M_N → M_k(A^U)`.
- `Φ` commutes with `M_k(A)`.
- For every tracial state `σ` of `M_k(A^U)` and every `y ∈ M_k(A)`, write
  `e_i = Φ(e_ii)`. Then
  `σ(y e_i) = σ(Φ(e_1i) y Φ(e_i1)) = σ(y e_1)`, so `σ(y e_i) = σ(y)/N`.

*Step 2 (PD).* Let `p ∈ M_k(A^U)` be a projection, represented by `(p_m)`.
- Lifting `Φ_0` gives c.p.c. order zero maps `M_n → A`. These asymptotically
  commute in `‖·‖_{2,u}` with any prescribed finite subset of `A`, and have
  `‖1 − φ(1)‖_{2,u}` small.
- At index `m`, choose one commuting within `1/m` with the entries of `p_m`,
  and take its diagonal amplification. The resulting sequence defines a unital
  order zero map, hence a *-homomorphism `Φ': M_n → M_k(A^U) ∩ {p}'`.
- Then `x ↦ pΦ'(x)` is a unital *-homomorphism `M_n → p M_k(A^U) p`.

*Step 3 (TSP).* Fix `a ∈ M_k(A)_{1,+}` and `ε ∈ (0, 1)`. Put `η = δ = ε/(3k)` and
`N ≥ 3k/ε`.

**The element.**
- Put `t_i = η + (1 − η)(i − 1/2)/N ∈ [η, 1]` and `h = Σ_i t_i e_i`. Then `h`
  commutes with `a`.
- Let `μ_σ` be the spectral measure of `a` under `σ`, of mass `k`. Step 1 and
  density of `span{f ⊗ g}` in `C([0,1]²)` give, for every `F ∈ C([0,1]²)`,

  ```text
  σ(F(a,h)) = (1/N) Σ_i ∫ F(s, t_i) dμ_σ(s).
  ```

- Put `g_δ(u) = min(1, max(0, u/δ))`, `F_δ(s,t) = g_δ(s − t)` and `e = F_δ(a,h)`.

**Heredity.**
- `F_δ(s,t) = 0` whenever `s ≤ η`, since `t ≥ η`.
- So `G = F_δ/s`, extended by `0` for `s ≤ η`, is continuous with `‖G‖ ≤ 1/η`.
- Hence `e = a^{1/2} G(a,h) a^{1/2}`. Representatives `a^{1/2} y_m a^{1/2}` lie in
  `her_A(a)`, so `e ∈ her(a)^U`.

**Defect.**
- `(g − g²)(u) ≤ 1_{0<u<δ}`, and an open interval of length `δ` contains at most
  `δN/(1−η) + 1` of the points `t_i`.
- So `σ(e − e²) ≤ k(δ/(1−η) + 1/N) ≤ ε`.

**Trace.**
- `g_δ(s − t) ≥ 1_{t ≤ s−δ}`, and `#{i : t_i ≤ c} ≥ N(c − η) − 1`.
- So `σ(e) ≥ ∫ (s − δ − η − 1/N) dμ_σ(s) ≥ σ(a) − ε`.

**Conclusion.** Lift and clip `e` as in Lemma A. By Fact 0, `γ_A(a) ≤ 2ε` for
every `ε`, so Lemma A gives TSP. ∎

*Proof of (b).* Fix `k`, `a ∈ M_k(A)_{1,+}`, `n` and `ε`.
1. **Support projection.** TSP gives a projection `p ∈ her(a)^U` with
   `σ(p) ≥ σ(a) − ε/2`.
2. **Division.** PD gives a unital *-homomorphism `Φ: M_n → p M_k(A^U) p`.
   Since `pyp ∈ her(a)^U`, `Φ` is a c.p.c. order zero map into `her(a)^U`, and
   `Φ(1) = p`.
3. **Lift.** `her(a)^U` is the image of the C*-algebra `ℓ^∞(her_A(a))`. By order
   zero lifting there are c.p.c. order zero `φ_m: M_n → her_A(a)` with
   `[(φ_m(1))] = p`.
4. **Traces.** By Fact 0, `lim_U sup_τ (τ(a) − τ(φ_m(1))) ≤ ε/2`. So for
   `U`-many `m`, `τ(φ_m(1)) > τ(a) − ε` for all `τ`.
5. **Conclusion.** Every `a` is tracially almost divisible, so `A` is tracially
   almost divisible (Vaccaro Definition 1.3). Under tlfnd, Vaccaro's
   Proposition 1.6 (2)⇒(1) makes `A` uniformly McDuff, and CETW Theorem 4.6 then
   gives uniform Gamma. ∎

**Remark (single-element McDuff).** The proofs of 1(a) Step 3 and 1(b) use a
unital `M_N` only through its commutation with the single element `a`. Say `A`
is *single-element McDuff* if for all `k, N` and `a ∈ M_k(A)_{1,+}` there is a
unital *-homomorphism `M_N → M_k(A^U) ∩ {a}'`.
- Such an algebra has TSP, by Step 3 verbatim.
- It is tracially almost divisible: `c ↦ a^{1/2}Φ(c)a^{1/2}` is order zero with
  value `a` at `1`, then lift.
- So under tlfnd: uniform Gamma ⇔ single-element McDuff ⇔ TSP plus PD.

## 3. Theorem 2: comparison and bounded rank density divide projections

**Theorem 2.** If `A` has PC and RD_b, then PD holds.

*Proof.* Let `p ∈ M_k(A^U)` be a projection and `n ≥ 1`.
1. **Profile.** Represent `p` by positive contractions `p_m ∈ M_k(A)` with
   defect tending to `0`. Then `f_m(τ) = τ(p_m)/n` is continuous affine with
   values in `[0, k]`.
2. **Near projections.** RD_b gives positive contractions `b_m ∈ M_k(A)` with
   profile error and defect below `1/m`. So `e' = [(b_m)]` is a projection with
   `σ(e') = σ(p)/n` for every limit trace.
3. **First piece.** By PC, `e' ≾ p`. Take `e_1 = v_1 v_1* ≤ p` with
   `v_1* v_1 = e'`.
4. **Induction.** For `j < n − 1`, the projection `p − (e_1 + … + e_j)` has
   profile `(n − j) σ(p)/n ≥ σ(e')`. PC gives `e_{j+1}` under it, equivalent to
   `e'`.
5. **The remainder.** `r = p − Σ_{i<n} e_i` has profile `σ(e')`. PC gives `w`
   with `w*w = e'` and `ww* ≤ r`. Then `r − ww*` vanishes on every limit trace,
   so `r = ww*` by Fact 0. Put `e_n = r`.
6. **Matrix units.** With partial isometries `w_i*w_i = e'` and `w_i w_i* = e_i`,
   the elements `E_ij = w_i w_j*` form matrix units of a unital `M_n` inside
   `p M_k(A^U) p`. ∎

This is Section 4.1 of `research/artifacts/toms-winter-tracial-ultrapower-comparison-2026-09-12.md`
applied to corners.
- The matrix size is held fixed so that PC applies in one amplification.
- Strict comparison is replaced by PC.

## 4. Corollary 3 and what it changes

**Corollary 3.** Let `A` be as in Section 0.
1. **Certificate.** If `γ_A(a) > 0` for some `a ∈ M_k(A)_{1,+}`, then `A` does
   not have uniform property Gamma (Theorem 1(a)).
2. **Certificates.** The support gap is an existence invariant under a single
   element, not a pair of non-subequivalent projections. So the argument of
   `strict-comparison-bundle-certificate-vanishes` does not rule it out for
   strict-comparison algebras. Whether strict comparison forces `γ_A ≡ 0` is
   open in general.
   - It does hold on algebras with locally finite nuclear dimension (norm, not
     tracial) and rank density, through
     `rank-density-and-strict-comparison-give-purity`, Winter's pure theorem and
     CETW Theorem 5.6.
   - So a strict-comparison certificate `γ_A(a) > 0` can only live off that
     locus, e.g. with tracially but not norm locally finite nuclear dimension,
     or without rank density.
3. **Witnesses.** Suppose `A` has tlfnd and RD_b. Then `A` witnesses
   `gamma-failure-invisible-to-projection-comparison` iff `A` has PC and
   `γ_A(a) > 0` for some `a` (Theorems 1 and 2).
4. **`(Q_tr)` on the locus.** There, `(Q_tr)` is equivalent to
   `comparison-forces-tracial-support-projections`, through the route
   `lfnd-locus-gamma-via-support-projections`.

**Relations recorded, not claimed.**
- **Compared with real rank zero.** RR0 of `A^U` gives TSP: an approximate unit
  of projections `p` in `closure(aA^Ua)` with `‖pap − a‖ < ε` has `σ(p) ≥ σ(a) − ε`.
  So TSP is weaker than real rank zero of the ultrapower. Vaccaro's route
  consumes real rank zero twice, at (2.3) and at (2.8). Theorem 2 replaces the
  second use by PC and RD_b, and TSP isolates the first as a tracial
  single-element condition.
- **Toms's algebra.** It fails PC, so Corollary 3(3) says nothing about it.
  Which of TSP and PD fails there was not computed.
- **Relation to CETW Question 3.5.** That question gives central projections of
  constant trace `1/n` with no halving against `A`. TSP gives non-central
  projections under one element. The two properties are different.

## 5. Attempts on `comparison-forces-tracial-support-projections`

- **Moving rank-density projections under `a`.** PC compares projections only,
  and `a` is not a projection.
  - The dilation projection `P_a = [[a, √(a−a²)], [√(a−a²), 1−a]]` is always
    equivalent to `1_k ⊕ 0` through `[[a^{1/2}, (1−a)^{1/2}], [0, 0]]`, in any
    algebra.
  - So comparing `P_a` with anything carries no information about projections
    under `a`.
- **Spectral cutoffs.**
  - `g(a)` for a steep `g` is a near projection only where the spectral
    distributions of `a` put uniformly small mass near the cutoff.
  - For `a` from a finite stage of a doubling or AH system, branch traces
    concentrate on single points of that stage. This gives atoms of mass at
    least `1/(stage rank)` at every eigenvalue level swept by the stage.
  - So no uniform cutoff level exists. Splitting those atoms is exactly TSP.
- **Commuting diffuse element.** Theorem 1(a) Step 3 builds TSP from any unital
  `M_N` commuting with `a`.
  - PD supplies unital `M_{2^j}` in `M_k(A^U)`, but not commuting with `a`.
  - Conjugating one into `{a}'` is single-element McDuff, which under tlfnd is
    equivalent to uniform Gamma itself.
- **Bauer boundary (heuristic).** In the W*-bundle picture, TSP asks for a
  2-norm continuous selection, over the extreme boundary, of subprojections of
  the support of `a` of trace at least `τ(a)`.
  - Locally trivial pieces admit it, by the partition-of-unity construction of
    `trivial-r-fibre-bundles-compare-equal-trace-projections` inside `{a}'`.
  - Failure should localize where non-triviality does. This was not proved.

## Trust surfaces

- **Proofs.** Sections 1–3 are elementary. They rest on CETW Theorem 4.6,
  Vaccaro Proposition 1.6 and order zero lifting. None has been independently
  reviewed, and nothing is in Lean.
- **How the sources were read.**
  - The source statements were read from the arXiv PDFs on 2026-09-12.
  - The MSI auth breaker was set during the first read, 16:10–16:25, so the
    first pass did not use the MSI copies.
  - Afterwards the MSI text copy of Vaccaro was grep-confirmed at the cited
    lines, and the CETW copy exists on MSI.
- **Novelty.** None asserted.
  - Theorem 1(b) is the proof pattern of Vaccaro's Proposition 2.2, with real
    rank zero replaced by TSP plus PD.
  - Theorem 1(a) is elementary from CETW.
  - Theorem 2 is the corner form of an existing artifact section.
- **RD_b.** It is a hypothesis. Whether AH algebras satisfy it in bounded matrix
  size was not checked: Brown–Perera–Toms build rank approximants in
  `M_∞(B)`, and compressing them into `M_k` needs large block ranks.
