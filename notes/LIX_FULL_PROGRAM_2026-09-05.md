# STW Problem LIX in Lean: the full unconditional program (2026-09-05, lead: session 6b)

USER ORDER (2026-09-05 evening): formalize the negative answer to STW Problem LIX
**fully and unconditionally, no literature inputs, beautifully**, with an Opus
team.  The previous three-target fleet (`notes/STW_THREE_TARGETS_PROGRAM_2026-09-05.md`)
is **paused and will do nothing**; every module it authored is now owned by the
lanes below.  This note is the single source of truth for this program.  Read
it fully before writing a line.

## 0. The target

Problem LIX (Schafhauser–Tikuisis–White, "Nuclear C*-algebras: 99 problems"):
*is every unital simple C*-algebra K₁-injective?*  Answer: **no**.  Source
proof: `research/artifacts/stw59-simple-ah-k1-counterexample-manuscript-2026-09-05.md`
(read §1–§6 once; the Lean route below differs from it in the places marked).

The endpoint (owner: lane `cs-endpoint`) must read, over Mathlib vocabulary
plus the repo's generic `K1Inj`:

```lean
/-- STW Problem LIX. -/
def ProblemLIX : Prop :=
  ∀ (A : Type) [CStarAlgebra A], Nontrivial A → IsSimpleCStar A → K1Inj A

theorem not_problemLIX : ¬ ProblemLIX
theorem exists_simple_unital_not_k1Inj :
    ∃ (A : Type) (_ : CStarAlgebra A), Nontrivial A ∧ IsSimpleCStar A ∧ ¬ K1Inj A
```

`IsSimpleCStar A` := every closed two-sided ideal is `⊥` or `⊤` (C*-simplicity;
**not** Mathlib's `IsSimpleRing`, although `isSimpleCStar_iff_isSimpleRing` is to
be landed as a lemma, recipe in §5.2).  `K1Inj` is
`Analysis/LIXEndpointStatement.lean`'s `K1Injective` with the canonical
spectral order pinned.  Separability is a bonus conjunct if cheap; `K₁(A) = 0`
and "order exactly two" are **out of scope** (they are not part of the LIX
answer and each needs a further topological theorem).

Everything below exists to produce ONE unitary `v` in ONE simple unital `A`
with `v ∉ U₀(A)` and `diag(v, 1) ∈ U₀(M₂(A))`
(`not_k1Inj_of_witness` in `Analysis/LIXEndpointStatement.lean`).

## 1. The mathematics, as the Lean will do it

### 1.1 Objects (all in Type 0)

* `S⁵ := unitVectors (Fin 3) ⊂ Fin 3 → ℂ` and `S⁴ ⊂ EuclideanSpace ℝ (Fin 5)`
  (`Analysis/LIXBlockProjections.lean`), `CP d :=` rank-one self-adjoint
  idempotents in `Matrix (Fin (d+1)) (Fin (d+1)) ℂ` (`Analysis/LIXProjectiveSpaceModel.lean`, GREEN).
* A complex vector bundle over a compact Hausdorff `X` **is** a continuous
  projection-valued map `p : C(X, Matrix (Fin K) (Fin K) ℂ)` (equivalently a
  projection in `Matrix (Fin K) (Fin K) C(X, ℂ)`); an isomorphism of bundles
  **is** Murray–von Neumann equivalence of projections; `Γ(X, End E)` **is** the
  corner `p M_K(C(X)) p`.  No bundle library, no Serre–Swan.
* Stage `i`: `Y_i = ∏_{j<i} CP(2^{j+1})`, `X_i = S⁴ × Y_i`,
  `H_i = ⊕_{j<i} L_{j}^{⊕ 2^{j+1}}` (`Hproj i`), `E_i = 1² ⊕ H_i` (`Eproj i`),
  `A_i := Eproj i · M(C(X_i)) · Eproj i`.  `rank E_i = 2^{i+1}`, `dim X_i = 2^{i+2}`.
* `F` over `S⁵`: `Fproj = 1₃ − x xᴴ` (rank 2).  The generator `u : S⁴ → U(2)` is
  the seam discrepancy of hemisphere frames of `U(3) → S⁵`
  (`Analysis/LIXGeneratorUnitary.lean`, `Analysis/LIXClutching.lean`): it lands
  in `U(2)`, `diag(u,1)` contracts in `U(3)` for free, and the projection
  clutched by `u` over `S⁵` is `Fproj`.  Frames: two Householder reflections
  through the normalised midpoint `(p+x)/‖p+x‖` give an explicit continuous
  `σ_p : {x : pᴴx ≠ −1} → U(3)` with `σ_p(x) e₃ = x` on each closed hemisphere
  (cs-clutching, 20:15 EDT); the old memory that this is "Bott, not
  elementary" is wrong.

### 1.2 The C*-side chain (manuscript §3–§6)

1. `w_i := u ⊕ 1_{H_i} ∈ U(A_i)`.  **Corollary 4**: `w_i ∉ U₀(A_i)`, because a
   null-homotopy of `w_i` would make the projection clutched by `w_i` over
   `S⁵ × Y_i`, namely `F ⊕ H_i`, MvN-equivalent to `1² ⊕ H_i`
   (`ClutchingObstruction` / `clutchingObstruction_of_equiv` in `LIXClutching.lean`),
   contradicting **Lemma 2** (§1.3).
2. `φ_i : A_i → A_{i+1}`, `φ_i(a)(x, z) = a(x) ⊕ (a(x_i) ⊗ 1_{L_{i+1}, z})`
   (twisted point evaluation at a point `x_i ∈ X_i` chosen so that every tail of
   `{π_{k,i}(x_i)}` is dense in `X_k`).  Injective unital *-homomorphism.
3. `A := ` the inductive limit.  **Realize it concretely**: algebraic sequential
   colimit (`Analysis/SequentialGroupColimit.lean`, GREEN, pattern) carrying the
   limit norm, then `Analysis/CStarCompletion` — or any other construction that
   yields `CStarAlgebra A`, injective unital *-homs `ι_i : A_i → A` compatible
   with `φ_i`, with dense union of images.  Nothing downstream needs more.
4. **Lemma 6 is DELETED (cs-clutching, 20:35 EDT).**  Because `connect`'s added
   block is constant in the `S⁴` coordinate, `tower.climb j 0 u = u ⊕ c_j` holds
   as an EQUALITY (induction on the tower's recursion) for a unitary `c_j` of
   `p_{H_j}` over `Y_j` alone; the generalized Corollary 4 — `u ⊕ c ∉ U₀(A_i)`
   for EVERY unitary `c` of `p_{H_i}` over `Y_i`, by the same hemisphere gluing
   with `c` carried on the north side — then gives `v_i ∉ U₀(A_i)` with no
   homotopy at all.  This removes the need for path-connectedness of the unitary
   group of `Matrix (Fin r) (Fin r) ℂ`, which is NOT in Mathlib at the pin.
   Load-bearing constraint on `connect`: evaluate at the fixed `stagePoint i`,
   never reindex through anything depending on the `S⁴` coordinate.
   Interfaces (cs-clutching, 20:45 EDT): the generator stays in `M₃` throughout —
   `genU x := (σ₊ x)ᴴ * σ₋ x` with `genU x * rk1 e₃ e₃ = rk1 e₃ e₃`, the corner
   addressed by the projection `E₂ := 1 − rankOneProj e₃`, never by
   `Matrix.submatrix`; the shape is the predicate `HasGeneratorShape i u a`
   (function-matrix `fromBlocks (pullMat prS4 u) 0 0 (pullMat prY c)`) with three
   obligations — stage 0 with empty `c`, `connect i` preserves it, hence
   `tower.climb j 0` — stated at `tower.climb j 0` from the start.
5. **Lemma 7** (`Analysis/LIXFiniteStageNullHomotopy.lean`): a unitary of a
   stage that is null-homotopic in the limit is null-homotopic in some later
   stage (Mathlib's `Unitary.mem_pathComponentOne_iff` + `Unitary.joined`).  So
   `v := ι_0(u) ∉ U₀(A)`.
6. **Simplicity** (`Analysis/LIXSimplicity.lean`): stage-wise fullness of the
   positive cut-down ⇒ every nonzero closed ideal of the limit is everything.
   Fullness of `φ_{k,i+1}(a)` for `0 ≠ a ≥ 0` in `A_k`: pick `i ≥ k` with
   `π_{k,i}(x_i)` in `{a ≠ 0}`; then the point-evaluation summand of
   `φ_{k,i+1}(a)` is nonzero at every point, and a section nonzero in every
   fibre generates the whole corner (fibres are full matrix algebras).
7. `diag(v, 1) ∈ U₀(M₂(A))`: `diag(u, 1)` contracts already in `U(3) ⊂ M₂(A_0)`
   (`LIXClutching`'s null-homotopy of `u ⊕ 1`), transported along `M₂(ι_0)`.
8. Endpoint assembly (§0).

### 1.3 The topological core: Lemma 2, mod 2, in the projection model

**Lemma 2.** For every `l` and `d : Fin l → ℕ` with every `d j` **even and
positive** (the tower has `d j = 2^{j+1}`), over `M := S⁵ × ∏_j CP(d j)` the
projections `F ⊕ p_H` and `1² ⊕ p_H` (both of pointwise rank `2 + m`,
`m = Σ d j`; note `V = 1³ ⊕ H` has rank `3 + m` — a one-character hazard) are
**not** Murray–von Neumann equivalent.

Proof shape (manuscript §2, re-cut mod 2; the route document is
`research/artifacts/stw59-obstruction-lean-routes-2026-09-05.md` §§9–11, whose
notation `γ_i` = mod-2 Chern class we keep):

* **Step A (algebra, exists).**  An MvN equivalence extends by `e ↦ s` to a
  unitary `g` of the corner of `V = 1³ ⊕ p_H` with `g e = s`
  (`Analysis/LIXObstructionComplementUnitary.lean`).
* **Step B (mapping torus).**  `W_g` over `N := S¹ × M` restricting to `V` on
  the slice, realized as a projection over `S¹ × M`.  **Settled 20:15 EDT
  (cc-lix-odd, `CharClass/MappingTorusProjection.lean`, green 8662):** the
  Whitehead-path model does NOT descend to the circle (the rotation run over
  the whole circle returns to `1` and trivialises the bundle), so the module
  CLUTCHES over the two-point equator of `S¹` — identity at one seam, `g` at
  the other — giving `W_g|_{north} = V ⊕ 0` on the nose (`mappingTorus_north`),
  with no Murray–von Neumann transport for Step D.  Gluing direction is the
  manuscript's own: northern field constant `e`, southern field the path
  (2.10) from `e` to `s`, descent condition `g e = s`; if Step A hands over `g`
  with `g s = e`, instantiate with `gᴴ`.
* **Step C (odd side).**  The manuscript's section (2.10), transported into
  `W_g`, has exactly ONE zero `z`, and near `z` the section is a **local
  homeomorphism** onto a neighbourhood of `0 ∈ ℂ^r` (inverse function theorem
  on an explicit chart; the derivative is `AlgTop/EulerLocalModel.lean`'s
  isomorphism).  Hence the mod-2 top Chern class `γ_r(W_g) ≠ 0` in `H^{2r}(N;F₂) ≅ F₂`:
  `γ_r(W) = j^*(s^* u)` with `u` the Thom class, `s^* u ∈ H^{2r}(N, N∖z)` the
  local generator (excision to the chart + a homeomorphism induces an
  isomorphism — **no degree computation**), and
  `j^* : H^{2r}(N, N∖z) → H^{2r}(N)` an isomorphism because `H^{2r}(N∖z) = 0`
  (Mayer–Vietoris recursion on the product, §4).
* **Step D (even side).**  For EVERY rank-`r` bundle `W` over `N` restricting
  to `V` on the slice, `γ_r(W) = 0`.  Route: Künneth
  `H^*(N;F₂) = Λ(t) ⊗ Λ(x) ⊗ H^*(Y;F₂)`; write `γ(W) = γ(p^*V)(1 + z·b)`,
  `z = t x`, `b ∈ H^*(Y)`; Step 1: `γ(V) = ∏_j (1 + h_j)^{d_j}` is supported in
  even `H^{4k}` because each `d_j` is even (Frobenius); Step 2: the single Wu
  relation (Wu-diag) `Sq^{2i} γ_{i+1} = Σ_{s=0}^{i} γ_{i-s} γ_{i+1+s}`, read on
  the `z`-part, plus **instability** (`Sq^{2k} b_j = 0` for `k > j`), kills every
  even-index `b_n`; Step 3: assemble `γ_r(W) = Σ_k A_{m-k} b_k = 0`.
* Contradiction ⇒ no `g` ⇒ no MvN equivalence.

**Target statement (corrected 20:40 by cc-lix-odd, green at 8667 jobs in
`CharClass/LemmaTwoStatement.lean`):** the earlier `fromBlocks` form with blocks
over `Fin 3 ⊕ HIdx` and `Fin 2 ⊕ HIdx` was ILL-TYPED (`MurrayVonNeumannEquiv`
needs both elements in one type).  The manuscript's own form is used: inside the
single algebra over `VIdx = Fin 3 ⊕ HIdx`, with `V = 1³ ⊕ H` and the unit
sections `e = (e₃, 0)`, `s = (x, 0)`,
```lean
FHmat := V − s sᴴ      -- F ⊕ H   (first block 1 − x xᴴ = STW59.Fproj, `FHmat_eq_fromBlocks`)
EHmat := V − e eᴴ      -- 1² ⊕ H  (the constant complement of e₃ inside 1³)
theorem …  : ¬ ContinuousMvNEquiv FHmat EHmat
```
with a bridge to `MurrayVonNeumannEquiv` over `Matrix VIdx VIdx C(M, ℂ)` via
cs-stages' green `matEval` (cc-lix-odd, separate module).  Step A targets
`HasStepAUnitary` (continuous `G` on `baseM`, `IsCornerUnitary (Vmat m) (G m)`,
`G (Sum.elim (aVec m) 0) = Sum.elim (bVec m) 0`).  Lemma 2 is delivered in this
shape, not as a `ClutchingObstruction`; Corollary 4 glues the explicit hemisphere
frames inside `V` rather than routing through `clutchMat`.

### 1.4 What Step C/D need, and the design that makes them cheapest

All cohomology is **mod 2 singular cohomology of the vendored tree**
(`GroupApproximation/ThirdParty/HamSandwich/SphereOddDegree/AlgebraicTopology/`,
objects of `TopCat.{0}`, `cohomologyZMod2 X n`, cup product `cochainCup`,
homotopy invariance, Mayer–Vietoris `mvShortExact`/`mvHomologyIso` for two
opens, small chains = excision).  Nothing integral, no Steenrod machinery beyond
what is listed, no K-theory, no Bott, no Poincaré duality, no CW structures.

The characteristic-class layer is built **Grothendieck-style from the
projective bundle**, so that relative cohomology is needed only for Step C:

1. `H^*(CP^n;F₂)` groups by Mayer–Vietoris on `CP^n = (CP^n ∖ pt) ∪ cell`,
   `CP^n ∖ pt ≃ CP^{n-1}`, intersection `≃ S^{2n-1}`; the degree-2 generator
   `h_n` and its compatibility under `CP^{n} ⊂ CP^{n+1}`.
2. For a line bundle `L ⊂ X × ℂ^K` (rank-one projection-valued map, i.e. a map
   `f_L : X → CP^{K-1}`): `e(L) := f_L^* h_K ∈ H^2(X;F₂)`.  Well defined on
   isomorphism classes (rotate one embedding into the other; homotopy
   invariance).  Natural.
3. **Leray–Hirsch** for `P(E) → X` (fibre `CP^{r-1}`, `ξ := e(taut)`):
   `H^*(P(E)) = ⊕_{i<r} H^*(X) ξ^i`, by Mayer–Vietoris induction over a
   **finite trivializing open cover** of the compact base (local triviality is
   free: projections at distance `< 1` are unitarily conjugate,
   `AlgTop/BundleCalculusProjection.lean`, `unitaryConj_of_norm_sub_lt_one`).
   Base case = Künneth with `CP^{r-1}`, itself by MV on the fibre.  The
   connecting map of MV is `H^*(X)`-linear for globally defined classes.
   Bootstrapping order: LH for `P(L ⊕ 1)` (fibre `CP¹`, needs only
   `H^2(CP^{K-1})`) ⇒ **Gysin sequence** of the circle bundle `S(L)` from the
   Mayer–Vietoris of `P(L ⊕ 1) = E(L) ∪ (P(L⊕1) ∖ Z)` ⇒ the RING
   `H^*(CP^n;F₂) = F₂[h]/(h^{n+1})` (`S(taut) = S^{2n+1}`) ⇒ LH in general.
4. **mod-2 Chern classes** `γ_i(E)` := coefficients of the relation
   `ξ^r + γ_1 ξ^{r-1} + ⋯ + γ_r = 0` in `H^*(P(E))`.  Naturality, **Whitney sum**
   (Hatcher VBKT Thm 3.9's argument: both `P(E) , P(E')` sit in `P(E ⊕ E')`),
   `γ(L) = 1 + e(L)`, **splitting principle** (flag bundle = iterated `P(-)`,
   `H^*(X) → H^*(Fl(E))` injective by LH), invariance under MvN equivalence.
5. **Thom class** `u ∈ H^{2r}(E, E∖0)`: from the pair `(P(E⊕1), P(E⊕1)∖Z)`,
   `Z` the zero section; `P(E⊕1) ∖ Z ≃ P(E)`, LES + LH make
   `H^{k+2r}(P(E⊕1), P(E⊕1)∖Z) ≅ H^k(X)`, generated by the lift of
   `ξ^r + Σ γ_i ξ^{r-i}`; excision `(E, E∖0) ⊂ (P(E⊕1), P(E⊕1)∖Z)`.  Then
   `z_0^* u = γ_r(E)` (Euler class = top class, by definition) and for a section
   `s` nonvanishing off `Z(s)`, `s^* u ∈ H^{2r}(X, X ∖ Z(s))` is the relative
   Euler class, natural, with `j^*(s^* u) = γ_r(E)`.
6. **Steenrod squares** `Sq^i` on `cohomologyZMod2`: cup-`i` products from
   Steenrod's explicit formula on singular simplices; natural, additive,
   `Sq^0 = id`, `Sq^n x = x ⌣ x` in degree `n`, `Sq^i = 0` above the degree;
   **Cartan formula** via the ℤ/2-equivariant acyclic-models theorem.  Then
   `Sq(e(L)) = e(L) + e(L)²` for complex line bundles (`Sq^1 e = 0` by
   naturality from `CP^{K-1}`, whose `H^3 = 0`).
7. **(Wu-diag)** from 4 + 6 and the pure `MvPolynomial (Fin n) (ZMod 2)` identity
   `Σ_{s≤i} e_{i-s} e_{i+1+s} = Σ_{|B|=i} Σ_{k∉B} y_B² y_k` (routes doc §10.3).

Steenrod squares are the single genuinely new foundation; (3)–(5) are large but
standard; everything else is bookkeeping.  **A lane that finds a cheaper route
to the same interface may take it, but must not weaken the interface.**

## 2. Lane roster

Namespace for all new topology: `GroupApproximation.CharClass`, directory
`GroupApproximation/CharClass/`, file prefixes as listed.  C*-side lanes work in
`GroupApproximation/Analysis/` on the files listed.  **A lane edits only its own
files.**  To use a peer's declaration, import their module; if it is red, tell
the lead (final report or a note in `notes/lix-lane-reports/<lane>.md`) rather
than editing it.

| lane | owns | delivers |
|---|---|---|
| `cc-cohom-api` | `CharClass/Cohomology*.lean` | element-level graded-ring API over `cohomologyZMod2` (cup, one, assoc, comm, pullback functoriality, homotopy invariance, `TopCat.of` bridging for subtypes/products), Mayer–Vietoris in element form with the `H^*(X)`-linearity of `δ`, Künneth with spheres `H^*(X × S^n)`, `H^k(S^n)` and vanishing above dimension, `H^*(X × [0,1]) ≅ H^*(X)` |
| `cc-relative` | `CharClass/Relative*.lean` | relative cochains `C^*(X,A)` for a subspace, `H^n(X,A)`, LES of a pair (natural), excision for open covers, homeomorphism invariance of pairs, `H^{n}(V, V∖0)` for an open `0 ∈ V ⊂ ℝ^n`/`ℂ^r` ≅ `F₂` via the LES and the sphere |
| `cc-steenrod` | `CharClass/Steenrod*.lean` | cup-`i` products on mod-2 singular cochains, chain-level coboundary formula, `Sq^i` on cohomology, naturality, additivity, `Sq^0 = id`, top square = cup square, instability, compatibility with the LES connecting map |
| `cc-cartan` | `CharClass/AcyclicModels*.lean`, `CharClass/Cartan*.lean` | the (ℤ/2-equivariant) acyclic-models theorem for functors `TopCat.{0} ⥤ chain complexes over ZMod 2`; the Cartan formula `Sq^k(a ⌣ b) = Σ Sq^i a ⌣ Sq^{k-i} b` for `cc-steenrod`'s squares |
| `cc-bundle` | `CharClass/Bundle*.lean` | projection-model bundles over compact Hausdorff bases: total space `E(p)`, `E(p)∖0`, sphere bundle, projective bundle `P(p) ⊂ X × CP(K-1)`, tautological line, `p ⊕ q`, pullback, `P(p) ⊂ P(p ⊕ 1)`, `E(p) = P(p⊕1) ∖ P(p)` (open), zero section, `P(p⊕1)∖Z ≃ P(p)`, local triviality, finite trivializing cover, local homeomorphisms `P(p)|_U ≅ U × CP^{r-1}`, `E(p)|_U ≅ U × ℂ^r`, invariance under MvN equivalence |
| `cc-projective` | `CharClass/ProjectiveSpace*.lean`, `CharClass/LerayHirsch*.lean`, `CharClass/Chern*.lean` | items 1–4 of §1.4: `H^*(CP^n)` groups then ring, `e(L)`, LH for `P(L⊕1)`, Gysin, LH general, Künneth with `CP^n` and with products of `CP`s and spheres, `γ_i`, naturality, Whitney, `γ(L)=1+e(L)`, splitting principle |
| `cc-thom` | `CharClass/Thom*.lean`, `CharClass/EulerLocal*.lean`, and (from 19:00 EDT) `CharClass/MayerVietoris*.lean` — the cohomological Mayer–Vietoris moved here from `cc-cohom-api` | item 5 of §1.4; the punctured-product recursion `H^{top}(N ∖ z;F₂) = 0` for `N` a product of spheres and `CP`s; `j^*` isomorphism; "one zero which is a local homeomorphism ⇒ `γ_r ≠ 0`" |
| `cc-wu` | `CharClass/Wu*.lean`, `CharClass/ParityEven*.lean` | the `MvPolynomial` identity; (Wu-diag) for `γ`; the even side Step D, first stated over an axiomatized graded `F₂`-algebra with a Steenrod-like operation and Künneth data, then instantiated |
| `cc-lix-odd` | `CharClass/MappingTorus*.lean`, `CharClass/LIXSection*.lean`, `CharClass/LemmaTwo*.lean` | Step B, Step C's section (from `AlgTop/ManuscriptSectionZeroCount.lean`, `MappingTorusSectionZeros`, `EulerLocalModel`, `CPTautologicalSection`), the local homeomorphism at the zero, and the final Lemma 2 in the `LIXBlockProjections` vocabulary plus the bridge to `LIXClutching.ClutchingObstruction` |
| `cs-stages` | `Analysis/LIXBlockProjections.lean`, `Analysis/LIXCornerAlgebra.lean`, `Analysis/LIXStageAlgebra*.lean`, `Analysis/LIXConnectingMap*.lean` | repair to green; `A_i` as `CStarAlgebra`; the dense point sequence `x_i`; `φ_i` as injective unital ⋆-homs; `φ_{k,i}`; the point-evaluation summand is nonzero everywhere once `π_{k,i}(x_i) ∈ {a ≠ 0}` |
| `cs-limit` | `Analysis/LIXLimit*.lean`, `Analysis/LIXFiniteStageNullHomotopy.lean` | the limit `A` (§1.2 item 3) with `ι_i`, density, unitality, nontriviality; Lemma 7 verified; `diag(v,1) ∈ U₀(M₂A)` transport; separability if cheap |
| `cs-simplicity` | `Analysis/LIXSimplicity.lean`, `Analysis/LIXSimplicityInstance*.lean`, `Analysis/CStarSimple*.lean` | `IsSimpleCStar`, `isSimpleCStar_iff_isSimpleRing`; `LIXSimplicity` verified; fullness for the specific tower; `IsSimpleCStar A` |
| `cs-clutching` | `Analysis/LIXClutching.lean`, `Analysis/LIXGeneratorUnitary.lean`, `Analysis/LIXObstructionComplementUnitary.lean`, `Analysis/LIXLemmaSix*.lean` | repair to green; `u` by Householder frames, `diag(u,1) ∈ U₀` by construction, Step A; the shape lemma `climb j 0 u = u ⊕ c_j` and the generalized Corollary 4 (`u ⊕ c ∉ U₀`) over `tower.climb` — Lemma 6 deleted |
| `ggt-repair` | the four red GGT consumers of `fadb6fd6d` | a green root (outside LIX) |
| `cs-endpoint` | `Analysis/CStarKOne*.lean`, `Analysis/CStarSymmetryComponent.lean`, `Analysis/LIXEndpointStatement.lean`, `Manuscript/NinetyNineProblems/ProblemLIX.lean` | repair `CStarKOne` (noncomputable) to green; `ProblemLIX`, `not_problemLIX`, the assembly; `#audit_closed_axioms` lines; the root wiring proposal (lead wires) |

The lead (this session) wires the root, runs the mutexed full builds, keeps
this note current, and arbitrates interfaces.  Interfaces between lanes are
Lean signatures; when you need one from a peer that does not exist yet, write
the signature you need into `notes/lix-lane-reports/<your-lane>.md` under
"NEEDS", and build against a local `structure`/hypothesis in the meantime —
never a `sorry`, never an `axiom`.

## 3. Standing discipline (every lane, no exceptions)

1. **Never run Lean locally.**  The build is remote only.  Your probe is
   `bash /private/tmp/claude-501/-Users-user-nonsofic-existence/0d670c23-df04-42d0-9de1-e659ef71184e/scratchpad/cc/ccprobe.sh <your-lane> GroupApproximation.<Module> [more modules]`
   — it syncs the whole local `GroupApproximation/` tree into YOUR private
   hardlink clone of the warm 25 GB cache on acn112, clears the artifacts of
   every changed module, and builds exactly the named targets on a bounded core
   set.  It takes no fleet lock and cannot damage the shared tree.  A green is
   the line `Build completed successfully (N jobs)` **with N**, and the log must
   show the module being *built*, not `Replayed`.  Do not use
   `scripts/remote-build.sh` (that is the lead's mutexed full build) and never
   a bare `msi "lake build"` in the shared tree.  Batch: author a lot, probe
   once; each probe costs a minute of sync plus the build.
2. **Mathlib pin `81a5d257` (toolchain v4.32.0).**  Check names with
   `git -C /Users/user/mathlib4 grep -n <pat> 81a5d257 -- Mathlib` and read
   files with `git -C /Users/user/mathlib4 show 81a5d257:Mathlib/<path>`.
   `rg`/`grep` on the checkout read a NEWER revision.  **Never conclude a name
   is absent from a search piped through `head`**; count with `grep -c` or read
   the file.  Deprecated aliases are ERRORS (`-DwarningAsError=true`), as are
   unused simp args, unused variables, unused section variables.
3. **No `sorry`, `admit`, `axiom`, `opaque`, `native_decide`.**  An unproved
   step is a named hypothesis of an intermediate lemma or a `structure` field,
   documented with exactly what discharges it — never in a final statement.
4. **Never edit `GroupApproximation.lean`** (the root).  Never delete or rename a
   peer's module.  Never `git reset/stash/amend/revert`, no branches, no
   worktrees; recover forward.
5. **Commit and push as you go**: `git add <your files>` (explicit paths only),
   `git commit -m "<lane>: <what>"`, `git push origin main`; if the push is
   rejected, `git pull --no-rebase origin main` then push again.  Small commits.
   Every commit message ends with the two attribution lines the lead uses:
   `Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>` and
   `Claude-Session: https://claude.ai/code/session_016pTr64vYTcyhDJXGRCQ8a8`.
6. **Vendored tree**: import `GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.…`
   modules freely; 96/102 of `AlgebraicTopology/*` and 78/90 of the top-level
   ones have oleans in the cache (check with
   `ls` on `.lake/build/lib/lean/GroupApproximation/ThirdParty/…` inside your clone
   if a probe complains).  Their conventions: spaces are `TopCat.{0}`, coefficients
   `ZMod 2`, cochains are functions on singular simplices (`CupProduct.lean:67–82`).
7. **Fleet-green modules you may import** (job counts recorded by the previous
   lead): `KTheory/{MatrixProjection,BlockMoves,Basic,Functorial}` (2965),
   `AlgTop/{ChernSeries,ChernSplitNewton,ChernEvenTopClass,ChernSquareZeroIdeal}`,
   `AlgTop/{MappingTorusParityCore,MappingTorusParity}`,
   `AlgTop/{EulerLocalModel,MappingTorusSectionZeros,EulerParityBridge,PuncturedNormedSphere}` (8664/8655),
   `Analysis/{SequentialGroupColimit,CStarMatrixBlockInclusion,LIXProjectiveSpaceModel,CStarUnitaryComponent}`.
   Everything else under `Analysis/LIX*`, `AlgTop/BundleCalculus*`,
   `AlgTop/ComplexProjective*`, `AlgTop/SingularCohomology`/`CupProduct`
   (integral) is **authored but never verified**; treat as reference material
   and re-prove what you need in your own files unless a probe shows it green.
8. **Lean gotchas recorded in memory, condensed**: `omega` does not split
   `ite`; `rw` on a unit-like type rewrites everything; a `(by omega)` argument
   inside a term leaves metavariables — bind it first; a dependent proof
   argument blocks `rw` (transport with a `_congr` lemma); `autoImplicit` can
   silently bind an unresolved name — a name that "resolves" but behaves oddly
   is probably an implicit variable (check the `open`s of a neighbouring file);
   `CStarMatrix` needs `[PartialOrder A] [StarOrderedRing A]` — supply
   `CStarAlgebra.spectralOrder` locally; state lemmas at the reducible form;
   an instance timeout usually means a missing binder; an `ext` on a sphere
   subtype should be `ContinuousMap.ext`; `Module.Basis` not `Basis` at this pin;
   a definition whose result is a CLASS (`evenAlgebra`, a graded-ring structure, an
   `Opens` carrier) must be `@[reducible]` or nothing downstream unifies against it;
   `DirectSum` carries two syntactically different `Semiring` paths, so build an
   `Algebra` structure directly rather than through `RingHom.toAlgebra`;
   `first | ring | …` never reaches later alternatives because `ring` falls back to
   `ring_nf` and "succeeds" without closing the goal — use `ring1`; `ring` is
   commutative-only (`rw [mul_sub, sub_mul]; abel` in a noncommutative ring);
   `Matrix ι ι ℂ` has NO norm instance at this pin, so local triviality of a
   projection-valued map comes from the invertible intertwiner
   `p x₀ · p x + (1 − p x₀)(1 − p x)` (open determinant condition), not from
   `‖p x − p x₀‖ < 1`; at `C(X, CStarMatrix ι ι ℂ)` bare `Mul`/`Star` resolve to
   `ContinuousMap.instMul`/`instStar`, not the `Semiring`/`StarRing` ones — state
   arithmetic over an abstract `[CStarAlgebra A]` and cross once by application;
   `NonUnitalStarAlgHom.isometry` needs an explicit `import Mathlib.Analysis.CStarAlgebra.Hom`;
   `mulRight_continuous` is a deprecated alias (use `continuous_mul_const`).
   A `git add` chained behind a command that can fail silently drops files and
   leaves a DANGLING IMPORT on main (add each file explicitly, check `git status`
   before pushing); a probe syncs the tree at LAUNCH, so reason about the built
   bytes via `git show <commit>:<path>`, not the file on disk.
9. **Report**: keep `notes/lix-lane-reports/<your-lane>.md` current (what is
   green with job counts, what is authored-unverified, NEEDS from peers, traps
   found).  Your final message to the lead must contain the same four sections.
   Green claims without a job count are not green claims.
10. **Namespaces (added 20:55 after a real collision).** Every declaration lives
    in a lane-specific sub-namespace (`GroupApproximation.CharClass.Bundle`,
    `…CharClass.CPn`, `…CharClass.Steenrod`, `…CharClass.MV`, `…STW59`, …).  A
    fully-qualified duplicate across two modules is not a type error, it makes
    the root import FAIL outright.  The lead runs the fully-qualified duplicate
    scan before every wiring; four real collisions were found at 20:55
    (`cohCast_self`, `hasSphereCohomology_sphere`, a bare `of`, a bare `is`).
11. **Do not oversubscribe acn112**: the probe already pins you to a bounded
    core range.  Never write build output to `/tmp` on the node.  Do not start
    a second probe while one of yours is running.

11. **A published signature never changes.**  Once a peer consumes a name, its statement
    is frozen; a slimmer or stronger form goes under a NEW name (old one may become a
    one-line wrapper).  Consumers switch when convenient.  (Ruled 22:58 after cc-wu slimmed
    `gamma_top_eq_zero_of_slice_totalH` while cc-lix-odd's `LemmaTwoStepD` was already green
    against it.)

## 4. Lane-specific design notes

### cc-cohom-api
The vendored `CohomologyCupProduct.lean` descends the cup product only through
`cupLeftMor`/`cupRightMor'` morphisms.  Provide `cup : H^p X → H^q X → H^{p+q} X`
as a function with `cup_mk` (class of `cochainCup`), bilinearity, associativity
(with a degree cast confined to one lemma), commutativity mod 2 (needs the
vendored Alexander–Whitney symmetry or a chain homotopy — if absent, prove it
via the acyclic-models theorem from `cc-cartan`, or restrict all downstream use
to classes pulled back from different factors, where commutativity is a cross-
product statement), `one`, naturality.  Mayer–Vietoris: from `mvShortExact`
derive the cohomology LES in element form with the connecting map `δ` and prove
`δ (a ⌣ b|_{U∩V}) = δ a ⌣ b` for `b` global.  Künneth with spheres by MV on the
sphere's two hemispheres, inductively, producing the description
`H^k(X × S^n) ≅ H^k(X) ⊕ H^{k-n}(X)` via `pr₁^*` and `(-) × σ_n`.  Bridge
lemmas: `TopCat.of` of a subtype of `Fin n → ℂ`, of a product, `Homeomorph` to
an iso of cohomology, `ContinuousMap` to `⟶`.

### cc-relative
Define `relCochain X A n := {φ : C^n(X) // φ vanishes on simplices in A}` (or
the kernel of restriction), the quotient-free LES from the short exact sequence
of cochain complexes `0 → C^*(X,A) → C^*(X) → C^*(A) → 0` (surjectivity of
restriction holds for functions on simplices).  Excision: for opens `U, V`
covering `X`, `H^*(X, U) ≅ H^*(V, U ∩ V)` — from the vendored small-chains
quasi-isomorphism (`SmallChainsQuasiIso`, `SubordinateChains`).  Maps of pairs,
functoriality, homotopy invariance for pairs if cheap.  Compute
`H^n(V, V∖0) ≅ H^{n-1}(V ∖ 0)` for an open ball/any open `0 ∈ V ⊂ ℝ^n`
(`V ≃ pt` for a ball; for general open `V` excise) and `H^{n-1}(ℝ^n∖0) ≅ H^{n-1}(S^{n-1}) ≅ F₂`.

### cc-steenrod
Cochains are functions on singular simplices `Δ^n → X`.  Use Steenrod's
formula: for `α ∈ C^p`, `β ∈ C^q`, `(α ⌣_i β)(σ) = Σ α(σ ∘ front-part) · β(σ ∘ back-part)`
summed over index sets `0 ≤ j_0 < ⋯ < j_i ≤ p+q-i`, with the two faces given by
the alternating blocks (González-Díaz–Real normal form; mod 2 no signs).  Prove
the coboundary formula `δ(α ⌣_i β) = δα ⌣_i β + α ⌣_i δβ + α ⌣_{i-1} β + β ⌣_{i-1} α`
mod 2 (a finite cancellation over face maps of the standard simplex — set it up
as an identity about sub-sequences of `Fin (n+1)` and prove it once, generally),
then `Sq^{p-i} [α] := [α ⌣_i α]`.  Deduce naturality, additivity (`(α+β)⌣_i(α+β)`
cross terms cancel by the coboundary formula), `Sq^p = ⌣`-square (`⌣_0 = ⌣`, up to
the vendored Alexander–Whitney convention), `Sq^0 = id` (`α ⌣_p α = α`
pointwise since `x² = x` in `ZMod 2`), instability (`⌣_i = 0` for `i > p`),
and compatibility with the connecting map of a pair (needed by `cc-thom` for
`Sq` on Thom classes only if the Thom-definition route is used — low priority).
Package the diagonal `Φ(e_i ⊗ σ)` as a natural ℤ/2-equivariant chain map for
`cc-cartan`.

### cc-cartan
State and prove: for functors `F, G : TopCat.{0} ⥤ ChainComplex (ModuleCat (ZMod 2)) ℕ`
with `F` free on the models `Δ^n` (a chosen basis of `F_k(Δ^n)` generates
`F_k(X)` freely under all `Δ^n → X`) and `G` acyclic on the models, any natural
augmentation-preserving map in degree 0 extends to a natural chain map, unique
up to natural chain homotopy; then the ℤ/2-equivariant variant (free over
`ZMod 2[ℤ/2]`).  Apply to `W ⊗ S(X) → S(X) ⊗ S(X)` (Steenrod's diagonal).  **Cartan is proved
INTERNALLY, on one space, with no products, no Eilenberg–Zilber and no
linearized Alexander–Whitney** (cc-cartan verified 19:43 that neither exists
anywhere and that building them is a full lane): compare the two natural
ℤ/2-equivariant chain maps `W ⊗ S(X) → S(X)^{⊗4}`, (A) `(Φ₀ ⊗ Φ₀) ∘ Φ` and
(B) `τ₂₃ ∘ (Φ ⊗ Φ) ∘ (Δ_W ⊗ Φ₀)` with `Δ_W(e_n) = Σ_{i+j=n} e_i ⊗ T^i e_j`
the coproduct of the periodic resolution.  **Action correction (cc-cartan,
20:00 EDT):** `(Φ₀ ⊗ Φ₀) ∘ Φ` intertwines `T` with the permutation `(13)(24)`
of the four factors, while `(Φ ⊗ Φ) ∘ (Δ_W ⊗ Φ₀)` intertwines it with
`(12)(34)`; so fix the `Λ`-action on `S(X)^{⊗4}` to be `(13)(24)` and put the
transposition `τ₂₃` of the middle factors in front of the second composite —
then both are equivariant for one action and both send `e₀ ⊗ x` to
`x ⊗ x ⊗ x ⊗ x`.  The `T^i` in `Δ_W` is harmless mod 2 because `β ⊗ β` is
symmetric.  One more input, owned by `cc-cartan`: a positive-degree contraction
of the singular chains of the standard simplex, `Homotopy (𝟙 (S Δ^m)) α` with
`α` vanishing in positive degrees (from acyclicity over the field `F₂` by
choosing a complement per degree), which feeds the models' acyclicity.  They agree in degree 0 and the target is contractible on models,
so they are equivariantly homotopic; evaluating the homotopy on
`a ⊗ b ⊗ a ⊗ b` is the Cartan formula.  Coordinate the exact form of `Φ` with
`cc-steenrod` early (write the signature into your report).

### cc-bundle
Work over a compact Hausdorff (in practice compact metric) `X : Type` with
`p : C(X, Matrix (Fin K) (Fin K) ℂ)` projection-valued (or the equivalent
`Matrix (Fin K) (Fin K) C(X,ℂ)`; provide both directions,
`AlgTop/BundleCalculusModelBridge.lean` has `matrixSectionEquiv` unverified).
All spaces as subtypes of products, with `TopCat.of`.  Prove the local
homeomorphisms explicitly from a local unitary `U(x)` conjugating `p(x)` to
`p(x₀)` on `{x : ‖p x − p x₀‖ < 1}`.  Give `P(p)` as
`{(x, q) : q ≤ p x, q rank one}` inside `X × CP(K-1)` with `CP` from
`Analysis/LIXProjectiveSpaceModel.lean` (GREEN; do not make a second model).

### cc-projective
Everything in §1.4 items 1–4.  The Gysin trick: for a line bundle `L` over `X`,
`P(L ⊕ 1) = E(L) ∪ (P(L⊕1) ∖ Z)`, `E(L) ≃ X`, `P(L⊕1)∖Z ≃ P(L) = X`,
`E(L) ∩ (P(L⊕1)∖Z) = E(L)∖0 ≃ S(L)`; Mayer–Vietoris plus LH for `P(L ⊕ 1)`
(basis `1, ξ`) gives `⋯ → H^{k-2}(X) →^{⌣ e(L)} H^k(X) → H^k(S(L)) → H^{k-1}(X) → ⋯`.
With `X = CP^n`, `L = taut`, `S(L) = S^{2n+1}` the ring structure follows.
Whitney: Hatcher, Vector Bundles and K-Theory, proof of Theorem 3.9 (do not
cite it; reprove it).  Splitting principle: iterate `P(-)`.

### cc-thom
Item 5 of §1.4 and the odd side.  The punctured-product recursion: for
`N = S¹ × M'`, `z = (t₀, m₀)`, cover `N∖z = (S¹∖t₀) × M' ∪ S¹ × (M'∖m₀)`;
`H^{top}(N∖z)` is a cokernel into `H^{top-1}((S¹∖t₀) × (M'∖m₀)) = H^{top-1}(M'∖m₀)`,
which vanishes by the same statement one dimension down; base cases are
`S^n ∖ pt ≃ pt` and `CP^d ∖ pt ≃ CP^{d-1}`.  State it as: for `P` in the class
generated by spheres and `CP`s under products, `H^k(P ∖ pt;F₂) = 0` for
`k ≥ dim P` — with `dim` bookkeeping and the Künneth descriptions from
`cc-cohom-api`/`cc-projective`.  Then `j^* : H^{2r}(N, N∖z) → H^{2r}(N)` is a
surjection `F₂ → F₂`, hence an isomorphism.

### cc-wu
`esymm_halfAntidiagonal_eq` exactly as in the routes doc §10.3 (generating
function `∏ (1 + 2 y_k T + y_k² T²)` over `ℤ`, halve, reduce).  Then state Step D
over a structure `ParityData` bundling: a graded commutative `F₂`-algebra
`H`, elements `t, x` with `t² = x² = 0`, a subalgebra `H_Y` with the Künneth
decomposition `H = H_Y ⊕ t H_Y ⊕ x H_Y ⊕ t x H_Y`, elements `h_j` of degree 2
with `h_j^{d_j+1} = 0`, an operation `Sq` (additive, Cartan, instability,
`Sq(h_j) = h_j + h_j²`, `Sq^{>0} t = Sq^{>0} x = 0`), and the classes `γ_i(W)`
satisfying (Wu-diag) and `γ(W)|_{slice} = ∏ (1 + h_j)^{d_j}`.  Prove
`γ_r(W) = 0`.  `cc-lix-odd`/the lead instantiate it.

### cc-lix-odd
Mapping torus: from `g` a unitary of the corner `V M_K(C(M)) V` (extended by
`1 − V` to a unitary of `M_K(C(M))` if convenient), build a continuous
`h : [0,1] × M → U(2K)`, `h_0 = 1`, `h_1 = diag(g, gᴴ)` (Whitehead rotation
formula, continuous in `g`), and `W_g := {(t, m, v) : v ∈ h_t(m)(range V(m) ⊕ 0)}`
as a projection-valued map on `S¹ × M` (`S¹` as `[0,1]/0∼1` or as the unit
circle with an explicit chart — pick what makes the section continuous).  The
section: `S(m, t) := h_t(m)((1−t)·x + t·e₃, χ(t) σ(y), 0)` arranged so the two
ends agree through `g e = s` (check the direction!).  Its zero set is the single
point given by `AlgTop/ManuscriptSectionZeroCount.lean`; near it the section is
a local homeomorphism (inverse function theorem `HasStrictFDerivAt.toOpenPartialHomeomorph` (Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean at the pin)
on an explicit chart of `S⁵ × CP^{d} × ℝ`; derivative from `EulerLocalModel`).
Deliver Lemma 2 as `¬ MurrayVonNeumannEquiv (F ⊕ p_H) (1² ⊕ p_H)` and as
`ClutchingObstruction`.

### cs-stages / cs-limit / cs-simplicity / cs-clutching / cs-endpoint
Start by probing the files you own **as they are** to learn the true red/green
state (the last probes of the previous lead: `LIXBlockProjections` red on a
type mismatch at line 124 plus deprecations, `LIXCornerAlgebra` red on
`noncomm_ring`/instances, `CStarKOne` red on missing `noncomputable`,
`CStarSymmetryComponent` red on an unsolved goal; `LIXClutching`,
`LIXGeneratorUnitary`, `LIXObstructionComplementUnitary`,
`LIXFiniteStageNullHomotopy`, `LIXSimplicity` never probed).  Fix, then extend.
Repo infrastructure map (memory, checked 2026-09-05): C*-quotients
`Analysis/CStarIdealApproximateUnit`, `CStarQuotientHom`, `CStarIdealQuotient`;
completion `Analysis/CStarCompletion`, `CStarCompletionCoe`; colimit pattern
`Analysis/SequentialGroupColimit`; unitary component
`Analysis/CStarUnitaryComponent` (`unitaryComponentOne`, `Joined 1 a ↔ mem`);
`Mathlib/Analysis/CStarAlgebra/Unitary/Connected.lean`
(`Unitary.mem_pathComponentOne_iff`, `Unitary.joined`); closed
`StarSubalgebra` is a `CStarAlgebra` via `StarSubalgebra.cstarAlgebra` with an
`IsClosed` instance.  `IsSimpleCStar ↔ IsSimpleRing` recipe: a proper two-sided
ideal of a unital Banach algebra lies in `nonunits`, which is closed
(`nonunits.isClosed`, `nonunits.subset_compl_ball`, `HasSummableGeomSeries`
from completeness), so its closure is a proper closed ideal.

## 5. Status board (lead-maintained)

| item | state |
|---|---|
| program note, probe helper, base clone | 2026-09-05 18:10 EDT: base clone `cc_clones/_base` complete (12 min cp -al), marker set |
| every lane | launched 18:05 EDT, see `notes/lix-lane-reports/` |
| 18:52 EDT Opus session limit | all fifteen Opus lanes stopped; snapshot 292620dfd; every lane relaunched on Sonnet 5 at 19:33 EDT as `<lane>-s`, same files, same clones, same rules; Opus agents resume after 22:40 EDT |
| root: `CStarSimple` + `ProblemLIX` wired | 19:05 EDT, commit 1b4a37c25 (green at 2999 jobs; `#audit_axioms` report the three classical axioms) |
| cc-wu | GREEN 19:55 EDT, 1553 jobs: the `MvPolynomial` half-antidiagonal identity, (Wu-diag) over `SqData`, Step D over `ParityData` (general "every `d_j` even" route, routes doc §12.3) |
| cs-limit | GREEN 19:51 EDT, 3000 jobs: Lemma 7, tower, completion, matrix transport, separability, `hasK1InjWitness_limit` |
| cs-simplicity | GREEN 19:50 EDT, 2988 jobs: `IsSimpleCStar`, `isSimpleCStar_iff_isSimpleRing`, positive cut-down, `isSimpleCStar_limit` from stage-wise fullness |
| C*-side funnel | everything now waits on cs-stages: `STW59.connect`, `connect_injective`, `Nontrivial (StageAlgebra 0)`, fullness in stage language; then cs-clutching's Lemma 6 / Corollary 4 / `diag(u,1)`; then Lemma 2 from the topology side |
| characteristic-class ring (20:05 EDT) | the FULL graded ring `⨁_n H^n(X;F₂)` (mod 2 no Koszul signs: `mul := cup` with no degree transport), not the even part `EvenH` — cc-wu's `ParityData` needs the degree-1 and degree-5 generators `t`, `x`. `one_cup`/`cup_assoc` green (cc-cohom-api, 8769 jobs); the single missing field is `cup_comm` in ALL degrees, owner `cc-steenrod-s` (recipe: `cochainCupI_coboundary` at `i = 0` + `cochainCupI_zero` + one cast bridge), Opus `cc-steenrod` reviewing. Fallback that needs no ring: `CharClass/LerayHirschDegree.lean` (classes degreewise). Homogeneity of `CP^{d+1}` for cc-thom's zero: a Householder construction inside the projection model (cc-projective) |
| roster at 20:10 EDT | Opus OWNS: cc-cohom-api (6 modules green 8767–8769; MV + Künneth remaining), cc-cartan (7 modules green 1674; internal Cartan comparison + simplex contraction), cc-steenrod (`cup_comm` first, at 292620dfd + an uncommitted `SteenrodCupOne.lean`), cs-limit (green 3000), cs-simplicity (green 2988), cs-endpoint (green 3002), cs-stages (`LIXCornerAlgebra`, `LIXBlockProjections`). cc-projective (Opus again from 20:25 EDT; all authored modules green 8683). Sonnet OWNS: cc-relative-s, cc-bundle-s, cc-thom-s (toolkit instantiation), cc-lix-odd-s, ggt-repair-s. Opus REVIEW-ONLY pairs: cc-relative, cc-bundle. (cs-clutching and cc-lix-odd returned to Opus 20:45.) Done: cc-wu (1553) |
| Mayer–Vietoris split (20:35 EDT) | cc-cohom-api owns the categorical dualized short exact sequence `mvCoSC`, `mvDelta`, three `ShortComplex.Exact` statements (`CharClass/CohomologyMayerVietoris.lean`); cc-thom (Opus) owns the element-form bridge `CharClass/MayerVietorisBiproduct.lean` + `MayerVietorisElement.lean` (restrictions, exactness at three spots, δ-linearity for global classes, vanishing form A1, the `MVSequence` term cc-projective consumes) |
| dualization duplicate (20:40 EDT) | THREE copies of the `Hom(−,F₂)`-exactness argument: `RelativeDual` (cc-relative), the `cohDualFunctor` block of `CohomologyMayerVietoris` (cc-cohom-api), `MayerVietorisDual` (cc-thom-s, 3c331f766); ruling: first green wins, the other two delete their copies and import it. STANDING STATE (verified against the tree 20:30): cc-cohom-api's `CohomologyMayerVietoris` (green 8768) is the single dualization — cc-thom executed the first ruling at 813ee2ec6 (deleted `MayerVietorisDual`, rebuilt `MayerVietorisBiproduct`/`Element` on `dualCx2`/`dualMap2`); a later lead reversal was VOID and withdrawn; cc-relative imports the same layer and deletes `RelativeDual`. Still owed by cc-thom for Leray–Hirsch: δ-linearity for global classes and naturality in a map of covered spaces (needs the missing chain-level map between subordinate-chain complexes) |
| cc-lix-odd | Sonnet finished 20:38 EDT: six modules green (8662/8658), Step B and the combinatorial half of Step C done, `LemmaTwoUnitary` authored (blocked on cs-clutching's red complement-unitary file); lane back with Opus |
| cc-cartan (20:50 EDT) | ten modules GREEN at 1700 jobs: acyclic models (both halves), tensor acyclicity, `AcyclicModelsSplitting` (over a field positive-degree acyclicity IS a contraction — the models' input), `CartanEvaluation` (the `(1+T)` term dies; `eval_sub_eq`), `CartanGroupRing`, the periodic resolution. Remaining: the Finsupp source functor free over the group ring (reindex the basis along the `ULift` in `TopCat.toSSet`'s simplices, in exactly the `basis`/`basis_apply` fields), the fourfold tensor with the block-swap action, the two composites; then `steenrodDiag` from cc-steenrod |
| cs-stages (20:55 EDT) | Opus owns all four files + `LIXConnectingMap.lean` (cs-stages-s stopped). GREEN: `LIXBlockProjections` 2966 (with `HprojY`, `Hproj_eq_pullMat`, `blockUnitary` = `w_i`, `Eproj_ne_zero`), `LIXCornerAlgebra` + `LIXConnectingMapPoints` 2975. `connect`/`connect_injective` authored (404 lines, no sorry), being committed and probed; then the fullness theorem (exact `∑ x_l a y_l = 1`) |
| cup_comm GREEN (21:10 EDT) | `CharClass/SteenrodCupOne.lean`, 2062 jobs, all degrees, shape `cup a b = cohCast (Nat.add_comm q p) (cup b a)`; `SteenrodDiagonal.lean` green (`steenrodDiag`, naturality, boundary identity) for cc-cartan; seven Steenrod modules green. Remaining in that lane: the `Sq^k` layer (needs "a cocycle with zero class is a coboundary") in cc-wu's `SqData` shapes |
| cs-simplicity (21:10 EDT) | positivity-free entry point `CStarTower.isSimpleCStar_limit_of_ne_zero` added beside the original (2988 jobs, e28b1333b); no order instances needed on the stages for that route |
| cc-cartan (21:15 EDT) | eleven modules GREEN at 1701 jobs: `CartanDiagonalW` (the resolution's diagonal identity mod 2 — `W ⊗ W` is deliberately NOT built; both composites are defined on the free basis over the group ring with `Δ_W` entering as the index sum with coefficient `T^i`), fourfold tensor acyclicity over a field. Remaining: the Λ-action (block swap) on the fourfold tensor — Mathlib at the pin has NO braiding for `HomologicalComplex` monoidal, so build it by hand via `mapBifunctorDesc` + `mapBifunctor.hom_ext` or a Finsupp model where the swap is an index permutation — the Finsupp source functor with the `ULift` reindexing, the two composites; then instantiate with `steenrodDiag` (green) |
| `connect` LANDED (21:15 EDT) | `Analysis/LIXConnectingMap.lean:391` `connect` with exactly the type `CStarTower.ofInjective` takes, `connect_injective` at :399, `instNontrivialStageAlgebra` at `LIXStageAlgebra.lean:247`; the C*-side is ONE theorem from done — cs-stages' fullness — after which cs-limit names the algebra and cs-endpoint adds the two closed theorems |
| Künneth (20:35) | general two-factor Künneth needs Eilenberg–Zilber (absent) and is OUT; the program needs only one-factor forms chained over `N = S¹ × S⁵ × ∏CP`: cc-cohom-api owns `H^k(S^n × Y) ≅ H^k(Y) ⊕ H^{k−n}(Y)` in ISOMORPHISM form, natural in `Y`, with the explicit maps (`pr_Y^*`, `(pr^*σ_n) ⌣ pr_Y^*(−)`) — required by `ParityData`'s `ι`, `t`, `x`, `tx_inj`; cc-projective owns the `CP` factor (`H^*(Y × CP^d) ≅ H^*(Y)[h]/(h^{d+1})`, from Leray–Hirsch for the trivial projective bundle); the vanishing forms are corollaries. cc-cohom-api: eight modules green (8767–8769) incl. `CohomologyProductCover`, `CohomologyShapes` (cc-projective's `HasPointCohomology`/`HasSphereCohomology`) |
| punctured-product recursion (20:45) | cc-thom's `CohomologyToolkit` now takes per-factor `KunnethFactor` instances (spheres from cc-cohom-api, one `CP` from cc-projective); the recursion splits the `Fin`-indexed `baseY` at its LAST factor (`Fin.snoc`), so the model `M = S⁵ × (∀ j : Fin i, CP _)` is unchanged and the second slot is always a sphere or one `CP`. cc-thom thirteen modules green at 8782; next: δ-linearity `mvDelta_cup` (blocks Leray–Hirsch), then MV naturality, then the toolkit instantiation |
| cc-lix-odd (20:50) | eleven modules green (4ea51e08c, 8663–8667): mapping torus, section path, `tautColSection` fix, `LIXSectionManuscript` (Step C's single zero, an iff), `LIXSectionChart` (chart on `ℂ × ℂ × ℝ × ℝ`, derivative as a `ContinuousLinearEquiv`), `LemmaTwoParity` (rank arithmetic + `ParityData` skeleton), `LemmaTwoStatement` (Lemma 2 with Steps A, C, D as named hypotheses); remaining: one `HasStrictFDerivAt`, the `matEval` bridge to `MurrayVonNeumannEquiv`, `LemmaTwoUnitary` probe, `ParityData` instantiation |
| cc-cohom-api (20:50) | eleven modules green (8767–8773); remaining: Künneth with a sphere factor in ISOMORPHISM form |
| 20:35 batch | `connect` GREEN (cs-stages, 451a97231, 2977 jobs, all five stage modules); the hemisphere frames of `F`, the seam generator `u` and their continuity GREEN (cs-clutching, 69ebc1fdd, 2385 jobs) — the old "Bott, not elementary" claim is refuted in Lean; cc-projective: `CP^d` homogeneous (8659), the three cohomology inputs to the `CP` induction (8782), the projection of a projective bundle is injective on cohomology (8783); cc-steenrod: `SteenrodSquare.lean` authored, probe in flight. C*-side now waits only on the fullness theorem (cs-stages) and the stage-level witness (cs-clutching: `hdiag`, shape lemma, generalized Corollary 4 — the last needs Lemma 2) |
| cc-bundle (20:55) | eight modules GREEN at 2974 (Sonnet); lane back with Opus for the zero section + retraction `P(p⊕1)∖Z ≃ P(p)` and the classifying map / rotation homotopy |
| δ-linearity (20:45) | REASSIGNED to cc-cohom-api (owns `mvCoSC`/`mvDelta`/the splitting; route `ShortComplex.ShortExact.δ_eq` + mod-2 Leibniz + transport through `subCxDualIso`); it is the second half of `tx_inj` in the Künneth isomorphism AND the δ-rung of Leray–Hirsch's ladder. cc-thom takes MV naturality in a map of covered spaces (chain-level map between subordinate-chain complexes) and the toolkit instantiation (sphere base case done at 8786; `KunnethFactor (CP d) (2d)` awaited from cc-projective) |
| CONCRETE ALGEBRA GREEN (20:45) | cs-limit: `LIXLimitAlgebra` (3013) and `LIXLimitSimple` (3017) — `GroupApproximation.LIX.lixTower`, `LIXLimit : Type` (abbrev; `CStarAlgebra`, `Nontrivial` by `inferInstance`), `lixIota`, `lixLimit_hasK1InjWitness`, `lixLimit_isSimpleCStar`, six instance-ladder `example`s. Trap: `Subtype.partialOrder` from the pointwise order beats the spectral order — fixed by a priority. NEEDS: `∀ k (a : StageAlgebra k), a ≠ 0 → ∃ j, k ≤ j ∧ IsFull (lixTower.climb j k a)` (cs-stages) and the generator's stage-level facts (cs-clutching) |
| cc-steenrod COMPLETE (20:45) | `SteenrodSquare` green at 2131: `Sq k : Hmod2 X n → Hmod2 X (k + n)` with `Sq_mk`, `Sq_add`, `Sq_self`, `Sq_zero`, `Sq_eq_zero_of_lt`. New assignment: the total-degree `SqH` on `⨁ Hmod2 X n` in cc-wu's `SqData`/`ParityData` shape, plus `Sq(y) = y + y²` for line classes (`CharClass/SteenrodTotal*`) |
| ENDPOINT PLUGGED IN (20:45) | cs-endpoint: the assembly against the concrete `LIXLimit` is green at 3019 jobs (4141b5f9f); the two closed theorems `exists_simple_unital_not_k1Inj` / `not_problemLIX` now need exactly `hfull` (cs-stages' fullness theorem) and the generator's stage-level facts `hstage`/`hdiag` (cs-clutching; `hstage` needs Lemma 2 from the topology side) |
| Chern classes over the graded ring (20:45) | cc-projective: `ChernTotalRing` (2464; `TotalH.of/component/of_eq_zero_iff/of_mul/map`) and `ChernClasses` (2466; `PowerBasis (TotalH X) (TotalH P)`, `γ` as `minpolyGen` coefficients); the `DirectSum` semiring diamond is gone. DO NOT WIRE the superseded `ChernEvenPiece`, `ChernEvenRing`, `ChernEvenRingComm` (green but unused). Two inputs stand between the lane and Leray–Hirsch: `mvDelta_cup` (cc-cohom-api) and `mvResWU_one` (cc-thom). cc-relative's `RelativeDual` green at 8730 |
| cs-clutching (20:50) | three modules green together at 8658: rank-one toolkit, Householder reflection, phased transport, two-step frame `frameRot` (domain = sphere minus one point), both hemisphere frames, `seamGen` with `seamGen_mul_rk1` (it IS `diag(u,1)`), the explicit null-homotopy `seamPath` (`seamPath_zero = seamGen`, `seamPath_one = 1`, unitary, jointly continuous) — `StableNullHomotopy` RETIRED; `clutchingObstruction_of_equiv` repaired. Remaining: `HasGeneratorShape` + obligations, `hdiag`, generalized Corollary 4, `hstage` (modulo Lemma 2's Steps C/D) |
| cc-thom phase 1 | GREEN, nine modules, 2911 jobs (19:00 EDT); Step C assembled over a `CohomologyToolkit` awaiting MV/Künneth/relative/LH instantiation |
| root: K₁ layer + endpoint statement wired | 18:50 EDT, commit fa15b619f (ten modules, cs-endpoint green at 2996 jobs); `LIXEndpointStatement` built in the root build |
| root build 2 (20:00 EDT) | every wired LIX module BUILT in the root (`LIXSimplicity`, `LIXLimitCompletion`, `LIXLimitSeparable`, `LIXSimplicityInstance`, `LIXLimitMatrixTransport`, `LIXLimitWitness` with `Built` lines); the GGT breakage is WIDER: `fadb6fd6d` edited `HullSCRelativeGreendlingerStatement`, 89 rooted modules are downstream, and each root build surfaces only the next few reds (`…RelativeBoundary`, `…KernelGeodesicCut`, `…PrefixCutRatio`, `HullSCLemma49FromRelativeGreendlinger` in build 2); `ggt-repair-s` now owns every failing rooted consumer and iterates on the 89-module list in its clone |
| 21:32 EDT (REAL time; the rows labelled 21:45–23:15 above were written ~1h40m AHEAD of the wall clock — subtract accordingly; from here on times come from `date`) | **Root build 5 RED, not on main**: it failed only in `Analysis/LIXLemmaSixGenerator.lean` (unused `w` at 233/234, three `failed to synthesize instance`, two `No goals`) — the shared working tree was rsynced at launch (21:23) while cs-clutching's file was mid-edit; the committed 85f09ba37 (21:26:55) has `fun _` there and the `open scoped CStarAlgebra`/`ComplexOrder` fix that cures exactly those instance failures, and probed green at 2981. Everything else in the root closure built (the 12-module Lemma 2 slice and the 8698-job endpoint included). HAZARD recorded: `scripts/remote-build.sh` builds the WORKING TREE, so an in-flight edit of a rooted module by any lane reds the root build for everyone; root build 6 goes from a clean export of `origin/main` |
| 23:08–23:15 | cc-wu **`SqDataInstance` green** (570b0cd44, 8786): `hwu` and the per-space Cartan are OFF the checklist; even-side endpoint `Wu.gamma_top_eq_zero_of_splitting` takes FOUR hypotheses — `CartanTotal` (= cc-steenrod's `Steenrod.CartanOf` quantified over the space; cc-cartan), `htx_inj`/`hγ`/`hsq_b` (cc-cohom-api), `SplittingData N F r γ` (`proj`, degree-2 `root`, `pull_injective` on `TotalH`, `sq_one_root`, `chern_split : π^*γ_k = e_k(roots)`; cc-projective) + slice data; `totalH_map_injective` bridges degreewise LH injectivity to the ring form; old name kept stable (rule 11). cc-projective **`LerayHirschColumn` green** (2056): `MVFacts`, `lhDomain`, five componentwise maps; the one `dite` only supplies `n − 2i + 1 = n + 1 − 2i`; files 2 (squares) and 3 (five lemma + cover induction) next. cc-thom **`mvExactZero` green** (`MayerVietorisZero`, 8772; general fact `mono_homologyMap_zero`: a degreewise mono of ℕ-indexed cochain complexes is mono on `H⁰`, via `CochainComplex.isIso_homologyπ₀`) — the element-form MV sequence is COMPLETE (exact at all four spots, four pullback identifications, `mvSequence`, toolkit term); assigned `KunnethFactor (CP d) (2d)` over `MVFacts` by induction on `d`. cc-steenrod **`SteenrodCartanTotal` green** (2136): the Cartan transport bridge; the graded Cartan statement is stated in the TOTAL ring because the graded form does not typecheck; told to do the chain-map condition against cc-cartan's landed differential now |
| 22:58–23:08 | cs-endpoint **two-step endpoint statements green** (01863243b, 8704; eight audit lines classical): `exists_simple_unital_not_k1Inj_of_lemmaTwoInput_data`, `not_problemLIX_of_lemmaTwoInput_data` over `∀ j, CharClass.LemmaTwoInput (lixDD j)` — cc-thom's Step C and cc-wu's Step D are literally the endpoint's hypotheses (asymmetric: C for the section-carrying unitary, D for EVERY corner unitary, so no comparison of two tori). Exactly THREE statements in the whole chain are not yet theorems: Step C, Step D, the witness arrow. cc-bundle item 3 **`BundleStabilize`** green (0fb0c22f1, 2974; `homotopic_cpEmbed_same`: the rotation homotopy after ONE stabilisation along a linear isometric embedding with the SAME embedding on both sides — in `ℂP^d` itself the statement is false; hypotheses = four matrix identities) — lane COMPLETE (13 modules), now review-pair for cc-projective's ladder. cc-relative **(B6) `RelativeLocalModel` green** (8776; `localEquiv`, `localGenerator`, `localGenerator_ne_zero`, `eq_smul_localGenerator`, `relCohomologyCongrPoint`, `ne_zero_of_iso`, `relCohomologySetCongr`; total in `r`) — lane COMPLETE, `RelativeDual` retirement deferred to post-endpoint hygiene, now review-pair for cc-cohom-api's δ-linearity. cs-limit `lixLimit_separableSpace` (3024) → cs-endpoint lands the separable stronger theorem |
| 22:48–22:58 | cs-clutching **`LIX.genUnitary : unitary (StageAlgebra 0)` green** (85f09ba37, 2981; `blockUnitary 0 genMat`, corner membership + unitarity fibrewise via `matrix_ext_of_matEval`, no norm estimate) — the `u` of `lixLimit_hasK1InjWitness` at `k = 0`; verified `lixDD j i = stageRank i` and `CharClass.baseY (lixDD j) = STW59.baseY j` DEFINITIONALLY; the only mismatch is the `H` index type (sigma over `Fin ℓ` vs iterated binary sum), reindexed inside Corollary 4. cs-limit: alias deleted, **`lixLimit_separableSpace : SeparableSpace LIXLimit` unconditional by `inferInstance`** (3024), four audit gates classical. cc-lix-odd `LemmaTwoStepD` green (8804): Step D wired to cc-wu's endpoint (must stay a LEAF so the endpoint's `LemmaTwoStatement` closure carries no cohomology until the final closed theorem). cc-thom handed cc-lix-odd `puncturedAcyclic_lixBase` (first hypothesis of Step C, in cc-lix-odd's vocabulary; sphere model transport left explicit) and was assigned `mvExactZero` (left-end MV injectivity, cc-projective's shape) so cc-cohom-api stays on δ-linearity alone |
| 22:42–22:48 | cc-thom **`EulerLocalAssembly` green (8784): Step C is ONE application** — `topChernClass_ne_zero_of_chain` chains excision, the chart iso and the local model, remaining inputs as named hypotheses with owners in the docstring; twenty-one cc-thom modules; owed: `ℂP` Künneth factor (cc-projective), δ-linearity (cc-cohom-api), (B6) (cc-relative; cc-thom answered: rank ≥ 1 only, no generator/equivalence compatibility needed, yes to transport along a homeomorphism of punctured subspaces). cc-lix-odd told to write `stepC_of_chain` against it now. cs-simplicity review: `#audit_axioms` and `#audit_closed_axioms` on `lixLimit_isSimpleCStar` both `[propext, Classical.choice, Quot.sound]` (scratch file outside `GroupApproximation/`, af06502c1); Corollary 4 pre-review → four findings to cs-clutching: only `w ∉ U₀` is in scope (order-two and stable-`K₁` claims out by §0); `LemmaTwoHolds` is the STRONG (continuous-field) end and the implication runs matrix→continuous, so do not invert the binder; `toMatC` carries a continuity proof — `exact` crosses, `rw` does not (use `continuous_FHmat`/`continuous_EHmat`); index convention checks: manuscript one-based `d_j = r_{j−1} = 2^j` = Lean `lixDD j i = 2^(i+1)`. cc-thom trap: in this project an application-site "type error" (`Function expected … ?m`) usually means a NAME NOT IN SCOPE, masked by `autoImplicit` (fourth distinct symptom) |
| 22:35–22:42 | cc-projective **Leray–Hirsch ladder design approved**: `MVFacts X := (delta_cup) (exactZero)`; left column = `⊕_{i<r}` of the base MV sequence shifted by `2i`, indexed by all of `Fin r` with the truncated-subtraction junk cut out by the subgroup `lhDomain X r n := {c | ∀ i, n < 2i → c i = 0}` (no `dite`, no varying index type); `exactZero` IS the single boundary rung (`2i = n+1`, source forced zero, target `H⁰(X)`); three files `LerayHirschColumn` → `LerayHirschSquares` (restriction square = naturality of `pull`/`cup`; δ-square = `delta_cup`) → `LerayHirschInduction` (`bijective_of_ladder`, then the finite trivialising cover with cc-bundle's local triviality as base case); reindexing target for cc-bundle: `cpBlockIncl` into `CP (2d+1)` + apply lemma. cc-wu `SqDataInstance` probing: `hwu` REMOVED from the interface — `SqData` of the flag total space, (Wu-diag) there, pushed down along the injective pullback; replaced by ONE bundled input `SplittingData` (flag projection, degree-2 Chern roots, `π^*` injective, `Sq¹` kills each root = `H³(ℂP)=0` + naturality, Whitney on the flag bundle `π^*γ_k = e_k(roots)`) from cc-projective; `CartanTotal` quantified over the space; `totalH_map_injective`; endpoint `gamma_top_eq_zero_of_splitting` down to FOUR hypotheses (Cartan, two-sphere Künneth injectivity, Künneth decomposition with degrees, splitting). cs-limit: `#audit_closed_axioms` on `lixLimit_isSimpleCStar` = classical three (3021); three independent probes agree on the simplicity chain |
| 22:30 **ENDPOINT = ONE HYPOTHESIS** | cs-endpoint `ProblemLIX` green (2cbbd4666, 8698 jobs; six `#audit_axioms` lines = `[propext, Classical.choice, Quot.sound]`): `ProblemLIX`, `exists_simple_unital_not_k1Inj_of`, `…_of_limit`, `not_problemLIX_of_exists`, `exists_simple_unital_not_k1Inj_of_lemmaTwo_data`, `not_problemLIX_of_lemmaTwo_data` — the whole chain now takes exactly ONE explicit hypothesis, cs-clutching's `LemmaTwoHolds → HasK1InjWitness LIX.LIXLimit`; simplicity discharged (bare `lixLimit_isSimpleCStar`); the `_data` suffix drops when the witness lands, then `exists_simple_unital_not_k1Inj`/`not_problemLIX` with `#audit_closed_axioms` when `LemmaTwoHolds` is proved. Root: `LIXStageAlgebraSeparable` wired (9ab7f5e8b; cs-stages 5195146e5, 2978, second countability of `C(X,Y)` for locally compact second countable `X`); `ProblemLIX` closure = 44 modules all rooted (the 12-module Lemma 2 slice enters through it); corpus 4515 modules, no cycles/dangling, zero LIX duplicates. **Root build 5 launched** (`rootbuild5.log`). cc-relative (B6) `RelativeLocalModel` authored+committed, probing (iso first, generator = class of one; rank-0 case separate) |
| 22:20–22:28 | cc-projective `GysinCover` (3343; `chartOpens_sup_notZeroOpens`, the two opens of `P(p⊕1)` cover: squared lengths of last coordinate and of the rest sum to one) and **`GysinFromLerayHirsch`** (2057): "cup with the Euler class is an iso" derived from Leray–Hirsch for the `ℂP¹`-bundle without building the Gysin LES (pair of restrictions bijective where the sphere bundle is acyclic; in LH coordinates the pair is `(a,b) ↦ (a, a + b ⌣ e)`); `GysinData` named; **degree convention `n + 2`, never `n − 2`** (no truncated subtraction, no transport — 40 lines instead of hundreds); Whitney's algebra already green (`chernPoly_mul_of_map_injective` + `pull_injective`). ORDER: write the Leray–Hirsch ladder NOW over `structure MVFacts X : Prop := (delta_cup) (exactZero)` — it is the longest remaining pole; instantiation is two lines when cc-cohom-api lands. cs-limit: simplicity under BOTH names (`lixLimit_isSimpleCStar`, `…_unconditional`), one proof; flattening inventory for cs-clutching: `CStarMatrix.reindexₐ` is a `StarAlgEquiv`, `finProdFinEquiv`, and `Matrix.compAlgEquiv` lacks `map_star` (supply `map_star'` for `Matrix.comp` = block conjugate-transpose), `unitaryHom_mem_unitaryComponentOne` moves `U₀` along any unital ⋆-hom |
| 22:12–22:20 | cc-thom **`ThomToolkitInstance`: `cohomologyToolkit` is a TERM** (1f83edcff, 8780) — all four toolkit fields discharged, the punctured-product recursion unconditional (`puncturedAcyclic_prod`, `puncturedAcyclic_sphere'`); twenty cc-thom modules green; owed to it: the `ℂP` Künneth factor (cc-projective) and δ-linearity (cc-cohom-api). cs-simplicity verified the unconditional simplicity chain end to end (3020, every module Built, lexical scan clean; no star-stability assumed, no C*-quotient used, stages carry no order; report a53b11109) and is assigned REVIEW: axiom audit of `lixLimit_isSimpleCStar` + Corollary 4 read against the manuscript. cs-endpoint reverted its copy of the simplicity theorem per the ruling; endpoint patch re-probing. cc-relative committed (B6) `H^{2r}(ℂ^r, ℂ^r∖0) = F₂` with a named generator as AUTHORED-UNVERIFIED (6c324a55c), unrooted |
| 22:05–22:12 | **Lemma 2 hypothesis list = TWO items** (cc-lix-odd `lemmaTwoHolds_of : (∀ j, LemmaTwoInput (lixDD j)) → LemmaTwoHolds`): `stepC` (odd side, cc-thom; all of cc-lix-odd's inputs delivered incl. `lixSection_eq_zero_iff` unconditional, bump `χ = sin(πτ)`) and `stepD` (even side; `stepD_of_parity` reduces it to cc-wu's `gamma_top_eq_zero_of_slice_totalH`, now FIVE hypotheses: Cartan (cc-cartan), two-sphere Künneth injectivity + Chern decomposition + instability (cc-cohom-api), Wu relation (cc-projective)). Ruling: no `stepC_of_toolkit` placeholder; cc-lix-odd joins Step E on a piece cc-thom names. cc-steenrod `SteenrodDiagonalLambda` green (2037), Cartan transport to `TotalH` probing (the graded Cartan statement does not typecheck — degrees agree only propositionally — so the hypothesis is stated in the total ring). cs-limit lane: eight modules green (table in report); asked cs-stages for per-stage `SeparableSpace` (approved, low priority) → `SeparableSpace LIXLimit`. cs-clutching: `hdiag` needs the `M₂(M₂)→M₄` flattening (plumbing); shape lemma + Corollary 4 independent |
| 22:00–22:05 **SIMPLICITY UNCONDITIONAL** | cs-limit: `LIX.lixLimit_isSimpleCStar : IsSimpleCStar LIXLimit` with NO hypothesis (faee56161, 3020 jobs; the old form is `lixLimit_isSimpleCStar_of_full`). cc-lix-odd `CharClass/LemmaTwoGlue.lean` (05368b1e3, 8677): the endpoint seam — `LIX.LemmaTwoHolds` from Steps C and D at every stage (`lixZeroPoint`, `lixSection`, `lixSectionData`, `lixChi`). cc-steenrod `SteenrodDiagonalLambda` (9dec41494): `Phi` packaged over the group ring in namespace `Steenrod` (`PairIndex`, `injectPair`, `phiBasis`, `Phi`, `Phi_single_one`, `steenrodDiag_degree_zero`); `dupscan` still 0 in `CharClass`. C*-side status: every input proved outright except the witness arrow `LemmaTwoHolds → HasK1InjWitness LIXLimit` (cs-clutching: `hdiag` plumbing, shape lemma, Corollary 4, `hstage`). Root build 5 waits for cs-endpoint's `ProblemLIX` commit (the working-tree copy is mid-edit; a build now would compile in-flight bytes) |
| 21:55–22:00 | cs-clutching `paddedPath` green (a248de87e, 2981): the null-homotopy of `u ⊕ 1₂` in `U(4)` over `S⁴`, unitary and jointly continuous on `Icc 0 1 × S⁴` — `hdiag`'s mathematics; what remains is plumbing (`M₂(M₂(C(X))) ≅ M₄(C(X))` via `Matrix.compAlgEquiv` or a blockwise path with `finProdFinEquiv`, the free stage-zero corner `HIdx 0 = Empty`, `ContinuousMap.curry`). cs-endpoint: `#audit_axioms` caught a `sorryAx` that was Lean's error recovery after a mis-placed section (fixed; gate worked); endpoint patch now has simplicity unconditional and the witness arrow as the ONLY explicit hypothesis; ruling repeated: cs-limit declares `lixLimit_isSimpleCStar_unconditional` once. cs-stages report COMPLETE (48dc910a0); its fullness is over a tower parameter so the stage side stays upstream of the limit side. cc-bundle whole-lane probe 2978 (7f30bef4c); item 3 parked on cc-projective's target |
| 21:45–21:55 decisions | cc-thom: SKIP the δ-square/naturality file (all restriction squares are `pull` functoriality; a δ-square, if ever needed, comes from cc-cohom-api's `mvDelta_spec`); toolkit instantiation then Step E. cc-bundle **flag bundle** green (3176691e7, 2976; `BundleFlag.lean`: `Flag p r` inside the FIXED ambient `X × (ℕ → Matrix ι ι ℂ)` — lines are coordinates, rank one/orthogonal/continuous by construction; `flag_decomposition : comap (flagProj p r) p = ∑_{l<r} flagLine p r l`; `flagOne`, `flagForget`, `flagComplement`, `rank_flagComplement`), C1–C4 in cc-thom's shapes (`totalComap`/`projComap`); 63 bare-`CharClass` declarations in `BundleRankOne`/`BundleFrame` left alone (zero fully-qualified duplicates). cc-wu: `sqH_t`/`sqH_x`/`t_mul_t` discharged by `sq_pull_sphere_eq_zero` (a pulled-back sphere class has `Sq^k` pulled back from `H^{k+m}(sphere) = 0`), so they need no Cartan; endpoint for cc-lix-odd `Wu.gamma_top_eq_zero_of_slice_totalH`; assigned the `SqData` instance at `TotalH N` so `hwu` becomes one cc-projective input. cc-lix-odd `lemmaTwo_of_stepC_stepD` / `lemmaTwo_matrix_of_stepC_stepD` (8673; the implementer must be ADJOINTED — `wᴴ`, not `w`, satisfies both hypotheses). cs-endpoint `LIXLemmaTwoProp` green (8671; `lixDD_apply`, `even_lixDD`, `lixDD_pos`, `LemmaTwoHolds.at_stage`), endpoint patch probing. cc-projective **Gysin cover covers** (3343). cs-stages COMPLETE (8 modules) |
| 21:13–21:45 greens | cc-wu **`ParityInstance` green** (48d5ab0b8/675162ea6, 8783): `ParityData` assembled at `TotalH Y`/`TotalH N` over SEVEN named hypotheses — the topology side's checklist (cc-wu report §7): `hcartan` (cc-cartan formula + cc-steenrod transport to `SqH` on `TotalH`), `htx_inj` (cc-cohom-api, two sphere factors), `hγ` (cc-cohom-api Künneth split + cc-projective Chern classes), `ha_zero`/`ha_odd` (cc-projective, both free from the slice restriction), `hsq_b` (grading of the `t·x` component; cc-cohom-api), `hwu` (cc-projective splitting principle + Steenrod/Cartan via `SqData.wu_diagonal`). cc-thom `mvResWV_eq_pull` — **all four MV restrictions are honest pullbacks** (943a527ac); cc-lix-odd **Step A is a theorem** (`LemmaTwoStepA`, dc40761dd, 8673) — Lemma 2 needs only Steps C and D; cs-stages `isFull_climb_of_ne_zero` wired (6bace270d); cs-endpoint told to close simplicity with `lixLimit_isSimpleCStar (isFull_climb_of_ne_zero (T := lixTower) (fun _ => rfl))`. cc-relative-s COMPLETE (seven modules, 8735; §5 = the `ModuleCat`/`ChainComplex.of` label-mismatch recipes, §6 = the (B6) local-generator plan) and STOPPED; the Opus cc-relative resumed in edit mode to execute (B6) `localGenerator`/`localEquiv` for Step E |
| ROOT GREEN 4 (21:40) | root build 4: `Build completed successfully (12933 jobs)`, zero failures, with the six newly wired C*-side modules (`LIXClutching`, `LIXGeneratorUnitary`, `LIXObstructionComplementUnitary`, `LIXConnectingMapFullness`, `LIXConnectingMapFullnessSum` — 128 s at the root, as predicted — `LIXLemmaSixGenerator`); main is green. Next root build after cs-endpoint's `LIXLemmaTwoProp` + the endpoint patch and cs-stages' `LIXConnectingMapFullnessTower` land (wire those two plus the 12-module Lemma 2 closure) |
| 21:11–21:30 | cs-endpoint authored `Analysis/LIXLemmaTwoProp.lean` (`lixDD`, **`LIX.LemmaTwoHolds`**, plus "every stage dimension is even" and "positive" for Step D); verified the Lemma 2 statement's closure carries no cohomology/relative/Steenrod/Thom/projective/bundle module (13 project modules, but ~8671 jobs — the Mathlib closure of the mapping-torus/CP layer is ~5.7k jobs beyond the C*-side's); lead checked `wire.py closure LemmaTwoStatement` = 12 unrooted, no dangling, no duplicate against the rooted set; endpoint patch (`…_of_lemmaTwo`) staged, applied after the probe. cc-projective: **second MV requirement** for the Leray–Hirsch ladder besides `mvDelta_cup` — exactness at the LEFT end, injectivity of `H⁰(X) → H⁰(U) ⊕ H⁰(V)` (the shift-`2i` summand of the five-lemma column reaches base degree 0 at `n = 2i`, where the incoming term is absent); sent to cc-cohom-api as an addition; it is the bottom-of-complex fact behind `one_ne_zero_cohZero` (third time the degree-zero end was the awkward one in that lane). cc-bundle's two landings discharge cc-projective's bundle NEEDS except the projective-space-valued reindexing of the rotation homotopy |
| 21:06–21:25 greens + rulings | cc-cartan `CartanDiagonalModule` (W⊗S(X) degreewise module, 3c7ff9349, 1933); cc-wu 28e7d8d1a; cc-projective **mod-2 Euler class of a line bundle** (2c5fdc4bc, 8799; a rank-one projection-valued map IS a map to `CP`, no classifying-space theory; naturality, normalisation on the tautological line, vanishing through `H²`-free spaces; invariance under iso awaits cc-bundle's reindexing + cc-thom's `mvResV_eq_pull`); cc-lix-odd `LIXSectionNesting` (base as left-nested binary products, for cc-thom's one-factor-at-a-time recursion; 6146bb2ca, 8663) — thirteen modules green, Steps A/B/C done; cc-cohom-api `CohomologyDeltaChain` (both `mvCoSC` maps identified on the chain level: `g` = sum of restrictions, `f` = pair of ambient restrictions, V twin + F₂ sign lemmas; 05d2569de, 8776) — δ-linearity 3 of 4 milestones, `mvDelta_spec`/`mvDelta_cup`/`KunnethSecondInjective` remain; cc-thom `MayerVietorisPullAmbient` (`mvResU_eq_pull` via the small-chain end without inverting the quasi-iso; c8509ea5c, 8774) — naturality now only needs the δ-square map; cc-bundle C1–C4 (e05298022). ROOT: six C*-side modules wired (e6d82f181), root build 4 running. RULINGS: (i) Cartan carrier — `tgt` = free F₂-module on simplex pairs with the honest swap (= cc-steenrod's carrier), `src` = free Λ-module on `WSIndex`; cc-cartan builds both functors + `free` + `acyclic`, cc-steenrod writes `Phi`/`phi_zero` into them; (ii) `MayerVietorisPullAmbient` vs `MVDelta.*` overlap — keep both, no trimming before the endpoint; (iii) `ParityData` INSTANCE is cc-wu's (`ParityInstance.lean`); cc-lix-odd owns the glue `stepC_of_toolkit`/`stepD_of_parity` → `lemmaTwo_of` → `LIX.LemmaTwoHolds` over named hypotheses. Idle-lane pattern recurred five times this half hour (lanes stop after each milestone); each woken with an explicit "do not idle" order |
| 21:06–21:20 lane state | cs-stages: all seven modules green (table in its report; `LIXConnectingMapFullnessSum` = 110 s, 4M heartbeats, alone in its file); its `0 ≤ a` note: positivity unused, conclusion exact. cs-clutching `LIXLemmaSixGenerator` green (7c3192c2a, 2981): `equatorEmb` identifies `Metric.sphere (0:ℝ⁵) 1` with the chart equator via `(a₀+ia₁, a₂+ia₃, ia₄)` (third coordinate purely imaginary, never `±1`, which both hemisphere frames need), `genU2` = the 2×2 block `inclᴴ genU incl`, unitary because `genU` fixes the pole; NEEDS ROOT WIRING. cc-bundle: all eleven modules green (5beba00e1), roster row COMPLETE; `finSumFinEquiv` reindexing awaits cc-projective's hyperplane-stability shape; flag bundle assigned. cc-wu (28e7d8d1a, 1553) two conventions for instantiators: (a) **powers of two are NOT needed, `d_j` even suffices** (the `t·x` component of Wu-diag at every `i`, reindexed by the total index, gives "the convolution `(a⋆b)_N` vanishes for every odd `N`", then strong induction on odd `N` from `a₀ = 1`, `a_q = 0` at odd `q`; checked by hand at `d = 6`); (b) **`b` is indexed by the TOTAL index**, `γ_k = ι(a_k) + t x ι(b_k)` with `deg b_k = 2k − 6`, target `b_r`, `r = m+3` odd, so `b 0 = b 1 = b 2 = 0` — differs from the routes doc by 3; cc-wu now on the `ParityInstance` integration. cc-steenrod: `SteenrodTotal` was red only on the `DirectSum` induction case names (`zero`/`of`/`add`, not `H_`-prefixed), re-probing; Φ split being agreed with cc-cartan (three genuine unknowns: carrier = free module on simplex pairs vs Mathlib monoidal tensor; index pairing; target action = plain swap) |
| 21:04–21:05 lane greens | cc-relative `RelativeExcision` green (bfe4dd69c, 8734; `excisedSub`, small-simplex subordination, `relRetract_generator`, `excision_mapsTo`) — all six cc-relative modules green; cc-bundle pairs/pullbacks for cc-thom (5beba00e1, 2974: `comapTotal`, `comapProj`, `totalSet_triv`, `puncturedSet_triv`, `zTrace_lineOf_eq_zero`; C3/C4 withdrawn by cc-thom); cc-lix-odd `LIXSectionLocalHomeo` (`eulerLocalHomeo : OpenPartialHomeomorph ChartSrc (Fin 3 → ℂ)` from `HasStrictFDerivAt.toOpenPartialHomeomorph`, `lixTopDegree = 2∑dⱼ+6`; 8665) and `LemmaTwoUnitary` (`exists_isCornerUnitary_of_stepA`; 8661). cc-thom told Step E is unblocked. cs-endpoint assigned the ONE named Prop `LIX.LemmaTwoHolds := ∀ j, ¬ ContinuousMvNEquiv (FHmat (dd := lixDD j)) EHmat` (new module `Analysis/LIXLemmaTwoProp.lean`) and the endpoint theorems `…_of_lemmaTwo` over it; cc-lix-odd asked whether `stepA` is already a theorem |
| 21:15 **FULLNESS GREEN** | cs-stages `isFull_of_forall_stageEval_ne_zero` (a section vanishing in no fibre is full; matrix-unit averaging on `aᴴa`, trace nowhere zero, invertible in `C(X_j)`, `isFull_of_sum_eq_one` with no ε — positivity unused) and `isFull_connect_of_stageEval_ne_zero` (`b(x_i) ≠ 0 ⇒ IsFull (connect i b)`), 6b4b704d3, 2981 jobs; `LIXConnectingMapFullnessSum` needs 4M heartbeats / 110 s, alone in its file. Remaining assembly `lixTower_hfull` (dense tail `exists_stagePoint_mem_of_isOpen` + `stageEval_connect_ne_zero_of_pull` along `climb` + the one-step fullness) assigned to cs-stages in a new file, together with `lixLimit_isSimpleCStar_unconditional`. Hygiene: cc-projective deleted the superseded even-ring trio (0d5dd9918); `dupscan` = 0 duplicates in `CharClass`; `wire.py check` = 4493 modules, no cycles, no dangling |
| 21:10 fleet state | cc-cohom-api sixteen green (c61b14a73; `CohomologyClassOf` = class of a cocycle for an arbitrary F₂ cochain complex, natural, agrees with `cocycleClass`); δ-linearity steps 1, 1b green, step 2 `mvDelta_spec` specified with every input green — lane had gone IDLE on it, woken: it is the critical path. cc-thom `MayerVietorisPull` 8773, queue confirmed (MV naturality in covered maps → toolkit instantiation → Step E vs excision), owes cc-lix-odd the `openPartialHomeomorphChartPair` signature and cc-bundle the C1–C4 shapes. cc-bundle assigned: C1–C4 lemmas, then the FLAG BUNDLE (tower of projective bundles, pulled-back `p` = orthogonal sum of `r` rank-one projections, for Whitney/splitting and `ParityData.decomposition`), then the `finSumFinEquiv` reindexing on cc-projective's request |
| 20:58–21:05 lane greens | cc-lix-odd `LemmaTwoBridge` (Lemma 2 in both vocabularies, `not_continuousMvNEquiv`/`not_murrayVonNeumannEquiv`, 86c545f50, 8669) and `LIXSectionDeriv` (`hasStrictFDerivAt_trivialBlockChart` = the IFT input, 953db53fb, 8664) — Steps B, C complete on its side; cc-bundle zero section of `P(p⊕1)` + deformation retraction onto `P(p)` (a09311a43) and classifying maps + rotation homotopy (79e6f8271, 2973); cc-projective **`hasCPCohomology_CP (d) : HasCPCohomology (CPtop d) d` UNCONDITIONAL** (b69108dde, 8789) — the `mvResWU_one` hypothesis dissolved by a counting argument in `H^0`; cc-thom landed `MayerVietorisPull` anyway (`mvResWU_eq_pull`, `mvResWU_one`, `mvCxInclU_comp_g`, b696d70a0) — the ownership question is closed. **Critical path now: `mvDelta_cup` (cc-cohom-api)** — LH, Gysin, `ℂP` ring, `ℂP`-factor Künneth and Whitney all sit behind it; cc-projective told to scaffold them over a named δ-linearity hypothesis meanwhile. C*-side: cs-clutching assigned `hdiag`, `HasGeneratorShape`, generalised Corollary 4 over `¬ ContinuousMvNEquiv (FHmat (dd := dd_j)) EHmat`, and `hstage` over that one Prop, so the endpoint will close modulo exactly ONE named Prop. cc-lix-odd told its blocker (`LIXObstructionComplementUnitary`) has been green since 434bd8eae; `LemmaTwoUnitary`/`HasStepAUnitary` next |
| 20:50–20:56 lane greens | cc-projective dropped its duplicate `hasSphereCohomology_sphere` (8784); cc-relative `RelativeSmallChains` (8731); cs-stages fullness first half + matrix-unit averaging (2980); cc-cohom-api exported the cast calculus (`cohCast_congr`/`cohCast_self`/`cup_cohCast_left`/`cup_cohCast_right` in `CohomologyBasic`, 8771) and δ-linearity step 1 `CohomologyDeltaLift` (`ShortExact.δ_apply` specialised to `mvCoSC`, 8769); cs-clutching read the frames over `S⁵` and named the generator (2385). ON DISK, untracked, proof complete: `CharClass/MayerVietorisPull.lean` (`mvCxInclU_comp_g`, `mvResWU_eq_pull`, `mvResWU_one`) — ownership (cc-thom vs cc-projective) being confirmed; cc-cohom-api told to import it for δ-linearity step 2 and to write the `f`-side identification itself. Still-duplicate: the four cast lemmas in the dead `ChernEvenPiece`; cc-projective told to `git rm` the superseded even-ring trio |
| ROOT GREEN (20:50) | root build 3: `Build completed successfully (12927 jobs)`, zero failures — main is green again with the whole wired C*-side layer (K₁, endpoint statement, `CStarSimple`, the limit chain, `ProblemLIX` and through its import `LIXLimitSimple`/`LIXLimitAlgebra`/`LIXConnectingMap`/the stage modules) in the root closure |
| GGT ripple REPAIRED (20:43) | ggt-repair-s: all 89 rooted consumers of `fadb6fd6d` green at 10348 jobs; 22 files fixed forward (membership/length facts via `List.mem_rotate`/`length_rotate`; value-level facts given an explicit `rotation = 0` hypothesis threaded through real callers); `HullSCRelativeGreendlingerStatement` untouched; root build 3 launched to confirm |
| root build state (historical) | RED on four GGT modules (`HullSCLemma44EmbeddedCertificate` → `…RelativeDehn`, `…CertificateInjectivity`, `HullSCLemma49Correction`), broken since 06:47 by the WIP commit `fadb6fd6d` (boundary-cycle rotation); NOT LIX; lane `ggt-repair` (Opus) assigned 18:55 |
| root wiring tool | `scratchpad/cc/wire.py closure <modules>` (lead session): topological import order of the not-yet-rooted closure, cycle and dangling checks; corpus clean at 4370 modules |
| fleet-green modules with no olean | `AlgTop/ManuscriptSectionZeroCount`, `AlgTop/CPTautologicalSection` (now owned by `cc-lix-odd`); `AlgTop/BundleCalculus*`, `AlgTop/ComplexProjective*`, `AlgTop/SingularCohomology`, `CupProduct`, `CupAssoc`, `CrossProduct` (reference only) |
