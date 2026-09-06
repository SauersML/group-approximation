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

**Target statement (fixed 20:20 EDT, cs-clutching):** over `↥sphereFive × baseY i`,
```lean
¬ MurrayVonNeumannEquiv
    (Matrix.fromBlocks (pullMat prS5 Fproj) 0 0 (pullMat prY (HprojY i)))
    (Matrix.fromBlocks (1 : Matrix (Fin 2) (Fin 2) C(↥sphereFive × baseY i, ℂ)) 0 0
      (pullMat prY (HprojY i)))
```
(index types `Fin 3 ⊕ HIdx i` and `Fin 2 ⊕ HIdx i`; `HprojY`/`Hproj_eq_pullMat`
are cs-stages' Y-level form of `Hproj`).  Lemma 2 is delivered in THIS shape,
not as a `ClutchingObstruction`: `LIXClutching.clutchingObstruction_of_equiv`
had jointly contradictory hypotheses (being repaired), and Corollary 4 glues
the explicit hemisphere frames directly instead of routing through `clutchMat`,
whose seam-discrepancy condition the frames do not satisfy.

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
9. **Report**: keep `notes/lix-lane-reports/<your-lane>.md` current (what is
   green with job counts, what is authored-unverified, NEEDS from peers, traps
   found).  Your final message to the lead must contain the same four sections.
   Green claims without a job count are not green claims.
10. **Do not oversubscribe acn112**: the probe already pins you to a bounded
    core range.  Never write build output to `/tmp` on the node.  Do not start
    a second probe while one of yours is running.

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
| roster at 20:10 EDT | Opus OWNS: cc-cohom-api (6 modules green 8767–8769; MV + Künneth remaining), cc-cartan (7 modules green 1674; internal Cartan comparison + simplex contraction), cc-steenrod (`cup_comm` first, at 292620dfd + an uncommitted `SteenrodCupOne.lean`), cs-limit (green 3000), cs-simplicity (green 2988), cs-endpoint (green 3002), cs-stages (`LIXCornerAlgebra`, `LIXBlockProjections`). cc-projective (Opus again from 20:25 EDT; all authored modules green 8683). Sonnet OWNS: cc-relative-s, cc-bundle-s, cc-thom-s (toolkit instantiation), cc-lix-odd-s, cs-stages-s (`LIXStageAlgebra`, `LIXConnectingMapPoints`: `connect`), cs-clutching-s, ggt-repair-s. Opus REVIEW-ONLY pairs: cc-relative, cc-bundle. (cs-clutching and cc-lix-odd returned to Opus 20:45.) Done: cc-wu (1553) |
| Mayer–Vietoris split (20:35 EDT) | cc-cohom-api owns the categorical dualized short exact sequence `mvCoSC`, `mvDelta`, three `ShortComplex.Exact` statements (`CharClass/CohomologyMayerVietoris.lean`); cc-thom-s owns the element-form bridge `CharClass/MayerVietorisBiproduct.lean` + `MayerVietorisElement.lean` (restrictions, exactness at three spots, δ-linearity for global classes, vanishing form A1, the `MVSequence` term cc-projective consumes) |
| dualization duplicate (20:40 EDT) | THREE copies of the `Hom(−,F₂)`-exactness argument: `RelativeDual` (cc-relative), the `cohDualFunctor` block of `CohomologyMayerVietoris` (cc-cohom-api), `MayerVietorisDual` (cc-thom-s, 3c331f766); ruling: first green wins, the other two delete their copies and import it |
| cc-lix-odd | Sonnet finished 20:38 EDT: six modules green (8662/8658), Step B and the combinatorial half of Step C done, `LemmaTwoUnitary` authored (blocked on cs-clutching's red complement-unitary file); lane back with Opus |
| cc-cartan (20:50 EDT) | ten modules GREEN at 1700 jobs: acyclic models (both halves), tensor acyclicity, `AcyclicModelsSplitting` (over a field positive-degree acyclicity IS a contraction — the models' input), `CartanEvaluation` (the `(1+T)` term dies; `eval_sub_eq`), `CartanGroupRing`, the periodic resolution. Remaining: the Finsupp source functor free over the group ring (reindex the basis along the `ULift` in `TopCat.toSSet`'s simplices, in exactly the `basis`/`basis_apply` fields), the fourfold tensor with the block-swap action, the two composites; then `steenrodDiag` from cc-steenrod |
| cc-thom phase 1 | GREEN, nine modules, 2911 jobs (19:00 EDT); Step C assembled over a `CohomologyToolkit` awaiting MV/Künneth/relative/LH instantiation |
| root: K₁ layer + endpoint statement wired | 18:50 EDT, commit fa15b619f (ten modules, cs-endpoint green at 2996 jobs); `LIXEndpointStatement` built in the root build |
| root build 2 (20:00 EDT) | every wired LIX module BUILT in the root (`LIXSimplicity`, `LIXLimitCompletion`, `LIXLimitSeparable`, `LIXSimplicityInstance`, `LIXLimitMatrixTransport`, `LIXLimitWitness` with `Built` lines); the GGT breakage is WIDER: `fadb6fd6d` edited `HullSCRelativeGreendlingerStatement`, 89 rooted modules are downstream, and each root build surfaces only the next few reds (`…RelativeBoundary`, `…KernelGeodesicCut`, `…PrefixCutRatio`, `HullSCLemma49FromRelativeGreendlinger` in build 2); `ggt-repair-s` now owns every failing rooted consumer and iterates on the 89-module list in its clone |
| root build state | RED on four GGT modules (`HullSCLemma44EmbeddedCertificate` → `…RelativeDehn`, `…CertificateInjectivity`, `HullSCLemma49Correction`), broken since 06:47 by the WIP commit `fadb6fd6d` (boundary-cycle rotation); NOT LIX; lane `ggt-repair` (Opus) assigned 18:55 |
| root wiring tool | `scratchpad/cc/wire.py closure <modules>` (lead session): topological import order of the not-yet-rooted closure, cycle and dangling checks; corpus clean at 4370 modules |
| fleet-green modules with no olean | `AlgTop/ManuscriptSectionZeroCount`, `AlgTop/CPTautologicalSection` (now owned by `cc-lix-odd`); `AlgTop/BundleCalculus*`, `AlgTop/ComplexProjective*`, `AlgTop/SingularCohomology`, `CupProduct`, `CupAssoc`, `CrossProduct` (reference only) |
