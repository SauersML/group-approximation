# Formalization blueprint: the marked-compression non-MF theorem

Date: 2026-08-12.  Status: ACTIVE COORDINATION DOCUMENT for the Lean
formalization of the non-MF construction recorded in
`EXPLICIT_FINITELY_PRESENTED_NON_MF_GROUP.md`.

Goal theorem (zero premises, kernel-checked):

```text
There is an explicit countable group E with ¬ IsWeakMF E.
```

The endpoint consumes the existing scaffold
`MarkedCompressionNormCertificate.not_isWeakMF` /
`not_isWeakMF_of_normMFInvisible` in `NormMFResidualDetector.lean`, or proves
`¬ IsWeakMF E` directly from a sequential `WeakMFApproximation E`.  The
finitely presented strengthening is deliberately deferred; it must not delay
the countable theorem.

## 0. Non-negotiables

* No `sorry`, no new axioms, no literature-transcription premises.  The only
  property `(T)` input is the in-repo theorem
  `ExplicitNonMFBase.base_hasKazhdanPropertyT`.
* All builds on MSI (sioux, warm cache); nothing heavy locally.
* Agents do NOT run `git add/commit/push`; the coordinator commits.
* Remote build lock (shared working dir!): before `scripts/msi-build.sh`,
  acquire `msi 'mkdir /projects/standard/hsiehph/sauer354/nonsofic_existence/.agentlock'`
  (success = you own it); release with `rmdir` immediately after the build
  command returns.  If busy, work on proofs locally and retry later; steal
  only if the lock dir is older than 25 minutes (`find ... -mmin +25`).
  Build specific targets, `taskset -c 0-31`.

## 1. The two mathematical layers

### Layer A (analytic): the kill theorem

File plan: `GroupApproximation/Sofic/MarkedCompressionKill.lean` (final
assembly; coordinator) on top of new supporting files below.

```lean
structure MarkedCompressionData (Γ : Type) (E : Type) [Group Γ] [Group E] where
  iota  : Γ →* E
  alpha : Γ →* Γ
  t c   : E
  a     : Γ
  kazhdan : HasKazhdanPropertyT.{0, 0} Γ
  compress : ∀ γ : Γ, t * iota γ * t⁻¹ = iota (alpha γ)
  comm_c   : ∀ γ : Γ, Commute c (iota γ)
  word_sq      : markedCompressionWord t (iota a) c ^ 2 = 1
  word_central : ∀ g : E, Commute (markedCompressionWord t (iota a) c) g

theorem MarkedCompressionData.not_isWeakMF [Countable E]
    (D : MarkedCompressionData Γ E)
    (hne : markedCompressionWord D.t (D.iota D.a) D.c ≠ 1) :
    ¬ IsWeakMF E
```

Note what is *absent*: injectivity of `iota`, properness of `alpha`,
`a ∉ range alpha`.  Those are only used in Layer B to prove `hne`.

Proof chain (all finite-stage, sequential; `w := markedCompressionWord ...`,
`z := w`):

1. From `IsWeakMF E` and `Countable E` get `A : WeakMFApproximation E`
   (`exists_weakMFApproximation`).  Write `Uₙ g` for the models.
2. **Involution rounding.**  `z ^ 2 = 1` plus almost-multiplicativity gives
   `‖Uₙ(z)² − 1‖ → 0`; with `Hₙ := (Uₙ z + (Uₙ z)ᴴ)/2` and
   `Zₙ := 2 · spectralAbove Hₙ 0 − 1` obtain an exact Hermitian symmetry with
   `‖Uₙ z − Zₙ‖ → 0` (uses `|λ − sgn λ| ≤ |λ² − 1|` on eigenvalues).
3. **Nonzero negative corner.**  If the `Zₙ = −1` eigenspace were zero along a
   tail, `Uₙ z → 1`, contradicting `separatedEventually z 1` (`hne`!).  This
   is the only use of separation.  Reindex so the corner is always nonzero.
4. **Corner leakage without spectral gaps.**  For every g, centrality of z
   gives `‖[Uₙ g, Uₙ z]‖ → 0`, hence `‖[Uₙ g, Zₙ]‖ → 0`, and the *identity*
   `(1+Z)/2 · M · (1−Z)/2 = ¼([Z,M] + [M,Z]Z)` gives corner leakage
   `‖(1−P₋)(Uₙ g)P₋‖ ≤ ‖[Zₙ, Uₙ g]‖`.  No Sylvester equation, no gap.
5. **Corner model.**  Diagonalize `Zₙ` (Hermitian), take the negative
   eigenvector coordinates as a new `FiniteModel` (pattern:
   `MovingIndex`/`principalBlock` in `KazhdanCornerModel`), compress, and
   polar-correct (`polarCorrect` in `KazhdanCornerPolar`).  Output:
   `B : OpAlmostRepresentation E` with `‖B.map n z + 1‖ → 0`.
6. **Adjoint representation.**  `adjointMatrix U` on the index type `Y × Y`
   with `(AdU)_{(i,j),(k,l)} = U i k * conj (U j l)`; it is exactly
   multiplicative and unitary, with the perturbation bound
   `‖Ad U − Ad V‖ ≤ 2‖U − V‖` for unitaries.  So `Ad ∘ B.map` is an
   `OpAlmostRepresentation E` on models `(B.model n) × (B.model n)`.  Under
   vectorization, `(Ad U).mulVec (vec M) = vec (U * M * Uᴴ)` and the
   Euclidean norm of `vec M` is the Frobenius norm of `M`.
7. **Kazhdan projection on the adjoint corner.**  Take the symmetric
   generating Kazhdan pair `(S, ε)` of `Γ`
   (`HasKazhdanPropertyT.exists_symmetric_generating_pair`), restrict the
   adjoint almost-representation along `iota` (`OpAlmostRepresentation.comap`),
   form `Pₙ := spectralAbove (hermitianAverage ...) t` with the threshold of
   `topSpectralDisplacement_vanishing_of_generates`.  That theorem
   (generalized to `OpAlmostRepresentation`, workstream W1) yields
   `‖(β̂ₙ γ − 1) Pₙ‖ → 0` for every fixed `γ : Γ`.
8. **Capture lemma** (dimension-free; workstream W2): for `H` Hermitian with
   `‖H‖ ≤ 1 + δ`, `P := spectralAbove H t`, and any `C` with `‖C‖ ≤ 1`:
   `(1−t) · ‖(1−P)C‖² ≤ ‖C − H*C‖ + δ` (spectral-calculus proof; `P`
   commutes with `H` so the cross term vanishes).  Applied to
   `C := βₙ(t)⁻¹ Pₙ` and to the vector `ξₙ := vec (Vₙ c)/√rₙ` it converts
   approximate S-fixedness into `Pₙ`-capture.
9. **Compression order.**  With `Qₙ := βₙ(t) Pₙ βₙ(t)ᴴ` (exact unitary
   conjugation, `βₙ(t) := adjointMatrix (Vₙ t)`): the relation
   `t (iota γ) t⁻¹ = iota (alpha γ)` plus step 7 (applied at the elements
   `alpha s`, `s ∈ S`) plus step 8 give `‖(1 − Qₙ) Pₙ‖ → 0`.
10. **Equal-rank flip (the finite-stage stable finiteness; W2).**  `Pₙ` and
    `Qₙ` are orthogonal projections of *equal rank* (exact unitary
    conjugation).  Lemma: orthogonal projection matrices `p, q` with
    `rank p = rank q` and `‖(1−q)p‖ ≤ ε < 1` satisfy
    `‖(1−p)q‖ ≤ ε / √(1−ε²)` (the map `x ↦ q.mulVec x` is injective from
    `range p` to `range q`, hence surjective by dimension count; pull unit
    vectors of `range q` back).  This replaces abstract stable finiteness and
    is REQUIRED in operator norm — the normalized-trace argument is not
    strong enough for step 11.
11. **The vector chain.**  `ξₙ := vec (Vₙ c)/√rₙ` is a unit vector,
    approximately `Γ`-fixed (comm_c + almost-multiplicativity, op→HS via
    `hsDistSq_le_sq_l2_opNorm`).  `D̂ₙ := βₙ(t) ξₙ` satisfies
    `‖(1−Qₙ)D̂ₙ‖ = ‖(1−Pₙ)ξₙ‖ → 0` (step 8), hence with step 10,
    `‖(1−Pₙ)D̂ₙ‖ → 0`, hence with step 7 at `γ = a`:
    `‖βₙ(a)D̂ₙ − D̂ₙ‖ → 0`, i.e. the normalized-Frobenius distance
    `‖Vₙa · Dₙ · (Vₙa)ᴴ − Dₙ‖₂ → 0` where `Dₙ := Vₙt · Vₙc · (Vₙt)ᴴ`.
12. **Contradiction.**  `‖[D,E'] − 1‖₂ ≤ 2‖D − E'‖₂` for unitaries makes the
    matrix word for `w` tend to `1` in normalized HS; but the word tracks
    `B.map n w = B.map n z → −1` in operator norm (finitely many
    almost-multiplicativity steps), so its normalized HS distance from 1
    tends to `‖1−(−1)‖₂ = 2`.  Contradiction; hence no `WeakMFApproximation`
    exists, i.e. `¬ IsWeakMF E`.

### Layer B (algebraic): the witness group

Base data (already in-repo, `ExplicitNonMFBase`):
`Γ := ExplicitNonMFBase.Base`, `α := compression` (injective,
`omitted ∉ range α`), `base_hasKazhdanPropertyT`.

Construction (avoid HNN normal forms and order-cocycle actions entirely):

* **Mapping telescope** `L := colim (Γ →α Γ →α ⋯)`: quotient of `ℕ × Γ` by
  `(n, γ) ≈ (m, δ) ↔ α^m γ = α^n δ` (check: this symmetric form is the right
  one for injective α; verify transitivity via injectivity).  Group law by
  lifting to a common level.  Facts needed: `ιₙ : Γ →* L` injective;
  the shift `σ ∈ MulAut L` with `σ (ιₙ x) = ιₙ (α x)` and
  `σ⁻¹ (ιₙ x) = ι_{n+1} x`; and `ι₁ x ∈ range ι₀ ↔ x ∈ range α`.
  (First check whether Mathlib's `Mathlib/Algebra/Colimit/DirectLimit.lean`
  or nearby files already provide group direct limits over ℕ; hand-roll only
  if absent.)
* **G** `:= L ⋊ ℤ` via `zpowersHom (MulAut L) σ` and Mathlib
  `SemidirectProduct`; `t_G := ⟨1, 1⟩`.  Then
  `t_G (inl (ι₀ γ)) t_G⁻¹ = inl (ι₀ (α γ))`, and
  `t_G⁻¹ (inl (ι₀ omitted)) t_G = inl (ι₁ omitted) ∉ inl ∘ ι₀ '' Γ`.
* **Coset space** `X := G ⧸ Γ'` where `Γ' := (inl.comp ι₀).range`, with the
  left-translation `MulAction` and `G →* Equiv.Perm X` via
  `MulAction.toPermHom`.  Key facts: `γ • root = root` for `γ ∈ Γ'`
  (root `:= ⟦1⟧`), and `t_G • root ≠ (inl (ι₀ omitted) * t_G) • root`
  (unfolds to the telescope range fact above).
* **Clifford lamp** `C(X) := PresentedGroup` on generators `Unit ⊕ X`
  (`z := of (inl ())`, `c x := of (inr x)`) with relators
  `z²`, `(c x)²`, `⁅z, c x⁆`, and `c x * c y * (c x)⁻¹ * (c y)⁻¹ * z⁻¹`
  for `x ≠ y`.  Consequences inside the presented group:
  `⁅c x, c y⁆ = z` for `x ≠ y`, `z` central (relators + generation).
* **z ≠ 1** via a homomorphism OUT (injectivity never needed): target
  `M := ZMod 2 × (X →₀ ZMod 2)` with multiplication
  `(ε,f)(δ,g) = (ε + δ + q f g, f + g)` where, for a fixed `LinearOrder X`
  (pull back from an injection `X ↪ ℕ`, `Countable X`),
  `q f g := Σ_{y < x} f x * g y`.  Associativity = bilinearity of `q`;
  inverse `(ε,f)⁻¹ = (ε + q f f, f)`.  All relators map to 1; `z ↦ (1,0) ≠ 1`.
* **Action on the lamp**: any `e : Equiv.Perm X` induces `MulAut (C(X))`
  fixing `z` and sending `c x ↦ c (e x)` (relator set is permutation
  invariant; use `PresentedGroup.toGroup` + hom extensionality on
  generators).  Compose: `φ : G →* MulAut (C(X))`.
* **E** `:= C(X) ⋊[φ] G`.  Set `t := inr t_G`, `c := inl (c root)`,
  `iota := inr.comp (inl.comp ι₀) : Γ →* E`, `a := omitted`.
* Verify the `MarkedCompressionData` fields by `SemidirectProduct` simp
  calculus, and `hne`: `markedCompressionWord t (iota a) c = inl z ≠ 1`.
* `Countable E`: quotients/products of countable types.

## 2. Workstreams (parallel)

STATUS 2026-08-12 late evening — lane map as agreed with the peer session:

* W1 DONE (commit 094b7f32): corner machinery generalized to
  `OpAlmostRepresentation`; the sole separation user
  (`eventually_nonempty_weakMFMovingIndex`) stays on `WeakMFApproximation`.
* Steps 2–5 (`ApproxInvolutionCorner.lean`) are owned by the PEER session,
  deliverable: from `A : WeakMFApproximation E` and central involution
  `z ≠ 1`, an `OpAlmostRepresentation E` on nonzero negative-corner models
  with `∀ ε > 0, ∃ N, ∀ n ≥ N, ‖map n z + 1‖ ≤ ε`.  The +365-line
  uncommitted rounding layer in that file is being handed over, not
  discarded.
* The Clifford lamp may land as either the presented group + ZMod 2 order
  model (w3) or the peer fork's realization inside Mathlib's
  `CliffordAlgebra` over `X →₀ ℝ` (`Monsters/CliffordLampGroup.lean`);
  first working `z ≠ 1` wins.  Either way the consumed interface is
  group-level: `lamp : X → C`, `z : C`, `z ≠ 1`, lamp involutions, `z`
  central, `⁅lamp x, lamp y⁆ = z` for `x ≠ y`, and
  `permHom : Equiv.Perm X →* MulAut C` moving lamps along the permutation
  and fixing `z`.
* W4a fork builds steps 7–10 (`KazhdanCompressorCorner.lean`) and 11–12
  (kill theorem) now, with clearly tagged `sorry` stubs for in-flight
  W2/peer APIs; the endpoint ships sorry-free.
* Remote builds (any `lake` invocation) serialize through the
  `.agentlock` mkdir-lock; commits stage by explicit path only.

### To the unidentified third writer working in this tree

You are real, active, and reading this file (your commits track its names).
Neither the coordinator session nor the peer session can address you.
Directives in force, from the human user: NO git branches (main only; `min`
was deleted); serialize every remote `lake` invocation through the
`.agentlock` mkdir-lock (two concurrent lake processes were observed at
20:15 — that corrupts oleans for everyone); stage commits by explicit path
only.  Lane facts: the peer session owns steps 2–5
(`ApproxInvolutionCorner.lean`, `NegativeCornerModel.lean` — your
`NegativeInvolutionCornerModel.lean` duplicates the latter: first green
wins, loser is deleted); w4 owns `KazhdanCompressorCorner.lean` and the
sequential kill; the endpoint is the DIRECT sequential `¬ IsWeakMF` — your
sorry'd `word_normMFInvisible` chain in `MarkedCompressionKill.lean` must
not ship and must not be filled via `hsNormSq_unitary_projection_balance`
(trace balance cannot reach the single-vector step; use the equal-rank
flip).  Your functorial-residual patch is good and is being committed.
Please identify yourself: append a note to this section or commit a file
`docs/THIRD_WRITER.md` stating your session and lanes.

* **W1 (refactor)**: generalize `OpNormVanishing`, `KazhdanCornerMatrices`,
  `KazhdanCornerCompression` from `WeakMFApproximation` to
  `OpAlmostRepresentation` (the four fields used are identical; the one use
  of `separatedEventually` is in `KazhdanCornerModel` ~line 1026 and stays on
  `WeakMFApproximation`).  Downstream call sites take
  `A.toOpAlmostRepresentation` (an `abbrev`, definitionally transparent).
  Whole-repo build + audit must stay green.
* **W2 (new matrix analysis, fresh files, no W1 dependency)**:
  `Sofic/AdjointMatrix.lean` (step 6 API), `Sofic/ProjectionRankFlip.lean`
  (step 10), `Sofic/InvolutionRounding.lean` (steps 2 and 4, dimension-free
  parts) and the capture lemma (step 8, dimension-free form).
* **W3 (algebra, fresh files)**: `Algebra/MappingTelescope.lean`,
  `Sofic/CliffordLampGroup.lean` (presented group + order model + z ≠ 1 +
  permutation action), `Sofic/MarkedCompressionGroup.lean` (G, X, E,
  `MarkedCompressionData` instance sans the analytic theorem, `hne`,
  countability).
* **W4 (integration; coordinator, after W1+W2)**:
  `Sofic/ApproxInvolutionCorner.lean` (steps 2–5 assembled),
  `Sofic/KazhdanCompressorCorner.lean` (steps 7–10 assembled),
  `Sofic/MarkedCompressionKill.lean` (steps 11–12, Layer A theorem),
  `Endpoint` wiring, audit, signatures, docs, manuscript.

## 3. Style and audit constraints

* Repo conventions: explicit `(h : 0 < Fintype.card Y)` instead of
  `[Nonempty Y]`-derived cardinality; no plain `:= rfl` theorems unless
  `@[simp]`; no Prop-valued `def`s never established (LAUNDERED_PROP); margin
  of the audit: run `lake env lean scripts/Audit.lean` remotely, capture to a
  file, check exit code AND `grep -vE ": 0$"`.
* Lean 4.32 gotcha: section variables used only in proof bodies need
  `include x in` before the declaration.
* Names must say what they prove; no vacuous strengthenings; thresholds and
  constants explicit.

### Mathlib API gotchas collected during this development

* `Finsupp.domLCongr` under a `≃ₗ[ℝ]` ascription sticks on a `Module`
  metavariable — pin it in a small `def` first.
* Algebra-only imports silently auto-bind `ℝ` as a type variable — add
  `import Mathlib.Data.Real.Basic`.
* `isUnit_of_mul_eq_one` is commutative-only.
* Orthonormal forms on `X →₀ ℝ`: `LinearMap.BilinMap.toQuadraticMap` +
  nested `Finsupp.lhom_ext'`/`LinearMap.ext_ring` +
  `CliffordAlgebra.ι_mul_ι_add_swap_of_isOrtho`.
* `(-1 : CliffordAlgebra Q) ≠ 1` via the `Nontrivial` instance from
  `CliffordAlgebra.Contraction`; no `algebraMap` injectivity needed.  (That
  Mathlib olean was missing from the warm cache once; now built.)
* `MulAut`-of-subgroup ext goals want `congrArg Units.val`, not
  `Subtype.ext`.
* `Subgroup.characteristic_iff_le_comap` can leave a stuck `Characteristic`
  instance mid-`refine`; prove via the raw constructor + `ext` instead.
* `▸` casts on subgroup-equality hypotheses (`hbot ▸ hx`) often fail
  elaboration where `rw [hbot] at hx` succeeds.
