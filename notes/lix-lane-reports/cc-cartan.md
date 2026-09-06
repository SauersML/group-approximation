# Lane `cc-cartan` — acyclic models and the Cartan formula

Owns `GroupApproximation/CharClass/AcyclicModels*.lean` and
`GroupApproximation/CharClass/Cartan*.lean`, namespace
`GroupApproximation.CharClass`.

## Formulation chosen (decided 2026-09-05, no further arbitration wanted)

**The equivariant theorem is not a separate theorem.**  A chain complex of
`R`-modules carrying an action of a group `Γ` *is* a chain complex of
`R[Γ]`-modules; an equivariant map *is* an `R[Γ]`-linear map; and "acyclic"
means the same thing for both, because kernels and images do not change when
one remembers the extra operators.  So the whole file is written over an
arbitrary commutative ring `Λ`, and the `ℤ/2`-equivariant statement demanded by
the program is the theorem instantiated at `Λ = (ZMod 2)[ℤ/2]` — a commutative
ring, since `ℤ/2` is abelian.  No second induction, no second structure.

**Category and models are arbitrary.**  The theorem is stated for an arbitrary
category `C`, an arbitrary family of models `M : ι → C` and functors
`F G : C ⥤ ChainComplex (ModuleCat.{0} Λ) ℕ`.  This is what makes the *bifunctor*
case free: the Cartan formula needs the comparison over `TopCat × TopCat` with
the *diagonal* models `(Δ^n, Δ^n)` (a singular `n`-simplex of `X × Y` is a pair
of singular `n`-simplices with a common domain, so `S(X × Y)` is free on the
diagonal models), and that is this theorem with `C := TopCat × TopCat`,
`ι := ℕ`, `M n := (Δ^n, Δ^n)`.  Do **not** ask for a separate two-variable
acyclic-models theorem; there is none to prove.

**Freeness is a `Module.Basis`.**  `FreeOnModels M Λ F` carries, for each degree
`k`, an index type `B k`, a model assignment `mdl k : B k → ι`, universal
elements `gen k b ∈ F(M (mdl k b))_k`, and for every object `X` a
`Module.Basis (Σ b : B k, (M (mdl k b) ⟶ X)) Λ ((F.obj X).X k)` whose basis
vector at `(b, φ)` is `F(φ) (gen k b)`.

**Acyclicity is element-level.**  `AcyclicOnModels M Λ G` says: for every model
`i` and every `k`, a cycle of `G(M i)` in degree `k+1` is a boundary.  Stated
this way (rather than as vanishing of a homology object) it is directly
consumable, directly provable from a chain contraction, and identical in the
equivariant and non-equivariant readings.

## 1. GREEN

Reprobed 2026-09-05 (Opus, lane returned): **all eleven owned modules build
clean together, `Build completed successfully (1701 jobs)`**, `LAKE_EXIT=0`,
`PROBE GREEN`; the log's `lake build` line names all eleven targets and
`clone cc-cartan` (see TRAPS on why that check is not optional).  Individual
`Built` lines this session: `AcyclicModelsSplitting` 8.0s (1626 jobs),
`CartanEvaluation` 6.8s (1700 jobs), `CartanDiagonalW` 5.4s (1574 jobs).  The
earlier seven-module figure of 1674 jobs was independently reconfirmed from this
side before the four new modules landed.

New since the seven-module green:

* `GroupApproximation/CharClass/AcyclicModelsSplitting.lean` — **over a field,
  positive-degree acyclicity IS a contraction.**  This closes the gap that
  `AcyclicModelsTensor.lean` left open: nothing in the repository produced a
  homotopy from the identity of a model complex to a map vanishing in positive
  degrees, only the vanishing of homology, and the tensor result needs the
  homotopy.  One choice of complement `U j` of the boundaries in each degree
  suffices, because (i) `d_{j+1}` restricted to `U (j+1)` is injective — its
  kernel lands in `im d_{j+2}`, which meets `U (j+1)` trivially, and this is the
  *only* use of acyclicity — and (ii) that restriction is onto `im d_{j+1}`,
  since the `im d_{j+2}` part of any preimage is killed.  `splitHomotopy` is the
  resulting `Homotopy (𝟙 K) (splitAlpha K)` with `splitAlpha` concentrated in
  degree `0`; `tensorSplitContraction` and `tensorSplit_exists_preimage` are the
  consequence for a tensor product.  Coefficients in the application are
  `ZMod 2`, a field, and the model complexes are the singular chains of a
  standard simplex, whose positive homology vanishes.
* `GroupApproximation/CharClass/CartanDiagonalW.lean` — **the arithmetic core of
  the resolution diagonal.**  `deltaW_chain_identity`: in the tensor square of
  the group ring over `ZMod 2`,
  `(1+T) ⊗ T^{i+1} + 1 ⊗ (T^i + T^{i+1}) = 1 ⊗ T^i + T ⊗ T^{i+1}`, because the
  two copies of `1 ⊗ T^{i+1}` produced on the left cancel in characteristic two.
  This is the one piece of mathematics in "`Δ_W` is a chain map".  The object
  `W ⊗ W` is deliberately **not** constructed: the source of the comparison is
  free over the group ring, so both composites are defined on that basis and
  `Δ_W` enters only as the index sum `∑_{i+j=n}` with coefficient `T^i`;
  building `W ⊗ W` would mean a tensor **over `ZMod 2`** of two complexes of
  `Λ`-modules with the diagonal action, a different operation from Mathlib's
  monoidal product over `Λ`, and none of it would be used.
* `AcyclicModelsSplitting.lean` also carries **the acyclicity half of item (2)**:
  `ker_le_range_of_positiveContraction` turns a contraction back into the
  `ker ≤ range` form so the tensor construction iterates, `tensorCx_ker_le_range`
  is the one-step version, and `fourfoldTensor_ker_le_range` is the conclusion —
  over a field, the fourfold tensor power of a positive-degree acyclic complex is
  positive-degree acyclic.  With `ZMod 2` a field and the singular chains of a
  standard simplex acyclic above degree zero, that is exactly the acyclicity
  hypothesis the internal comparison needs of `S(X)^{⊗4}`.
* `GroupApproximation/CharClass/CartanGroupRing.lean` (written by the Sonnet
  continuation) — `GroupRingZ2 := MonoidAlgebra (ZMod 2) (Multiplicative (ZMod 2))`,
  its generator with `T*T=1` and `(2:Λ)=0`, the bridge `moduleOfInvolution`
  turning an `F₂`-linear involution into a group-ring module structure, and `W`,
  the periodic resolution at the concrete ring.
* `GroupApproximation/CharClass/CartanEvaluation.lean` — **the `1 + T` term
  dies.**  A `Λ`-linear map into a module on which the generator acts trivially
  kills `(1 + T) • x`, because the two summands coincide and `2 = 0`
  (`map_one_add_smul_eq_zero`, `map_eq_of_split`, and their instances at the
  concrete group ring).  `DiagonalComparison.eval_sub_eq` assembles this with
  `NaturalHomotopy.cochain_succ` into the exact shape the final extraction uses:
  for a functional `u` annihilating boundaries and a source element whose
  differential splits as `(1 + T)•y + z`, the two evaluations differ by `v z`
  alone — so the difference of the two cochains is literally `δ` of a cochain on
  the space, with no leftover term.  `trivialCoeff` is the coefficient module
  `ZMod 2` with the generator acting as the identity.

* `GroupApproximation/CharClass/AcyclicModels.lean` — the acyclic-models
  theorem (uniqueness half).  Contents:
  * `homFamily`, `homotopyOfFamily` — repackage a degreewise family
    `s k : P_k ⟶ Q_{k+1}` plus the two homotopy identities as Mathlib's
    `Homotopy e 0` (generic preadditive `V`, reusable).
  * `FreeOnModels`, `AcyclicOnModels` — the two hypotheses.
  * `pickPreimage` — a classical boundary preimage, `0` when none exists.  The
    definition of the universal elements is deliberately separated from the
    proof that the choice succeeds; the invariant is established afterwards,
    inside the same induction that proves the homotopy identity.
  * `modelHom`, `modelElt`, `amHom`, `amObstruction`, `amPrev` — the
    construction.
  * `amHom_naturality` — naturality of the homotopy operator, which holds *by
    construction*, before any homotopy identity is available.
  * `d_comp_obstruction`, `amHom_step`, `amHom_comm` — the induction.
  * `NaturalHomotopy`, `NaturalHomotopy.homotopy`, `acyclicModelsHomotopy`,
    `acyclicModelsHomotopyApp` — the theorem and its packaging into Mathlib's
    `Homotopy` at each object (so `Homotopy.homologyMap_eq` applies).
* `GroupApproximation/CharClass/AcyclicModelsContraction.lean` — the
  `PositiveContraction` package (a chain homotopy of the identity to a map
  vanishing in positive degrees) and its `exists_preimage` consequence, used by
  both the tensor-acyclicity file and directly by any model complex that comes
  with an explicit contraction.
* `GroupApproximation/CharClass/AcyclicModelsExistence.lean` — the
  acyclic-models theorem, **existence half**: `Augmentation`,
  `AcyclicZeroOnModels`, and `acyclicModelsMap`/`acyclicModelsMap_zero`,
  extending a natural degree-0 map compatible with augmentations to a natural
  chain map.  Needed by anyone constructing a comparison map `Φ` rather than
  just comparing two already-given ones.
* `GroupApproximation/CharClass/AcyclicModelsTensor.lean` — **acyclicity of a
  tensor product** in the only form ever needed: if `𝟙 C` and `𝟙 D` are each
  homotopic to a map vanishing in positive degrees, so is `𝟙 (C ⊗ D)` (Mathlib's
  `HomologicalComplex.mapBifunctor` for the tensor bifunctor).
  `tensorCx_exists_preimage` is the resulting `AcyclicOnModels`-shaped
  conclusion for `C ⊗ D`.  This is the generic tool that "acyclicity of the
  tensor square of the singular chains of a simplex" instantiates once someone
  supplies the concrete contraction of `S(Δ^n)` (see NEEDS/TRAPS below — that
  concrete contraction does not exist anywhere in the repo yet).
* `GroupApproximation/CharClass/AcyclicModelsHomology.lean` — the bridge from
  "the homology of a model complex vanishes in positive degree" (the form a
  vanishing-homology theorem naturally supplies) to the element-level
  `AcyclicOnModels` hypothesis, via `HomologicalComplex.exactAt_iff_isZero_homology`
  and `ShortComplex.moduleCat_exact_iff`.  This is the *other* route to
  acyclicity, independent of `AcyclicModelsTensor.lean`'s explicit-contraction
  route — useful when only a homology computation, not an explicit homotopy,
  is in hand.
* `GroupApproximation/CharClass/AcyclicModelsResolution.lean` — **the periodic
  free resolution, mod 2.**  Over `ℤ`, the standard resolution of `ℤ` by the
  group ring `ℤ[ℤ/2]` alternates differentials `(1−T)`/`(1+T)`; mod `2` these
  coincide (`−1 = 1`), so the resolution collapses to `Λ` in every degree with
  the *single* repeated differential `(1+T)·`.  `periodicResolution T hT h2`
  builds this for any commutative ring `Λ` of characteristic `2` (`h2`) with an
  involution `T` (`hT : T*T=1`); `periodicDiff_comp_periodicDiff` is the
  `d∘d=0` check (`(1+T)² = 1+2T+T² = 1+0+1 = 2 = 0`, via `linear_combination hT
  + (1+T)*h2`); `periodicResolutionBasis` records termwise freeness of rank
  one.  Deliberately generic in `Λ`/`T` rather than committing to a specific
  presentation of `(ZMod 2)[ℤ/2]` (`MonoidAlgebra`, `AddMonoidAlgebra`, …) —
  that choice belongs to whoever builds the concrete `Φ` (see NEEDS).  This is
  the "cheap, standalone" piece I flagged as available on request; built it
  proactively since it blocks nobody and is needed regardless of the final
  presentation chosen.
* `GroupApproximation/CharClass/Cartan.lean` — the two peer-agnostic pieces of
  the Cartan formula (see the file's own docstring, reproduced accurately
  above the code): the cochain consequences of a natural homotopy
  (`NaturalHomotopy.cochain_succ/cochain_zero`), the `DiagonalComparison`
  package wrapping the acyclic-models hypotheses plus two natural
  transformations agreeing in degree 0, and — the part that does **not**
  depend on any construction of `Φ` at all — `sq_mul_of_sq_cross` /
  `sq_mul_of_sq_cross'`, which derive the cup-product Cartan formula formally
  from the cross-product one.

## 2. AUTHORED, UNVERIFIED

Nothing.  Every declaration in the seven owned modules is covered by the green
probe above.

## 3. NEEDS

### From `cc-steenrod` — the interface I will consume

Publish a Lean signature of this shape (names may differ; the *content* is what
matters).  Until it exists, `Cartan*.lean` states its theorems against a local
`structure` with exactly these fields.

```lean
-- Λ := the group ring (ZMod 2)[ℤ/2]; W ⊗ S(X) and S(X) ⊗ S(X) as functors
-- TopCat.{0} ⥤ ChainComplex (ModuleCat.{0} Λ) ℕ.
structure SteenrodDiagonal where
  /-- the source functor `X ↦ W ⊗ S(X;ZMod 2)`, with the diagonal ℤ/2-action -/
  src : TopCat.{0} ⥤ ChainComplex (ModuleCat.{0} Λ) ℕ
  /-- the target functor `X ↦ S(X) ⊗ S(X)`, with the swap ℤ/2-action -/
  tgt : TopCat.{0} ⥤ ChainComplex (ModuleCat.{0} Λ) ℕ
  /-- Steenrod's equivariant diagonal, as a natural transformation -/
  Phi : src ⟶ tgt
  /-- `src` is free on the models `Δ^n` over the group ring -/
  free : FreeOnModels stdSimplex Λ src
  /-- `tgt` is acyclic on the models -/
  acyclic : AcyclicOnModels stdSimplex Λ tgt
  /-- degree-0 normalization: `e_0 ⊗ x ↦ x ⊗ x` -/
  phi_zero : ...
```

What `cc-cartan` actually uses from `Φ` is only: *natural*, *`Λ`-linear in each
degree* (this is the equivariance), *a chain map*, and *the degree-0
normalization*.  Nothing about the explicit front/back-face formula.  If
`cc-steenrod` prefers to publish `Sq` only at the cohomology level, then the
minimum I need instead is:

```lean
theorem sq_cup_of_cross :   -- the last mile is mine, this is the input
    ∀ {X Y : TopCat.{0}} (a : H^p X) (b : H^q Y) (k : ℕ),
      Sq k (cross a b) = ∑ i ∈ Finset.range (k+1), cross (Sq i a) (Sq (k - i) b)
```

**Status 2026-09-05 (Sonnet continuation):** `Cartan.lean`'s `sq_mul_of_sq_cross`
already takes exactly `sq_cup_of_cross`'s hypothesis (as `hcart`) and derives the
cup-product formula, so *that* reduction is done and green — nothing further
needed from anyone for it.  I re-confirmed with `cc-steenrod-s` (message sent)
that I want the Finsupp-valued `steenrodDiag` (their report, §"Explicit `Φ`")
exported with its boundary identity, to build the functor-level `Φ` myself.

**SUPERSEDED (2026-09-05, Opus back on the lane).**  The paragraph that used to
stand here said the lane was blocked on an Eilenberg–Zilber comparison for a
product of two different spaces and on a linearized Alexander–Whitney chain map.
It is no longer blocked on either.  The lead's **internal** route compares two
natural equivariant chain maps out of `W ⊗ S(X)` into `S(X)^{⊗4}` on **one**
space, so no product, no Eilenberg–Zilber and no linearized AW enter.  The
finding that the vendored `AlexanderWhitney.lean` stops at the object level
still stands as a fact about the repository; it now blocks nothing.

**The internal route, with the correction the lead has adopted.**  The two maps
are `A = (Φ₀ ⊗ Φ₀) ∘ Φ` and `B = τ₂₃ ∘ (Φ ⊗ Φ) ∘ (Δ_W ⊗ Φ₀)`, where
`Δ_W(e_n) = Σ_{i+j=n} e_i ⊗ T^i e_j` and `τ₂₃` transposes the middle two of the
four tensor factors.  The `ℤ/2`-action on `S(X)^{⊗4}` must be the **block swap
(13)(24)**, not (12)(34), and this is forced twice over:

* `A` intertwines `T` with (13)(24) (the swap of `Φ`'s two outputs becomes the
  swap of the two blocks), while the naked second composite intertwines `T` with
  (12)(34); `τ₂₃` conjugates one to the other.
* the evaluating functional `u = a ⊗ b ⊗ a ⊗ b` is invariant under (13)(24) but
  **not** under (12)(34), and `u` has to be `Λ`-linear to be fed to
  `NaturalHomotopy.cochain_succ`.  Under (12)(34) the evaluation step does not
  typecheck at all.

Both composites send `e₀ ⊗ x` to `x⊗x⊗x⊗x`, so they agree in degree `0` and the
uniqueness half applies.  `Φ₀` and `Δ_W` are individually **not** `Λ`-linear;
only the composites are, so `A` and `B` should be defined by their values on the
`Λ`-basis of the (free) source and extended with `Module.Basis.constr`, never
assembled as tensor products of maps.

**Do not build `W ⊗ S(X)` with Mathlib's monoidal tensor of
`ChainComplex (ModuleCat Λ)`**: that tensors over `Λ`, and the object wanted is
over `ZMod 2` with the diagonal action.  Since `W_i = Λ` and the action on `S(X)`
is trivial, `(W ⊗ S(X))_k` is the free `Λ`-module on
`Σ i : Fin (k+1), Simp_{k-i} X`, a `Finsupp`; that indexing also makes every
degree side-condition disappear, since both terms of the differential land on
indices of the same shape.  The **target** `S(X) ⊗ S(X)` *is* a tensor over
`ZMod 2`, so `AcyclicModelsTensor.tensorCx` at `Λ := ZMod 2` is the right object
for it, and its acyclicity is then three applications of
`tensorPositiveContraction` on top of `AcyclicModelsSplitting.splitHomotopy`.

**Concrete obstacle for whoever instantiates, found by reading the pin.**
`TopCat.toSSet = Presheaf.restrictedULiftYoneda SimplexCategory.toTop`, and
`restrictedULiftYoneda A = uliftYoneda ⋙ …`, so
`singularSimplices X n = (TopCat.toSSet.obj X).obj (op [n])` is
`ULift (SimplexCategory.toTop.obj [n] ⟶ X)`, **not** the hom-set on the nose.
`FreeOnModels.basis` is indexed by `Σ b, (M (mdl k b) ⟶ X)`, so the basis of the
`Finsupp` source has to be reindexed along that `ULift` equivalence
(`Module.Basis.reindex`) in exactly one place — the `basis`/`basis_apply`
fields — and nowhere else.  Do this first; it is the field that fails to
typecheck if the models are set up wrongly.

### For `cc-cohom-api` — graded commutativity comes free, do not wait for me

Mod-2 commutativity of the cup product does **not** need acyclic models.  It is
the `⌣₁` coboundary formula that `cc-steenrod` is proving anyway:

```text
δ(α ⌣₁ β) = δα ⌣₁ β + α ⌣₁ δβ + α ⌣ β + β ⌣ α        (mod 2)
```

For cocycles `α, β` the first two terms vanish, so `α ⌣ β + β ⌣ α = δ(α ⌣₁ β)`
is a coboundary, i.e. `[α][β] = [β][α]` in `H^*(-;ZMod 2)`.  Take this from
`cc-steenrod`'s cup-one Leibniz lemma directly; routing it through the
acyclic-models comparison of `Φ` and `Φ ∘ swap` is strictly more work for the
same conclusion.

## 4. TRAPS

* `Module.Basis`, not `Basis`, at pin `81a5d257`; `Module.Basis.constr` needs a
  `SMulCommClass Λ S _`, which is why `Λ` is a `CommRing` and `S := Λ`.
* `(ComplexShape.down ℕ).Rel i j` unfolds to `j + 1 = i`, so in
  `Homotopy.zero i j hij` the hypothesis `hij : ¬ c.Rel j i` is literally
  `¬ (i + 1 = j)` — the same proposition as the `dite` condition of the
  homotopy family, so `dif_neg hij` closes it with no massaging.
* `dNext`/`prevD` are best evaluated with `dNext_eq` / `prevD_eq`, which take an
  explicit `c.Rel` witness (`rfl` in every case here), rather than with the
  `_nat` variants, which force `ℕ` truncated subtraction into the goal.
* **Mathlib has no braiding for `HomologicalComplex` monoidal at this pin.**
  `Mathlib/Algebra/Homology/Monoidal.lean` provides `MonoidalCategory` but no
  `BraidedCategory`/`SymmetricCategory` instance (there is a braiding for graded
  objects, `CategoryTheory/GradedObject/Braiding.lean`, but it is not transported
  to complexes).  So the block-swap involution `(13)(24)` on `S(X)^{⊗4}` — the
  `ℤ/2`-action the whole comparison is equivariant for — is **not** available off
  the shelf and has to be built by hand.  The pattern that works in this codebase
  is `HomologicalComplex.mapBifunctorDesc` to define a map out of a tensor by its
  values on the summands and `HomologicalComplex.mapBifunctor.hom_ext` to compare
  two such maps summandwise; that is how `AcyclicModelsTensor.lean` was proved.
  The alternative is a `Finsupp` model of the target, where the involution is a
  permutation of the index type.  Mod 2 there is no sign to get wrong either way.
* **Probe logs cross between lanes.**  Concurrent lanes share the ssh control
  socket, and a probe can come back containing another lane's build *verbatim*
  and none of its own — with that lane's `lake build` line, its clone name and
  its verdict.  A stolen log reads `PROBE GREEN` just as easily as
  `PROBE FAILED`.  Always confirm that the `==> lake build …` line names your
  targets and `clone <your-lane>` before believing anything.  Also: piping a
  probe through `tail` buffers everything until the pipeline ends, so a running
  probe looks like an empty output file; redirect to a per-lane file name
  instead.
* `Submodule.linearProjOfIsCompl` is a **deprecated alias** at pin `81a5d257`
  (`Mathlib/LinearAlgebra/Projection.lean:792`), and deprecations are hard
  errors under `-DwarningAsError=true`.  The live names are
  `Submodule.projectionOnto` (into the subtype), `Submodule.projection` (into
  the ambient module), `Submodule.projection_add_projection_eq_self`,
  `projection_apply_of_mem_left`, `projection_apply_eq_zero_iff`.
  `Submodule.exists_isCompl` lives in `Mathlib/LinearAlgebra/Basis/VectorSpace.lean`
  and needs a `DivisionRing`.
* `rw [add_comm]` in a goal mentioning `K.X (k + 1)` rewrites the **`ℕ`
  addition** `k + 1` first, and fails with "motive is not type correct" because
  the module element's type then depends on the rewritten term.  Close such a
  goal with `(h.symm).trans (add_comm _ _)` instead of a bare `rw`.
* A `def` whose type is a class and which takes **no arguments** must be marked
  `@[reducible]` (`noncomputable abbrev` works); the same definition with an
  explicit argument is accepted unmarked.  This is why `moduleOfInvolution`
  compiles as a plain `def` but `trivialCoeff` does not.
* `((f ≫ g).hom) x = g.hom (f.hom x)` and `((a + b).hom) x = a.hom x + b.hom x`
  are **`rfl`** for `ModuleCat`.  Stating those reassociations as `have … := rfl`
  is far more robust than `rw [ModuleCat.hom_comp, LinearMap.comp_apply]`, which
  picks whichever occurrence `kabstract` finds first and will silently fold the
  wrong side of the equation.
* Acyclicity must be stated for *positive* degrees only: the singular chain
  complex of a contractible space is **not** contractible (its `H_0` is the
  coefficient ring), only its augmentation is.  A "null-homotopy of the
  identity" hypothesis would be false for every model.
* `ModuleCat.{0} Λ` is **the category**; a single fixed object of it (e.g. `Λ`
  acting on itself) is `ModuleCat.of Λ Λ`, and a morphism between two fixed
  objects is typed against the *objects*, not the category — writing
  `f : ModuleCat.{0} Λ ⟶ ModuleCat.{0} Λ` type-checks (both sides are
  `Type`-valued) but means something else entirely (a functor-category
  morphism between the whole category and itself, one universe up) and every
  use of `f` downstream fails with confusing cascaded "application type
  mismatch" errors that do not obviously point back at the declaration.  Wanted
  `f : ModuleCat.of Λ Λ ⟶ ModuleCat.of Λ Λ`.
* `linear_combination` needs `import Mathlib.Tactic.LinearCombination`
  explicitly; without it the error is a bare "unknown tactic" with no hint
  about the missing import.  It is the right tool for any "`ring`-plus-a-few-
  hypotheses" goal (e.g. `(1+T)² = 0` from `T*T=1` and `(2:Λ)=0`: the
  coefficients are `linear_combination hT + (1+T) * h2`, found by matching the
  expansion `(1+T)² = 1+2T+T²` against `1·(T²−1) + (1+T)·(2−0)`) — much more
  robust than a manual `rw`-then-`ring` chain, which silently leaves a residual
  numeral goal (`⊢ 2 = 0`) that plain `ring` cannot close since `ring` never
  consults hypotheses.
