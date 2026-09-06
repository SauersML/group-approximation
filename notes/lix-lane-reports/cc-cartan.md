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

**Session update 2026-09-05 (later).**  Nine further modules landed green and
pushed.  Each was probed on its own; the job counts below are from the probe
that built it.  The lane now owns twenty-six modules.

**The geometric input of the Cartan formula is proved and the target side of the
comparison is complete.**  What that means concretely: the target functor
`X ↦ S(X) ⊗ S(X)` over the group ring exists with `map_id` and `map_comp`, its
differential is `cc-steenrod`'s, that differential squares to zero, and it is
acyclic on the standard simplices.  Those are exactly the hypotheses
`AcyclicOnModels` consumes.

* `CartanTargetSwap.lean` (2082) — the factor swap on the pair index, cast-free
  because the index carries both degrees as data with the sum as a proposition.
  Superseded in name by `cc-steenrod`'s `swapIdx`/`swapEnd`/`tgtModule`, which
  are the same objects and which this lane has adopted; the bridges are `rfl`.
* `CartanTargetEquivariance.lean` (2083) — the pair differential commutes with
  the swap, so it is linear over the group ring.  The two halves of the
  differential exchange places under the swap exactly, with no signs, because we
  are in characteristic two.  `galAlgHom_comm` is the reusable general fact: an
  `F₂`-linear map commuting with two involutions is linear over the mod-2 group
  ring of `ℤ/2`, stated at the level of the algebra map so that it applies before
  any module instance is in scope.
* `CartanTargetFunctorial.lean` (2087) — pushing a pair of simplices forward is
  functorial, commutes with the swap, and commutes with the differential.  All
  of it rests on one naturality statement about faces, which is `rfl` in the bare
  hom-set model: a face is precomposition with a coface, a pushforward is
  postcomposition, and the two commute by associativity.
* `CartanSimplexContractible.lean` (2068) — the models are contractible and a
  contractible space has no mod-2 homology in positive degrees.  **No cone
  operator on singular chains of a convex set had to be built**: the topological
  simplex is a `ULift` of a convex set, Mathlib's homotopy invariance of singular
  homology holds over any coefficient object and so at mod 2, and a point is
  totally disconnected.
* `CartanSimplexExact.lean` (2841) — the degreewise isomorphism between the
  coproduct carrier of the repo's singular complex and the finitely supported
  functions this lane uses, shown to be a chain map because the alternating signs
  collapse in characteristic two.  Conclusion: **over a standard simplex every
  positive-degree cycle for `bdU` is a boundary.**  That is the only geometric
  input in the whole Cartan formula.
* `CartanFreeCx.lean` (2082) — the tensor product of complexes of free
  `F₂`-modules, done once for an abstract complex presented by its degreewise
  index.  Indexed by `cc-steenrod`'s `PairDeg`, so the tensor square of the
  singular complex **is** their `PairIdx`, definitionally, and the fourfold
  object is the tensor of the pair with itself with no reindexing.  Includes
  `tensorD_tensorD`: the two square terms die because each factor is a complex,
  the two mixed terms are equal and cancel because two is zero.
* `CartanFreeCxAug.lean` (2083) — augmented contractions, and the operator
  `s ⊗ 1 + π ⊗ s` they induce on a tensor product.  The degree-zero residue is
  an idempotent rather than a naive augmentation, because the residue of a tensor
  is the product of the two residues.
* `CartanFreeCxTensorAug.lean` (2084) — **the tensor product of two contractible
  complexes is contractible**, hence positive-degree cycles are boundaries.  Two
  cancellations carry it and both are characteristic two.  Because the tensor is
  again a `FreeCx`, the construction iterates, so the fourfold object's
  acyclicity is this theorem applied twice.
* `CartanSingularFreeCx.lean` (2855) — the instantiation.  The singular complex
  is a `FreeCx`; the general tensor differential **is** `cc-steenrod`'s `dTgt`,
  proved through their own `dLeft_eq_bdU` and `dRight_eq_bdU`; hence `dTgt_dTgt`,
  which they no longer owe anyone; and the field-splitting machinery gives an
  augmented contraction of a model, so the pair complex is acyclic on the models.
* `CartanTargetComplex.lean` (2861) — the assembly: `tgtCx`, `tgtMap`, the
  functor `tgt`, and `tgt_acyclicOnModels`.

### Later in the session: the comparison itself

Four further modules, each probed on its own.

* `CartanFreeCxSwap.lean` (2087) — the factor swap on a tensor square, in
  general.  Used twice: on the pair, where it is `cc-steenrod`'s, and on the
  fourfold, where it is the block swap.
* `CartanFreeCxHom.lean` (2088) — chain maps of free `F₂`-complexes and their
  tensor product, with the chain-map property, functoriality, and compatibility
  with the swap.  This is what the two composites are built from.
* `CartanFourfold.lean` (2864) — **the fourfold object**: the tensor square of
  the pair complex, with the block swap acting, as a functor over the group ring,
  plus its acyclicity on the models.  The `(13)(24)` action is now *forced*: the
  block swap of a tensor square, with the pair complex as the factor, is exactly
  that permutation.
* `CartanMidFour.lean` (2089) — the middle-four interchange, and the conjugation
  identity that turns `(12)(34)`-equivariance into `(13)(24)`-equivariance.

`CartanComposeA.lean` (2875) also landed, but see the note on duplication below.

## The second composite: design, settled 2026-09-05

**No tensor square of the resolution is needed.**  `CartanDiagonalW.lean` was
written deliberately without constructing `W ⊗ W`, and that choice survives.  On
a basis element the second composite collapses to a double sum:

```text
B(e_i ⊗ σ) = Σ_{p+q=i} Σ_{σ' ⊗ σ'' ∈ Φ₀(σ)}  Φ(e_p ⊗ σ') ⊗ t^p · Φ(e_q ⊗ σ'')
```

The resolution diagonal `Δ_W(e_n) = Σ_{i+j=n} e_i ⊗ T^i e_j` and the regrouping
of `(W ⊗ W) ⊗ (S ⊗ S)` into `(W ⊗ S) ⊗ (W ⊗ S)`, taken together, amount to
nothing more than a power of the generator acting on the second factor, and `Φ`
is linear over the group ring, so that power comes straight out.

**The outer transposition is not optional, and here is the check.**  The map
above is equivariant for the permutation that swaps inside each block, `(12)(34)`,
because `Φ` is equivariant into the pair with its own factor swap.  The first
composite is equivariant for the block swap `(13)(24)`.  In the symmetric group,
with `σ = (12)(34)` and `τ = (23)`,

```text
τσ = (1 3 4 2) = (13)(24) τ ,
```

so `τ ∘ B` is `(13)(24)`-equivariant.  `CartanMidFour.lean` is that `τ`, and the
conjugation identity is `rfl` on the index.

What remains for `B`: the explicit double sum as a `Λ`-linear natural
transformation, and its chain-map identity.  The identity is the one genuine
computation left in the lane; the telescoping is the standard one and the two
copies of `Φ(e_p ⊗ σ') ⊗ t^{p+1} Φ(e_q ⊗ σ'')` cancel in characteristic two.

## Duplication with `cc-steenrod`, resolved 2026-09-05

We built the first composite independently and within about twenty minutes of
each other, and then each started writing the same two naturality lemmas.  The
resolution, agreed by me and communicated, not arbitrated by the lead:
`cc-steenrod` owns all of the first composite including its packaging as a
natural transformation; this lane's `CartanComposeA.lean` is to be deleted once
theirs is green, so that exactly one definition of the map survives; and this
lane owns the second composite, the acyclic-models comparison and the evaluation.

The reason it matters is not tidiness.  Two definitionally equal definitions of
one map are worse than either alone, because no rewrite crosses between them.


**Main-tree repair, same session.**  `CartanDiagonalModule.lean` had been
carrying an uncommitted change of mine that moves `SingularBoundaryData` from
`ZMod 2` to group-ring coefficients, while the committed
`CartanSourceBoundary.lean` already supplies one at group-ring coefficients.
The two do not typecheck together, so `main` was red on this lane's source chain
for as long as that went uncommitted.  Landed after a joint probe of
`CartanSourceFunctor`, `CartanSourceBoundary` and `CartanDiagonalModule`
together, green at 2082 jobs.

### Earlier in the session

**All seventeen owned modules build clean together:
`Build completed successfully (2113 jobs)`, `LAKE_EXIT=0`, `PROBE GREEN`**, log
verified to name all seventeen targets and `clone cc-cartan` (see TRAPS on why
that check is not optional).

`CartanSourceBoundary.lean` (`Built (10s)`, 2080 jobs) supplies
`singularBoundary : SingularBoundaryData`, so `src` and `srcFree` are **concrete
functors, not ones parameterized by a hypothesis**.  It is also the single place
in the lane where the two presentations of a singular simplex meet:
`singularSimplices` (Mathlib's and `cc-steenrod`'s) is the `ULift` of the bare
hom-set out of the standard simplex, and the source index uses the bare hom-set
because that is what `FreeOnModels` wants.  `bdHom` is the boundary conjugated by
that one `Equiv`, and both `∂∂ = 0` and naturality come across along the
conjugation.

The comparison machinery, complete:

* `AcyclicModels.lean` — the acyclic-models theorem, uniqueness half:
  `FreeOnModels`, `AcyclicOnModels`, `acyclicModelsHomotopy`, `NaturalHomotopy`
  and its packaging into Mathlib's `Homotopy`.  Over an arbitrary commutative
  ring, category and family of models, so the `ℤ/2`-equivariant case is the
  theorem at `Λ =` the group ring and the bifunctor case is the theorem over a
  product category; neither is a separate theorem.
* `AcyclicModelsExistence.lean` — the existence half, with augmentations.
* `AcyclicModelsContraction.lean`, `AcyclicModelsHomology.lean` — the two routes
  into the acyclicity hypothesis, from a contraction and from vanishing
  homology.
* `AcyclicModelsSplitting.lean` — **over a field, positive-degree acyclicity IS
  a contraction** (one complement of the boundaries per degree), and
  `fourfoldTensor_ker_le_range`: the fourfold tensor power of a positive-degree
  acyclic complex is positive-degree acyclic.  That is the acyclicity hypothesis
  for `S(X)^{⊗4}`, since `ZMod 2` is a field.
* `AcyclicModelsTensor.lean` — acyclicity of a tensor product from a
  null-homotopy of each factor's identity.
* `AcyclicModelsResolution.lean`, `CartanGroupRing.lean` — the periodic
  resolution mod 2, the concrete group ring `(ZMod 2)[ℤ/2]`, and
  `moduleOfInvolution`, which turns an `F₂`-linear involution into a group-ring
  module structure.
* `Cartan.lean`, `CartanEvaluation.lean`, `CartanDiagonalW.lean` — the cochain
  consequences of a natural homotopy, the evaluated comparison
  (`DiagonalComparison.eval_sub_eq`), the fact that a `Λ`-linear functional into
  a trivial-action module kills the `(1 + T)` half of the source differential,
  and the arithmetic core of the resolution diagonal.

The concrete objects, new:

* `CartanSingular.lean` — the mod-2 singular chain complex with `Finsupp`
  carriers, assembled as `toSSet`, then `ModuleCat.free (ZMod 2)` levelwise,
  then `alternatingFaceMapComplex`.  Degree `n` is literally the free module on
  `singularSimplices X n`, the same carrier `cc-steenrod`'s `tensorTwo` uses,
  and **`∂∂ = 0` comes free** from `AlternatingFaceMapComplex.d_squared`; the
  only cost is one lemma dropping the alternating signs.
* `CartanDiagonalModule.lean` — the degreewise carrier of `W ⊗ S(X)`,
  `WSIndex k X = Σ n : Fin (k+1), (stdSimplexTop n.val ⟶ X)` and
  `WTensorSMod X k = WSIndex k X →₀ Λ`, with the differential split into its
  `(1+T)` half and its boundary half, each defined by a `Fin` eliminator so that
  no transport of the simplex ever appears.
* `CartanSourceComplex.lean` — **`d ∘ d = 0`**.  Four pieces: `(1+T)² = 0`;
  `∂∂ = 0`; and the two mixed terms, which are the same element and cancel in
  characteristic two.
* `CartanTargetBoundary.lean` — the singular boundary with coefficients in any
  `ZMod 2`-algebra, and **`∂∂ = 0` over those coefficients**, `Built (9.1s)`,
  `Build completed successfully (2078 jobs)`.  The proof is a *transfer*, not a
  computation: pushing coefficients along `algebraMap` is additive and sends a
  basis element to the corresponding basis element, so a vanishing sum of basis
  elements over `ZMod 2` pushes forward to a vanishing sum over `Λ`, and the
  `ZMod 2` statement is Mathlib's `d_comp_d`.  This is the differential the
  target of the diagonal needs on `cc-steenrod`'s ruled carrier.  The same
  transfer discharges any characteristic-two identity between sums of basis
  elements, which is why it is stated as a lemma about `coeffPush`.
* `CartanSourceFunctor.lean` — **the source functor `src` and its freeness
  `srcFree : FreeOnModels stdSimplexTop GroupRingZ2 (src data)`.**  Freeness
  costs nothing: the index `FreeOnModels` wants is `WSIndex k X` on the nose, so
  the basis is `Finsupp.basisSingleOne` with no reindexing and `basis_apply` is
  `Category.id_comp`.

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

### The source functor: the design, worked out, for whoever builds it next

The remaining objects are the source `W ⊗ S(X)`, the target with the `(13)(24)`
action, and the two composites.  The source is the next one to build and its
design is settled; the point below is the one that decides whether it is
pleasant or miserable.

**Index the degree-`k` carrier by the simplex dimension, not by the `W`-index.**
Take

```text
(W ⊗ S(X))_k := (Σ n : Fin (k+1), singularSimplices X ↑n) →₀ Λ
```

so that the `W`-index is the *derived* quantity `i = k - n`.  With the opposite
convention (index by `i`, dimension `k - i`) both terms of the differential need
a transport of `σ` along `(k-1)-(i-1) = k-i`, i.e. a cast in the *definition* —
and a dependent proof argument in a definition blocks every later `rw`.  With
this convention there is no cast at all, because:

* the `(1 + T)` term keeps the simplex and lowers only the `W`-index, so it is
  the same `σ` at the same dimension;
* the boundary term lowers only the dimension.

**Get both branches from `Fin` eliminators, not from `if`.**  Write the two
terms as separate functions on the basis:

```lean
-- present unless the W-index is already 0, i.e. unless n = last
Fin.lastCases (motive := fun n => singularSimplices X ↑n → _)
  (fun _ => 0) (fun j σ => (1 + groupRingGen) • Finsupp.single ⟨j, σ⟩ 1)

-- present unless the dimension is 0
Fin.cases (motive := fun n => singularSimplices X ↑n → _)
  (fun _ => 0) (fun i σ => ∑ j, Finsupp.single ⟨i, faceSimplex X ↑i j σ⟩ 1)
```

`↑(j.castSucc) = ↑j` and `↑(i.succ) = ↑i + 1` are both `rfl`, so in each branch
the simplex already has the dimension the target index wants.  That is what
removes the casts; an `if` on `↑n < k+1` would not, because the branch would not
carry the decomposition of `n`.

Then `d ∘ d = 0` is four groups: `(1+T)² = 0`; the two mixed terms are equal and
cancel in characteristic two; and `∂∂ = 0` for the simplex part, which is now
available from `CartanSingular.lean` rather than needing the simplicial-identity
pairing argument.

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
* **`rw` refuses goals that are only defeq after unfolding a functor
  composition.**  `(singFree.obj X).X (n+1)` and
  `singFreeSimplicial.obj X _⦋n+1⦌` are definitionally equal, but only after
  unfolding `Functor.comp`, `alternatingFaceMapComplex` and `ChainComplex.of`,
  which `rw`'s type-correctness check does not do (it works at `instances`
  transparency).  Rewriting with a lemma whose right-hand side is a sum of
  `δ i`'s therefore produces a goal `rw` will not touch again, with the message
  "the target expression is not type-correct under the `instances` transparency
  level".  `congrArg` at an ascribed type does not fix it either, because the
  term's *inferred* type is what matters.  The fix that works: introduce the
  morphisms you need **named at the target type** (`singFace X n i :
  (singFree.obj X).X (n+1) ⟶ (singFree.obj X).X n`), prove they are the ones you
  mean by `rfl` at definition time where full defeq is available, and never let
  the other presentation into a `rw`.
* `(ModuleCat.ofHom L).hom` is `rfl`-equal to `L`, so a goal about it is best
  opened with `show` (full defeq) rather than `rw [ModuleCat.hom_ofHom]`, which
  has to match the `ModuleCat.of ↑M` roundtrip syntactically and often will not.
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

## The middle-four interchange is a chain map (2026-09-06)

`tensorD_midSwap` and `midSwapHom` in `CartanMidFourChainMap`, green, landed.
Five modules: `CartanPadTen`, `CartanMidFourGroup`, `CartanMidFourTgt`,
`CartanMidFourSrc`, `CartanMidFourChainMap`, reached from the root through
`CartanMidFourSlots`, which is now the entry point and defines nothing.

Twenty-six probes failed on this before the design changed, and none of them
failed on the mathematics.  The lesson is worth stating in general terms.

* **Never let a degree be an expression in the inputs.**  Carry every degree of
  the result as a free parameter and absorb the constraint into a constructor
  that returns `0` off the diagonal.  `padTen A B k a b u v` is the decomposable
  `u ⊗ v` in total degree `k`, or `0` when `a + b ≠ k`.  Two `padTen`s at the
  same three degrees are literally the same term whatever route produced them.
  The recipe is cc-steenrod's; it is what removed every degree cast from their
  lane, and it removed the whole difficulty here.
* What it fixes: `a + 1 + b` and `(a + b) + 1` are propositionally but not
  definitionally equal for a variable `b`, because addition on the naturals
  recurses on its second argument.  `Nat.succ_add` does not fire, because the
  successor is spelled as an addition.  Closing the gap definitionally is shut
  off too, because any such check unfolds the tensor's structure literal and
  exceeds the heartbeat budget.
* **A predecessor degree wants truncated subtraction, not a successor
  equation.**  `hf : f = e - 1` and `hf : f + 1 = e` differ exactly at `e = 0`,
  where the second makes the statement vacuous.  Both grouping lemmas need that
  case, so the second form fails by proving nothing.
* `split_ifs` on the padded generator times out at `whnf` inside 200k
  heartbeats: deciding the degree equation unfolds the structure literal.
  `by_cases` plus two projection lemmas costs nothing.  Four of the nine errors
  in the first round were this.
* `rw [← tenElt_single_single]` cannot find its own right-hand side when the
  complexes are left to be inferred: the pattern's index type is a metavariable
  applied to a structure projection.  Restating the three nested rewrites as one
  lemma with every argument explicit makes the same rewrite fire.
* **Two modules declaring the same name in one namespace is a root-only
  failure.**  Probes never see it, because no single probe imports both; the
  root imports everything and dies.  When a redesign supersedes a definition,
  retire the old module in the same wave, and check the root's import list
  rather than the probe.

## Evaluating the Cartan comparison (2026-09-06)

Composite A now evaluates to the left-hand side of the Cartan formula, and the
descent that turns the comparison into a statement about cohomology classes is
built as far as it can go without composite B.  Nine modules, all green, all
landed; 53 owned modules build together at 2914 jobs.

The chain, in order.

* `pairEvalIdx` pairs two cochains against the whole degree-`k` pair module,
  agreeing with cc-steenrod's fixed-bidegree `pairEval` on the matching bidegree
  and vanishing on every other.  `pairEvalIdx_phiPair`: pairing against
  Steenrod's diagonal is evaluating the cup-`i` product.
* `pairEvalIdx_phiZero_eq_evAt`: pairing against the Alexander-Whitney diagonal
  is evaluating the cup product, in **every degree at once**, with no side
  condition, because both sides vanish off degree `p + q` for the same reason.
  Statements of that shape are what let a lemma be used inside an induction over
  a chain whose degrees are not known.
* `fourEvalF2_tenElt_pair`: the fourfold functional is the product of the two
  pair functionals, on the nose (`fourEvalGen_eq` is `rfl`).
* `fourEvalF2_compA_sqCochain` and `fourEval_compA_single`: composite A,
  evaluated against `α ⊗ β ⊗ α ⊗ β`, is `sqCochain (p+q) j (α ⌣ β)`.
* `fourEvalMor`: the functional as a morphism of group-ring modules, with
  `trivialCoeffMod` as the coefficient object; it annihilates boundaries when
  the two cochains are cocycles.
* `fourEval_compA_eq_compB`: the master identity.  Two of the three terms of the
  homotopy identity die — the `d ∘ s` term because the functional annihilates
  boundaries, and the `1 + t` half of the source differential because the
  functional is group-ring linear into a trivial-action module and `2 = 0`.
* `fourEval_s_wDiffS`: the one surviving term is the coboundary of the homotopy
  cochain.

Degrees settle themselves throughout.  Two cochains of degree `p + q` pair
against a bidegree of the tensor square only in total degree twice that, so the
total degree is forced rather than chosen, and the simplex degree and cup index
that come out are exactly the ones the Steenrod square construction uses.  No
transport appears anywhere in the chain.

Traps confirmed by a failed probe, beyond the ones already listed.

* `map_sum` does not match under `instances` transparency when the summand's
  type is a `ModuleCat` carrier rather than the raw `Finsupp`.  Supply it as a
  term, through `congrArg` and `Eq.trans`; the same cure works for
  `Finset.sum_congr`, which as a rewrite hits the same wall.
* Rewriting a complex's differential inside a composition fails with "motive is
  not type correct", because the two sides of the `_d` lemma have syntactically
  different morphism types.  State the differential's action on an **element**
  and rewrite that.
* `(Fin.succ m).val` is definitionally `m.val + 1` but not syntactically; a
  `show` is needed before the rewrite that mentions it.
* A degree that must be the type of a cochain has to be written as the sum it
  is, not as a parameter with an equation to it: `sqCochain m j φ` with
  `hm : p + q = m` does not typecheck for `φ = α ⌣ β`.
