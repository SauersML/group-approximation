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

Reprobed 2026-09-05 (Sonnet continuation): all six owned modules build clean
together, `Build completed successfully (1665 jobs)`.

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

Nothing.  Every declaration in the six owned modules is covered by the green
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

**Finding, for the lead and both lanes: the concrete `Φ` is much bigger than a
wiring step.**  I checked whether the *linearized* Alexander–Whitney/
Eilenberg–Zilber chain map `Δ : C_•(X) → C_•(X) ⊗ C_•(X)` (or its product
variant `C_•(X×Y) → C_•(X) ⊗ C_•(Y)`) exists anywhere already — vendored tree
or Mathlib at `81a5d257` — since either would be the natural scaffold to hang
`steenrodDiag` on.  It does not.
`ThirdParty/HamSandwich/SphereOddDegree/AlgebraicTopology/AlexanderWhitney.lean`
builds only the **object-level** (unlinearized) front/back-face data
(`awPair`, `frontSimplex`, `backSimplex`) and its own docstring names the
linearization into a genuine chain map as "the remaining blocker" — nobody has
built it, in either direction.  So even with `steenrodDiag` in hand, assembling
the actual functor `Φ : W ⊗ S(-×-) ⟶ (S(-) ⊗ S(-))^{⊗2}` needs, from scratch:
the periodic resolution `W` (cheap: mod 2, `1 - T ≡ 1 + T`, so the classical
`⋯ → Λ →^{1-T} Λ →^{1+T} Λ` resolution of `ZMod 2` over `Λ = (ZMod 2)[ℤ/2]`
collapses to *one* repeated differential — a small, self-contained
`ChainComplex.of` construction, independent of everything below), the
Eilenberg–Zilber comparison for a literal product of two different spaces, and
the verification that evaluating the two sides against a cocycle pair
reproduces the cross-Cartan sum on the nose.  That is comparable in size to a
full lane's remaining budget, not a small bridge, and building it myself would
both duplicate what `cc-steenrod` explicitly declined (for good reason — cost)
and carry real risk of not finishing cleanly under remote-only, one-probe-at-a-
time iteration.  I am not attempting it in this session; the six owned modules
are green and stable regardless, and I will consume `steenrodDiag` the moment
it lands.  The `W` construction above is cheap enough that I would take it on
if either lane or the lead wants it split out as a separate, well-defined unit
of work — say so in this file or by message.

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
* Acyclicity must be stated for *positive* degrees only: the singular chain
  complex of a contractible space is **not** contractible (its `H_0` is the
  coefficient ring), only its augmentation is.  A "null-homotopy of the
  identity" hypothesis would be false for every model.
