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

*(job counts recorded here as probes come back; a green claim without a job
count is not a green claim)*

## 2. AUTHORED, UNVERIFIED

* `GroupApproximation/CharClass/AcyclicModels.lean` — the acyclic-models
  theorem.  Contents:
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
