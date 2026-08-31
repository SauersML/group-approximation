import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.CoveringTransferBoundary
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.InducedOnRPCohomology

/-!
# Descending the mod-2 transfer to homology and cohomology

This file (Prompt 05 of the transfer/Gysin sequence) descends the **chain map**
`projTransferChainMap n : C_•(RPⁿ; F₂) ⟶ C_•(Sⁿ; F₂)` of
`CoveringTransferBoundary.lean` to:

* a **homology-level transfer** `projTransferHomologyZMod2 n k : Hₖ(RPⁿ; F₂) ⟶ Hₖ(Sⁿ; F₂)`,
  obtained by applying Mathlib's `HomologicalComplex.homologyFunctor`; and
* a **cohomology-level transfer** `cohTransferZMod2 n k : Hᵏ(Sⁿ; F₂) ⟶ Hᵏ(RPⁿ; F₂)`,
  obtained by *dualizing* the chain map with the same `Hom(-, F₂)` machinery that
  builds `singularCohomologyZMod2`, and then taking homology of the resulting
  cochain map. Its source and target are **definitionally** the existing
  `sphereCohomology n k` and `rpCohomology n k` objects.

## The direction of the cohomology transfer (important convention note)

The chain transfer goes `C_•(RPⁿ) ⟶ C_•(Sⁿ)`, so its homology transfer goes
`Hₖ(RPⁿ) ⟶ Hₖ(Sⁿ)` (base ⟶ cover). Dualizing a chain map with the
contravariant functor `Hom(-, F₂)` **reverses arrows**, so the induced cochain map
goes `C^•(Sⁿ) ⟶ C^•(RPⁿ)` and the cohomology transfer goes
`Hᵏ(Sⁿ) ⟶ Hᵏ(RPⁿ)` (cover ⟶ base). This is the genuine *cohomology transfer*
`tr` of the double cover; it is **not** `projPullback` (the pullback `proj^*`
goes `Hᵏ(RPⁿ) ⟶ Hᵏ(Sⁿ)` and is degenerate on the top class — see the project
documentation), and it is **not** faked from it.

`RPnTopClassTransfer n` requires producing a sphere top class from an `RPⁿ` top
class, i.e. a map in the **opposite** direction `Hⁿ(RPⁿ) ⟶ Hⁿ(Sⁿ)`. As recorded
in `docs/current/Transfer_Homology_Cohomology_Result.md`, no such non-degenerate
map arises by dualizing a chain map (the only chain map `C_•(Sⁿ) ⟶ C_•(RPⁿ)` is
the pushforward `proj_*`, whose dual is the degenerate `proj^*`). The assembly of
`RPnTopClassTransfer` (Prompt 09) will therefore route through the genuine
transfer `cohTransferZMod2` built here together with the top-degree
identifications of Prompts 07–08, rather than a single linear `RPⁿ ⟶ Sⁿ`
cohomology map.

## Main declarations

* `singularHomologyCxZMod2 X k` — the `k`-th mod-2 singular homology object of `X`.
* `projTransferHomologyZMod2 n k` — the homology-level transfer.
* `dualizeCochainFunctor` — the `Hom(-, F₂)` dualizer on chain complexes,
  matching the construction of `singularCochainComplexFunctor`.
* `cohTransferZMod2 n k : sphereCohomology n k ⟶ rpCohomology n k` — the
  cohomology-level transfer (genuine dual of the chain map).
* `cohTransferZMod2_hom_add`, `cohTransferZMod2_hom_smul` — `ZMod 2`-linearity.
* `RPToSphereTransferNaturalityOdd`, `RPToSphereTransferTopNonzero` — the two
  expected top-degree future facts, stated as `Prop` predicates (the analogues of
  `rpToSphereTransfer_naturality_odd` / `rpToSphereTransfer_top_nonzero`), to be
  discharged in Prompts 06–08.
-/

noncomputable section

open CategoryTheory AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-! ## 1. The homology-level transfer -/

/-- The `k`-th mod-2 singular homology object of a space `X`, as a
`ModuleCat (ZMod 2)` object, obtained by taking `k`-th homology of the singular
mod-2 chain complex `singularChainCx X`. -/
noncomputable def singularHomologyCxZMod2 (X : TopCat.{0}) (k : ℕ) : ModuleCat.{0} (ZMod 2) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{0} (ZMod 2)) (ComplexShape.down ℕ) k).obj
    (singularChainCx X)

/-- **The homology-level mod-2 transfer** of the double cover `Sⁿ → RPⁿ`,
in every degree `k`:
```text
projTransferHomologyZMod2 n k : Hₖ(RPⁿ; F₂) ⟶ Hₖ(Sⁿ; F₂).
```
It is induced by the chain map `projTransferChainMap n` of
`CoveringTransferBoundary.lean` via `HomologicalComplex.homologyFunctor`. -/
noncomputable def projTransferHomologyZMod2 (n k : ℕ) :
    singularHomologyCxZMod2 (TopCat.of (RP n)) k ⟶ singularHomologyCxZMod2 (TopCat.of (Sphere n)) k :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{0} (ZMod 2)) (ComplexShape.down ℕ) k).map
    (projTransferChainMap n)

/-- The homology transfer is induced by the chain map: it is the image of
`projTransferChainMap n` under the homology functor. -/
theorem projTransferHomologyZMod2_eq (n k : ℕ) :
    projTransferHomologyZMod2 n k
      = (HomologicalComplex.homologyFunctor (ModuleCat.{0} (ZMod 2)) (ComplexShape.down ℕ) k).map
          (projTransferChainMap n) :=
  rfl

/-! ## 2. The dualizer and the cohomology-level transfer -/

/-- The `Hom(-, M)` dualizer on chain complexes, sending a chain complex (viewed
in `(ChainComplex (ModuleCat R) ℕ)ᵒᵖ`) to the cochain complex `Hom(-, M)`. This
is the second half of the composite that defines `singularCochainComplexFunctor`,
factored out so that we can apply it to the chain map `projTransferChainMap`
directly (rather than only to chain complexes coming from spaces). -/
noncomputable def dualizeCochainFunctor (R : Type) [CommRing R] (M : ModuleCat.{0} R) :
    (ChainComplex (ModuleCat.{0} R) ℕ)ᵒᵖ ⥤ CochainComplex (ModuleCat.{0} R) ℕ :=
  HomologicalComplex.opFunctor _ _
    ⋙ ((linearYoneda R (ModuleCat.{0} R)).obj M).mapHomologicalComplex _

/-- `singularCochainComplexFunctor R M` factors through `dualizeCochainFunctor`:
it is `((singularChainComplexFunctor (ModuleCat R)).obj M).op ⋙ dualizeCochainFunctor R M`.
Definitional. -/
theorem singularCochainComplexFunctor_eq (R : Type) [CommRing R] (M : ModuleCat.{0} R) :
    singularCochainComplexFunctor R M
      = ((singularChainComplexFunctor (ModuleCat.{0} R)).obj M).op ⋙ dualizeCochainFunctor R M :=
  rfl

/-- **The cohomology-level mod-2 transfer** of the double cover `Sⁿ → RPⁿ`,
obtained by dualizing the chain map `projTransferChainMap n` with the same
`Hom(-, F₂)` machinery used to build `singularCohomologyZMod2`, and then taking
`k`-th cohomology:
```text
cohTransferZMod2 n k : Hᵏ(Sⁿ; F₂) ⟶ Hᵏ(RPⁿ; F₂).
```
Its source and target are **definitionally** the existing `sphereCohomology n k`
and `rpCohomology n k` objects. (This is the genuine cohomology *transfer* `tr` of
the cover; note the direction — see the module docstring — it is **not**
`projPullback`.) -/
noncomputable def cohTransferZMod2 (n k : ℕ) :
    sphereCohomology n k ⟶ rpCohomology n k :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{0} (ZMod 2)) (ComplexShape.up ℕ) k).map
    ((dualizeCochainFunctor (ZMod 2) (ModuleCat.of (ZMod 2) (ZMod 2))).map
      (projTransferChainMap n).op)

/-- The cohomology transfer is induced by the dualized chain map. -/
theorem cohTransferZMod2_eq (n k : ℕ) :
    cohTransferZMod2 n k
      = (HomologicalComplex.homologyFunctor (ModuleCat.{0} (ZMod 2)) (ComplexShape.up ℕ) k).map
          ((dualizeCochainFunctor (ZMod 2) (ModuleCat.of (ZMod 2) (ZMod 2))).map
            (projTransferChainMap n).op) :=
  rfl

/-- `ZMod 2`-additivity of the cohomology transfer (it is a `ModuleCat` morphism,
hence a bundled linear map). -/
@[simp] theorem cohTransferZMod2_hom_add (n k : ℕ) (x y : sphereCohomology n k) :
    (cohTransferZMod2 n k).hom (x + y)
      = (cohTransferZMod2 n k).hom x + (cohTransferZMod2 n k).hom y :=
  map_add _ _ _

/-- `ZMod 2`-homogeneity of the cohomology transfer. -/
@[simp] theorem cohTransferZMod2_hom_smul (n k : ℕ) (c : ZMod 2) (x : sphereCohomology n k) :
    (cohTransferZMod2 n k).hom (c • x) = c • (cohTransferZMod2 n k).hom x :=
  map_smul _ _ _

/-- The cohomology transfer sends `0` to `0`. -/
@[simp] theorem cohTransferZMod2_hom_zero (n k : ℕ) :
    (cohTransferZMod2 n k).hom 0 = 0 :=
  map_zero _

/-! ## 3. The two expected top-degree facts (stated, not yet proved)

These are the `Prop`-level statements of the future top-degree theorems
`rpToSphereTransfer_naturality_odd` and `rpToSphereTransfer_top_nonzero`,
phrased on the genuine cohomology transfer `cohTransferZMod2` built above. They
are recorded as `Prop` predicates (the same style as the existing
`RPnTopClassTransfer`) so that the present file stays placeholder-free; their proofs
are the subject of Prompts 06–08. -/

/-- **Future fact (naturality for odd self-maps).** The cohomology transfer of the
double cover is natural with respect to an odd self-map `f` of `Sⁿ` and its
descent `fbar = inducedOnRP f hf`: the square

```text
        f^*
Hᵏ(Sⁿ) ─────────────▶ Hᵏ(Sⁿ)
   │                      │
tr │                      │ tr
   ▼                      ▼
Hᵏ(RPⁿ) ────────────▶ Hᵏ(RPⁿ)
        fbar^*
```

commutes, i.e. `spherePullback f k ≫ cohTransferZMod2 n k
  = cohTransferZMod2 n k ≫ inducedOnRPPullback f hf k`. To be proved in Prompt 06
from the chain-level naturality of `projTransferChainMap`. -/
def RPToSphereTransferNaturalityOdd (n k : ℕ) : Prop :=
  ∀ (f : C(Sphere n, Sphere n)) (hf : IsOddMap f),
    spherePullback f k ≫ cohTransferZMod2 n k
      = cohTransferZMod2 n k ≫ inducedOnRPPullback f hf k

/-- **Future fact (top-degree nonvanishing).** In the top degree `n`, the
cohomology transfer carries the nonzero top class of `Hⁿ(Sⁿ; F₂)` to the nonzero
top class of `Hⁿ(RPⁿ; F₂)` — equivalently, it is nonzero on the top class. To be
proved in Prompts 07–08 from the top-degree identifications. -/
def RPToSphereTransferTopNonzero (n : ℕ) : Prop :=
  ∀ c : sphereCohomology n n, c ≠ 0 → (cohTransferZMod2 n n).hom c ≠ 0

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
