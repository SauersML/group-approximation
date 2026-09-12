import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.CoveringTransferHomology
import GroupApproximation.Meta.AxiomGuard

/-!
# Naturality of the double-cover transfer for odd self-maps

This file (Prompt 06 of the transfer/Gysin sequence) proves that the genuine
mod-2 **transfer** of the double cover `proj n : Sⁿ → RPⁿ` is natural with
respect to an odd self-map `f` of `Sⁿ` and its descent
`fbar = inducedOnRP f hf` on `RPⁿ`.

The transfer constructed in Prompts 04–05 is the chain map
`projTransferChainMap n : C_•(RPⁿ; F₂) ⟶ C_•(Sⁿ; F₂)`, whose dualization gives
the genuine cohomology transfer `cohTransferZMod2 n k : Hᵏ(Sⁿ; F₂) ⟶ Hᵏ(RPⁿ; F₂)`
(cover → base; this is **not** the degenerate `projPullback`). The naturality
square we prove is therefore

```text
        f^*
Hᵏ(Sⁿ) ─────────────▶ Hᵏ(Sⁿ)
   │                      │
tr │                      │ tr
   ▼                      ▼
Hᵏ(RPⁿ) ────────────▶ Hᵏ(RPⁿ)
       fbar^*
```

i.e. `spherePullback f k ≫ cohTransferZMod2 n k
  = cohTransferZMod2 n k ≫ inducedOnRPPullback f hf k`, which is exactly the
predicate `RPToSphereTransferNaturalityOdd n k` recorded in
`CoveringTransferHomology.lean`.

## Strategy

The proof starts at the **chain level** and uses the actual point-set commuting
square `inducedOnRP_comp_proj` (`fbar ∘ proj = proj ∘ f`) together with
simplex-lift uniqueness:

* `singularChainFunctor_map_ι` — the singular chain pushforward of a continuous
  map acts on a basis simplex by post-composition.
* `oddMap_comp_antipodal` — an odd map commutes with the antipodal map.
* `projTransfer_naturality_degree` — the degreewise chain naturality, proved by
  comparing both sides through `projTransferOnSimplex_eq_of_lift` with a common
  lift `f ∘ τ` of `fbar ∘ σ` (here `τ` is a lift of `σ`; the second sheet
  `f ∘ (antipodal ∘ τ)` equals `antipodal ∘ (f ∘ τ)` because `f` is odd).
* `projTransferChainMap_naturality_odd` — the chain-map naturality, assembled
  degreewise.
* `rpToSphereTransfer_naturality_odd` — the cohomology naturality, obtained from
  the chain naturality by applying the dualizer and the homology functor (both
  functorial; the opposite category reverses arrows).
* `rpToSphereTransferNaturalityOdd_holds` — repackages the result as the
  `RPToSphereTransferNaturalityOdd n k` predicate for Prompt 09.

No use of the ordinary `projPullback` (`proj^*`) is made anywhere.
-/

noncomputable section

open CategoryTheory AlgebraicTopology Limits

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The singular mod-two chain map induced by a continuous map, stated directly
in the current simplicial-set chain-complex API. -/
noncomputable abbrev singularChainMapZMod2 {X Y : TopCat.{0}} (g : X ⟶ Y) :
    (TopCat.toSSet.obj X).chainComplex transferCoeff ⟶
      (TopCat.toSSet.obj Y).chainComplex transferCoeff :=
  SSet.chainComplexMap (TopCat.toSSet.map g) transferCoeff

/-- **Pushforward on a basis simplex.** The degree-`k` component of the chain map
induced by a continuous map `g : X → Y` sends the basis generator of a singular
simplex `σ` to the basis generator of its post-composition `g ∘ σ` (expressed
through `TopCat.toSSetObjEquiv`). -/
theorem singularChainFunctor_map_ι {X Y : TopCat.{0}} (g : X ⟶ Y) (k : ℕ)
    (σ : singularSimplices X k) :
    (TopCat.toSSet.obj X).ιChainComplex σ
        ≫ (singularChainMapZMod2 g).f k
      = (TopCat.toSSet.obj Y).ιChainComplex
          ((TopCat.toSSet.map g).app (Opposite.op (SimplexCategory.mk k)) σ) :=
  SSet.ι_chainComplexMap_f _ _ _ _ _

/-- A singular simplex is pushed forward by postcomposition. -/
@[simp] theorem toSSet_map_apply_singularSimplex {X Y : TopCat.{0}} (g : X ⟶ Y)
    (k : ℕ) (σ : singularSimplices X k) :
    (TopCat.toSSet.map g).app (Opposite.op (SimplexCategory.mk k)) σ =
      (TopCat.toSSetObjEquiv Y (Opposite.op (SimplexCategory.mk k))).symm
        (g.hom.comp (TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk k)) σ)) :=
  rfl

/-- An odd self-map of the sphere commutes with the antipodal map:
`f ∘ antipodal = antipodal ∘ f`. -/
theorem oddMap_comp_antipodal {n : ℕ} (f : C(Sphere n, Sphere n)) (hf : IsOddMap f) :
    f.comp (antipodal n) = (antipodal n).comp f := by
  apply ContinuousMap.ext
  intro x
  exact hf x

/-- The defining equation for the transfer, phrased with Mathlib's canonical
singular-chain basis inclusion. -/
theorem projTransferChainDegree_ιChain (n k : ℕ)
    (σ : singularSimplices (TopCat.of (RP n)) k) :
    (TopCat.toSSet.obj (TopCat.of (RP n))).ιChainComplex σ ≫
        projTransferChainDegree n k = projTransferOnSimplex n k σ := by
  simpa only [SSet.ιChainComplex] using projTransferChainDegree_ι n k σ

/-- **Degreewise chain naturality of the transfer.** For an odd self-map `f` of
`Sⁿ` with descent `fbar = inducedOnRP f hf`, the degree-`k` transfer commutes with
the chain pushforwards of `f` and `fbar`:
```text
tr_k ≫ f_* = fbar_* ≫ tr_k.
``` -/
theorem projTransfer_naturality_degree {n : ℕ} (f : C(Sphere n, Sphere n)) (hf : IsOddMap f)
    (k : ℕ) :
    projTransferChainDegree n k ≫ (singularChainMapZMod2 (TopCat.ofHom f)).f k
      = (singularChainMapZMod2 (TopCat.ofHom (inducedOnRP f hf))).f k
          ≫ projTransferChainDegree n k := by
  apply SSet.chainComplex_hom_ext
  intro σ
  change
    (Sigma.ι (fun _ : singularSimplices (TopCat.of (RP n)) k => transferCoeff) σ ≫
        projTransferChainDegree n k) ≫ (singularChainMapZMod2 (TopCat.ofHom f)).f k =
      (Sigma.ι (fun _ : singularSimplices (TopCat.of (RP n)) k => transferCoeff) σ ≫
        (singularChainMapZMod2 (TopCat.ofHom (inducedOnRP f hf))).f k) ≫
          projTransferChainDegree n k
  set σc := TopCat.toSSetObjEquiv (TopCat.of (RP n)) (Opposite.op (SimplexCategory.mk k)) σ with hσc
  set v₀ : TopologicalSimplex k := Classical.arbitrary _ with hv₀
  set e : Sphere n := (proj_surjective n (σc v₀)).choose with he_def
  have he : proj n e = σc v₀ := (proj_surjective n (σc v₀)).choose_spec
  set τ : C(TopologicalSimplex k, Sphere n) := projLiftSimplex σc v₀ e he with hτ_def
  have hlift : ⇑(proj n) ∘ ⇑τ = ⇑σc := projLiftSimplex_lifts σc v₀ e he
  rw [projTransferChainDegree_ι,
      projTransferOnSimplex_eq_of_lift n k σ τ hlift]
  change
    ((TopCat.toSSet.obj (TopCat.of (Sphere n))).ιChainComplex
          ((TopCat.toSSetObjEquiv (TopCat.of (Sphere n))
            (Opposite.op (SimplexCategory.mk k))).symm τ) +
        (TopCat.toSSet.obj (TopCat.of (Sphere n))).ιChainComplex
          ((TopCat.toSSetObjEquiv (TopCat.of (Sphere n))
            (Opposite.op (SimplexCategory.mk k))).symm ((antipodal n).comp τ))) ≫
        (singularChainMapZMod2 (TopCat.ofHom f)).f k =
      ((TopCat.toSSet.obj (TopCat.of (RP n))).ιChainComplex σ ≫
        (singularChainMapZMod2 (TopCat.ofHom (inducedOnRP f hf))).f k) ≫
          projTransferChainDegree n k
  rw [Preadditive.add_comp,
      singularChainFunctor_map_ι (X := TopCat.of (Sphere n)) (Y := TopCat.of (Sphere n))
        (TopCat.ofHom f) k
        ((TopCat.toSSetObjEquiv (TopCat.of (Sphere n)) (Opposite.op (SimplexCategory.mk k))).symm τ),
      singularChainFunctor_map_ι (X := TopCat.of (Sphere n)) (Y := TopCat.of (Sphere n))
        (TopCat.ofHom f) k
        ((TopCat.toSSetObjEquiv (TopCat.of (Sphere n)) (Opposite.op (SimplexCategory.mk k))).symm
          ((antipodal n).comp τ)),
      singularChainFunctor_map_ι (X := TopCat.of (RP n)) (Y := TopCat.of (RP n))
        (TopCat.ofHom (inducedOnRP f hf)) k σ,
      projTransferChainDegree_ιChain]
  simp only [toSSet_map_apply_singularSimplex, Equiv.apply_symm_apply]
  have hτ' : ⇑(proj n) ∘ ⇑(f.comp τ)
      = ⇑(TopCat.toSSetObjEquiv (TopCat.of (RP n)) (Opposite.op (SimplexCategory.mk k))
          ((TopCat.toSSetObjEquiv (TopCat.of (RP n)) (Opposite.op (SimplexCategory.mk k))).symm
            ((inducedOnRP f hf).comp σc))) := by
    rw [Equiv.apply_symm_apply]
    funext x
    simp only [Function.comp_apply, ContinuousMap.comp_apply]
    rw [← projLiftSimplex_lifts_apply σc v₀ e he x]
    exact (inducedOnRP_comm f hf (τ x)).symm
  change
    (TopCat.toSSet.obj (TopCat.of (Sphere n))).ιChainComplex
          ((TopCat.toSSetObjEquiv (TopCat.of (Sphere n))
            (Opposite.op (SimplexCategory.mk k))).symm (f.comp τ)) +
        (TopCat.toSSet.obj (TopCat.of (Sphere n))).ιChainComplex
          ((TopCat.toSSetObjEquiv (TopCat.of (Sphere n))
            (Opposite.op (SimplexCategory.mk k))).symm (f.comp ((antipodal n).comp τ))) =
      projTransferOnSimplex n k
        ((TopCat.toSSetObjEquiv (TopCat.of (RP n))
          (Opposite.op (SimplexCategory.mk k))).symm ((inducedOnRP f hf).comp σc))
  rw [projTransferOnSimplex_eq_of_lift n k
      ((TopCat.toSSetObjEquiv (TopCat.of (RP n)) (Opposite.op (SimplexCategory.mk k))).symm
        ((inducedOnRP f hf).comp σc)) (f.comp τ) hτ']
  congr 2
  rw [← ContinuousMap.comp_assoc, ← ContinuousMap.comp_assoc, oddMap_comp_antipodal f hf]

/-- **Chain-map naturality of the transfer.** The transfer chain map of the double
cover is natural for an odd self-map `f` of `Sⁿ` and its descent
`fbar = inducedOnRP f hf`:
```text
projTransferChainMap n ≫ f_* = fbar_* ≫ projTransferChainMap n.
``` -/
theorem projTransferChainMap_naturality_odd {n : ℕ} (f : C(Sphere n, Sphere n)) (hf : IsOddMap f) :
    projTransferChainMap n ≫ singularChainMapZMod2 (TopCat.ofHom f)
      = singularChainMapZMod2 (TopCat.ofHom (inducedOnRP f hf)) ≫ projTransferChainMap n := by
  apply HomologicalComplex.hom_ext
  intro k
  change projTransferChainDegree n k ≫ (singularChainMapZMod2 (TopCat.ofHom f)).f k
      = (singularChainMapZMod2 (TopCat.ofHom (inducedOnRP f hf))).f k
          ≫ projTransferChainDegree n k
  exact projTransfer_naturality_degree f hf k

/-- **Naturality of the cohomology transfer for odd self-maps.** For an odd
self-map `f` of `Sⁿ` with descent `fbar = inducedOnRP f hf`, the genuine
cohomology transfer `cohTransferZMod2` of the double cover fits into the commuting
square
```text
spherePullback f k ≫ cohTransferZMod2 n k
  = cohTransferZMod2 n k ≫ inducedOnRPPullback f hf k,
```
i.e. `Tr(f^* a) = fbar^*(Tr a)`. It is obtained from the chain-map naturality
`projTransferChainMap_naturality_odd` by applying the `Hom(-, F₂)` dualizer and
the homology functor (both functorial; the opposite category reverses arrows).
The ordinary pullback `projPullback` is **not** used. -/
theorem rpToSphereTransfer_naturality_odd {n k : ℕ}
    (f : C(Sphere n, Sphere n)) (hf : IsOddMap f) :
    spherePullback f k ≫ cohTransferZMod2 n k
      = cohTransferZMod2 n k ≫ inducedOnRPPullback f hf k := by
  show (HomologicalComplex.homologyFunctor (ModuleCat.{0} (ZMod 2)) (ComplexShape.up ℕ) k).map
        ((dualizeCochainFunctor (ZMod 2) (ModuleCat.of (ZMod 2) (ZMod 2))).map
          (singularChainMapZMod2 (TopCat.ofHom f)).op)
      ≫ (HomologicalComplex.homologyFunctor (ModuleCat.{0} (ZMod 2)) (ComplexShape.up ℕ) k).map
          ((dualizeCochainFunctor (ZMod 2) (ModuleCat.of (ZMod 2) (ZMod 2))).map
            (projTransferChainMap n).op)
      = (HomologicalComplex.homologyFunctor (ModuleCat.{0} (ZMod 2)) (ComplexShape.up ℕ) k).map
          ((dualizeCochainFunctor (ZMod 2) (ModuleCat.of (ZMod 2) (ZMod 2))).map
            (projTransferChainMap n).op)
        ≫ (HomologicalComplex.homologyFunctor (ModuleCat.{0} (ZMod 2)) (ComplexShape.up ℕ) k).map
            ((dualizeCochainFunctor (ZMod 2) (ModuleCat.of (ZMod 2) (ZMod 2))).map
              (singularChainMapZMod2 (TopCat.ofHom (inducedOnRP f hf))).op)
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
  congr 2
  rw [← op_comp, ← op_comp, projTransferChainMap_naturality_odd f hf]

/-- The naturality square of the cohomology transfer, packaged as the predicate
`RPToSphereTransferNaturalityOdd n k` recorded in `CoveringTransferHomology.lean`.
This is the form consumed by the Prompt-09 assembly of `RPnTopClassTransfer`. -/
theorem rpToSphereTransferNaturalityOdd_holds (n k : ℕ) :
    RPToSphereTransferNaturalityOdd n k :=
  fun f hf => rpToSphereTransfer_naturality_odd f hf

#audit_axioms projTransferChainMap_naturality_odd
#audit_axioms rpToSphereTransfer_naturality_odd

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
