import GroupApproximation.Manuscript.NonMFNotes.Full.TWWKK.Qalg
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWKK.StabMap
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWUCT.BootstrapClosureBasic

/-!
# The Cuntz functor `A ↦ 𝒦 ⊗ qA` on separable non-unital C⋆-algebras

Cuntz (J. Cuntz, *A new look at KK-theory*, K-Theory 1 (1987), §§1--3) describes `KK(A, B)`
as the set of homotopy classes of `⋆`-homomorphisms `𝒦 ⊗ qA → 𝒦 ⊗ qB`, and this description
makes sense for non-unital `A` and `B`.  This file bundles the functor `A ↦ Stab (Qalg A)`
(lane TWWKK: `Qalg` is Cuntz's `qA`, `Stab` the spatial stabilization `𝒦 ⊗ -`) as a
`Bootstrap.KKnFunctor`.  It is the intended instance of the bootstrap layer
(`BootstrapClosure*`), of the unital-model comparison (`UnitalModel*`) and of the
Higson--Kasparov and proper-crossed-product lanes, used for the Tikuisis--White--Winter input of
`thm:fixed-radical-membership` in `non_mf_group_notes.tex`.

Contents:
* `Bootstrap.stabQn : KKnFunctor`, with `obj A = Stab (Qalg A)` and `map f = Stab.map (Qalg.map f)`;
* `stabQn_obj`, `stabQn_map`, `stabQn_map_apply`: its values, by definition;
* `stabQn_kknEquivalent_of_homotopyEquiv`, `stabQn_kknEquivalent_of_starAlgEquiv`: the two basic
  sources of `KKn`-equivalences, specialised to `stabQn`.

The functoriality of `Stab` (`Stab.map`, `map_id`, `map_comp`, `map_nhomotopic`) is supplied
by lane TWWKK-Stab (A1).
-/

namespace GroupApproximation.Full.TWWUCT.Bootstrap

open GroupApproximation.Full.TWWKK

noncomputable section

/-- **The Cuntz functor** `A ↦ 𝒦 ⊗ qA`, bundled as a `KKnFunctor`: the object map is
`Stab ∘ Qalg`, the morphism map `Stab.map ∘ Qalg.map`, and both factors preserve identities,
composites and homotopies. -/
def stabQn : KKnFunctor where
  obj A := Stab (Qalg A)
  map f := Stab.map (Qalg.map f)
  map_id A := by
    show Stab.map (Qalg.map (NonUnitalStarAlgHom.id ℂ A)) = _
    rw [Qalg.map_id, Stab.map_id]
  map_comp f g := by
    show Stab.map (Qalg.map (g.comp f)) = (Stab.map (Qalg.map g)).comp (Stab.map (Qalg.map f))
    rw [Qalg.map_comp, Stab.map_comp]
  map_nHomotopic h := Stab.map_nhomotopic (Qalg.map_nhomotopic h)

theorem stabQn_obj (A : SepNUCStarAlgebra) : stabQn.obj A = Stab (Qalg A) :=
  rfl

theorem stabQn_map {A B : SepNUCStarAlgebra} (f : A →⋆ₙₐ[ℂ] B) :
    stabQn.map f = Stab.map (Qalg.map f) :=
  rfl

theorem stabQn_map_apply {A B : SepNUCStarAlgebra} (f : A →⋆ₙₐ[ℂ] B) (x : Stab (Qalg A)) :
    stabQn.map f x = Stab.map (Qalg.map f) x :=
  rfl

/-- Homotopy-equivalent separable algebras are `KKn`-equivalent for the Cuntz functor. -/
theorem stabQn_kknEquivalent_of_homotopyEquiv {A B : SepNUCStarAlgebra} (f : A →⋆ₙₐ[ℂ] B)
    (g : B →⋆ₙₐ[ℂ] A) (hgf : NHomotopic (g.comp f) (NonUnitalStarAlgHom.id ℂ A))
    (hfg : NHomotopic (f.comp g) (NonUnitalStarAlgHom.id ℂ B)) : stabQn.KKnEquivalent A B :=
  KKnFunctor.kknEquivalent_of_homotopyEquiv (F := stabQn) f g hgf hfg

/-- `⋆`-isomorphic separable algebras are `KKn`-equivalent for the Cuntz functor. -/
theorem stabQn_kknEquivalent_of_starAlgEquiv {A B : SepNUCStarAlgebra} (e : A ≃⋆ₐ[ℂ] B) :
    stabQn.KKnEquivalent A B :=
  KKnFunctor.kknEquivalent_of_inverse (F := stabQn) e.toNonUnitalStarAlgHom
    e.symm.toNonUnitalStarAlgHom (fun a => e.symm_apply_apply a) (fun b => e.apply_symm_apply b)

end

end GroupApproximation.Full.TWWUCT.Bootstrap
