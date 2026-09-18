import GroupApproximation.Manuscript.NonMFNotes.Full.TWWKK.StableFunctor
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWKK.StabQGroupAbstract

/-!
# Cuntz groups for a stabilized homotopy functor

Let `F` be a `StableFunctor` whose values carry `CuntzStable` structures, with an endomorphism
`ν A` of each `F A` satisfying `[id ⊕ ν A] = 0`.  Then:

* `StableFunctor.cuntzGroups`: the morphism sets `F.Hom A B = [F A, F B]` are abelian groups
  under the Cuntz sum;
* `StableFunctor.compBilinear_cuntzGroups`: composition is bilinear (`F.CompBilinear`).

For `F = stabQ` (`A ↦ 𝒦 ⊗ qA`) this gives Cuntz's theorem that `KK(A, B) = [𝒦 ⊗ qA, 𝒦 ⊗ qB]`
is an abelian group with bilinear product (J. Cuntz, *A new look at KK-theory*, K-Theory 1
(1987), §1--3; Blackadar 17.8).

Manuscript: `non_mf_group_notes.tex`, UCT hypothesis of `thm:fixed-radical-membership`.
Work order `WO-TWWKK-B`.
-/

namespace GroupApproximation.Full.TWWKK

noncomputable section

namespace StableFunctor

variable (F : StableFunctor)

/-- **The Cuntz group structures** on the morphism sets of a stabilized homotopy functor. -/
def cuntzGroups (S : ∀ A : KK.SepCStarAlgebra.{0}, CuntzStable (F.obj A))
    (ν : ∀ A : KK.SepCStarAlgebra.{0}, F.obj A →⋆ₙₐ[ℂ] F.obj A)
    (hν : ∀ A : KK.SepCStarAlgebra.{0},
      HomotopyClass.mk ((S A).sum (NonUnitalStarAlgHom.id ℂ (F.obj A)) (ν A)) =
        HomotopyClass.mk 0)
    (A B : KK.SepCStarAlgebra.{0}) : AddCommGroup (F.Hom A B) :=
  (S B).cuntzAddCommGroup (S A) (ν A) (hν A)

/-- **Composition is bilinear** for the Cuntz group structures. -/
theorem compBilinear_cuntzGroups (S : ∀ A : KK.SepCStarAlgebra.{0}, CuntzStable (F.obj A))
    (ν : ∀ A : KK.SepCStarAlgebra.{0}, F.obj A →⋆ₙₐ[ℂ] F.obj A)
    (hν : ∀ A : KK.SepCStarAlgebra.{0},
      HomotopyClass.mk ((S A).sum (NonUnitalStarAlgHom.id ℂ (F.obj A)) (ν A)) =
        HomotopyClass.mk 0) :
    @CompBilinear F (F.cuntzGroups S ν hν) := by
  intro A B C x x' y y'
  exact ⟨(S B).comp_addClass_left (S C) y x x', (S C).comp_addClass_right y y' x⟩

end StableFunctor

end

end GroupApproximation.Full.TWWKK
