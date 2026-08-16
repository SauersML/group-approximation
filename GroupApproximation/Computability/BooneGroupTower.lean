import GroupApproximation.Computability.BooneGroupPresentation
import Mathlib.GroupTheory.HNNExtension

/-!
# S3: the HNN tower

Simpson's Definition 6 builds `G'_M` from the base group by adjoining one stable
letter per machine quadruple, each conjugating one copy of `G_{ab}^{MM}` onto
another copy `G_{c0}^{M²,1}`.  Mathlib's `HNNExtension` carries **one** stable
letter, so the tower has to be built one letter at a time.

The obstacle to writing that as a recursive *type* is that each stage's
subgroups live in the previous stage, so the type, its group instance and the
embedding of the base group would all have to be defined by the same recursion.
Bundling them avoids it entirely: a `Stage` carries the carrier, its group
structure, the map from the base group, and the proof that map is injective, and
`Stage.step` is an ordinary function on bundles.  The tower is then a fold, and
injectivity of the composite `ι` is maintained as an invariant rather than
proved afterwards --- `HNNExtension.of_injective` composed with the previous
stage's injectivity.

The identification attached to a quadruple is `quadEquiv`: both
`G_{ab}^{MM}` and `G_{c0}^{M²,1}` are ranges of injective embeddings of the base
group, so each is isomorphic to the base group, and the composite of one
isomorphism with the inverse of the other is the required
`G_{ab}^{MM} ≃* G_{c0}^{M²,1}`.

What is *not* here is the correctness of the tower --- that is S4, the
good-subgroup lemma, which is the only place Britton's Lemma is used.
-/

namespace GroupApproximation
namespace BooneGroup

open Base

/-- A stage of the tower: a group with an injection of the base group. -/
structure Stage where
  /-- The group at this stage. -/
  Carrier : Type
  /-- Its group structure. -/
  group : Group Carrier
  /-- The base group, embedded. -/
  ι : BaseGroup →* Carrier
  /-- The embedding is injective; maintained as an invariant up the tower. -/
  ι_injective : Function.Injective ι

attribute [instance] Stage.group

/-- The bottom of the tower: the base group itself. -/
def Stage.base : Stage where
  Carrier := BaseGroup
  group := inferInstance
  ι := MonoidHom.id _
  ι_injective := fun _ _ h => h

/-- Adjoin one stable letter, conjugating the image of `A` onto the image of `B`
along `ψ`.  This is one step of Simpson's Definition 6. -/
noncomputable def Stage.step (S : Stage) {A B : Subgroup BaseGroup} (ψ : A ≃* B) : Stage where
  Carrier :=
    HNNExtension S.Carrier (A.map S.ι) (B.map S.ι)
      (((Subgroup.equivMapOfInjective A S.ι S.ι_injective).symm.trans ψ).trans
        (Subgroup.equivMapOfInjective B S.ι S.ι_injective))
  group := inferInstance
  ι := (HNNExtension.of).comp S.ι
  ι_injective := by
    intro x y h
    apply S.ι_injective
    apply HNNExtension.of_injective
    exact h

/-- An identification of base subgroups, as the tower consumes them. -/
abbrev Identification := Σ A B : Subgroup BaseGroup, A ≃* B

/-- **The tower.**  One stable letter per identification, bottom to top. -/
noncomputable def tower : List Identification → Stage
  | [] => Stage.base
  | ⟨_, _, ψ⟩ :: l => (tower l).step ψ

/-- **The base group embeds in every stage.**  This is the invariant the bundle
carries, and it is what Britton's Lemma will be applied against. -/
theorem tower_ι_injective (l : List Identification) :
    Function.Injective (tower l).ι :=
  (tower l).ι_injective

@[simp] theorem tower_nil : tower [] = Stage.base := rfl

@[simp] theorem tower_cons (A B : Subgroup BaseGroup) (ψ : A ≃* B)
    (l : List Identification) :
    tower (⟨A, B, ψ⟩ :: l) = (tower l).step ψ := rfl

/-! ## The identification a machine quadruple supplies

Simpson attaches to a quadruple the identification of `G_{ab}^{MM}` with
`G_{c0}^{M²,1}`.  Both are ranges of injective embeddings of the base group, so
both are isomorphic to it, and the identification is the composite. -/

/-- The isomorphism `G_{ab}^{MM} ≃* G_{c0}^{M²,1}` attached to a quadruple. -/
noncomputable def quadEquiv (a b c M : ℤ) (hM : M ≠ 0) :
    Gsub a b M M ≃* Gsub c 0 (M ^ 2) 1 :=
  (MonoidHom.ofInjective (emb_injective (a := a) (b := b) hM hM)).symm.trans
    (MonoidHom.ofInjective
      (emb_injective (a := c) (b := 0) (pow_ne_zero 2 hM) one_ne_zero))

/-- The identification a quadruple contributes to the tower. -/
noncomputable def quadIdentification (a b c M : ℤ) (hM : M ≠ 0) : Identification :=
  ⟨Gsub a b M M, Gsub c 0 (M ^ 2) 1, quadEquiv a b c M hM⟩

end BooneGroup
end GroupApproximation
