import GroupApproximation.Sofic.SymmetricDoubleSubgroupReflection
import GroupApproximation.Higman.AmalgamPushout

/-!
# Matched subgroups embed as a sub-amalgam

Suppose `M` embeds in two groups `A` and `B`, and subgroups `Z ≤ A` and
`Q ≤ B` pull back to the same subgroup `Delta ≤ M`.  Then the small amalgam

`Z *_Delta Q`

maps injectively into `A *_M B`.  Its range is exactly the subgroup generated
by the images of `Z` and `Q`.

This is the structural half of the matched-subgroup descent used by the
paired-return cutter.  Injectivity is an application of the repository's
internal Bass--Serre base-change theorem; the two exact comap identities are
used precisely to show that the factor inclusions reflect membership in the
large edge group.  No conclusion-shaped hypothesis is present.
-/

namespace GroupApproximation
namespace Higman
namespace MatchedSubgroupAmalgam

open Monoid

variable {M₀ A B : Type}
  [Group M₀] [Group A] [Group B]
  (eA : M₀ →* A) (eB : M₀ →* B)
  (Z : Subgroup A) (Q : Subgroup B) (Delta : Subgroup M₀)

/-- The edge map from the matched subgroup into the left small factor. -/
def edgeToZ (hZ : Z.comap eA = Delta) : ↥Delta →* ↥Z :=
  ((eA.comp Delta.subtype).codRestrict Z fun d => by
    have hd : (d : M₀) ∈ Z.comap eA := by
      rw [hZ]
      exact d.property
    exact hd)

/-- The edge map from the matched subgroup into the right small factor. -/
def edgeToQ (hQ : Q.comap eB = Delta) : ↥Delta →* ↥Q :=
  ((eB.comp Delta.subtype).codRestrict Q fun d => by
    have hd : (d : M₀) ∈ Q.comap eB := by
      rw [hQ]
      exact d.property
    exact hd)

/-- The two-factor diagram for the small amalgam. -/
def smallEdge (hZ : Z.comap eA = Delta) (hQ : Q.comap eB = Delta) :
    ∀ b : Bool, ↥Delta →* Amalgam.fam ↥Z ↥Q b
  | false => edgeToZ eA Z Delta hZ
  | true => edgeToQ eB Q Delta hQ

/-- The factorwise inclusion of the small diagram into the large diagram. -/
def factorInclusion :
    ∀ b : Bool, Amalgam.fam ↥Z ↥Q b →* Amalgam.fam A B b
  | false => Z.subtype
  | true => Q.subtype

/-- The matched edge subgroup includes into the large edge group. -/
def edgeInclusion : ↥Delta →* M₀ := Delta.subtype

theorem factorInclusion_commutes
    (hZ : Z.comap eA = Delta) (hQ : Q.comap eB = Delta) :
    ∀ b, (factorInclusion Z Q b).comp (smallEdge eA eB Z Q Delta hZ hQ b) =
      (Amalgam.famHom eA eB b).comp (edgeInclusion Delta) := by
  intro b
  cases b <;> rfl

/-- The homomorphism from the small amalgam to the large amalgam. -/
def matchedMap
    (hZ : Z.comap eA = Delta) (hQ : Q.comap eB = Delta) :
    PushoutI (smallEdge eA eB Z Q Delta hZ hQ) →*
      Amalgam.Push eA eB :=
  PushoutBaseChange.map
    (smallEdge eA eB Z Q Delta hZ hQ)
    (Amalgam.famHom eA eB)
    (edgeInclusion Delta) (factorInclusion Z Q)
    (factorInclusion_commutes eA eB Z Q Delta hZ hQ)

/-- Left and right factor maps, with the dependent `Bool` family hidden behind
ordinary homomorphism types. -/
def smallInZ (hZ : Z.comap eA = Delta) (hQ : Q.comap eB = Delta) :
    ↥Z →* PushoutI (smallEdge eA eB Z Q Delta hZ hQ) :=
  PushoutI.of (φ := smallEdge eA eB Z Q Delta hZ hQ) false

def smallInQ (hZ : Z.comap eA = Delta) (hQ : Q.comap eB = Delta) :
    ↥Q →* PushoutI (smallEdge eA eB Z Q Delta hZ hQ) :=
  PushoutI.of (φ := smallEdge eA eB Z Q Delta hZ hQ) true

def bigInA : A →* Amalgam.Push eA eB :=
  PushoutI.of (φ := Amalgam.famHom eA eB) false

def bigInB : B →* Amalgam.Push eA eB :=
  PushoutI.of (φ := Amalgam.famHom eA eB) true

@[simp] theorem matchedMap_smallInZ
    (hZ : Z.comap eA = Delta) (hQ : Q.comap eB = Delta) (z : ↥Z) :
    matchedMap eA eB Z Q Delta hZ hQ (smallInZ eA eB Z Q Delta hZ hQ z) =
      bigInA eA eB (z : A) := by
  exact PushoutBaseChange.map_of
    (smallEdge eA eB Z Q Delta hZ hQ)
    (Amalgam.famHom eA eB) (edgeInclusion Delta)
    (factorInclusion Z Q)
    (factorInclusion_commutes eA eB Z Q Delta hZ hQ) false z

@[simp] theorem matchedMap_smallInQ
    (hZ : Z.comap eA = Delta) (hQ : Q.comap eB = Delta) (q : ↥Q) :
    matchedMap eA eB Z Q Delta hZ hQ (smallInQ eA eB Z Q Delta hZ hQ q) =
      bigInB eA eB (q : B) := by
  exact PushoutBaseChange.map_of
    (smallEdge eA eB Z Q Delta hZ hQ)
    (Amalgam.famHom eA eB) (edgeInclusion Delta)
    (factorInclusion Z Q)
    (factorInclusion_commutes eA eB Z Q Delta hZ hQ) true q

theorem smallEdge_injective
    (heA : Function.Injective eA) (heB : Function.Injective eB)
    (hZ : Z.comap eA = Delta) (hQ : Q.comap eB = Delta) :
    ∀ b, Function.Injective (smallEdge eA eB Z Q Delta hZ hQ b) := by
  intro b
  cases b with
  | false =>
      intro x y hxy
      apply Subtype.ext
      apply heA
      exact congrArg Subtype.val hxy
  | true =>
      intro x y hxy
      apply Subtype.ext
      apply heB
      exact congrArg Subtype.val hxy

theorem factorInclusion_reflects_range
    (hZ : Z.comap eA = Delta) (hQ : Q.comap eB = Delta) :
    ∀ b g, factorInclusion Z Q b g ∈ (Amalgam.famHom eA eB b).range →
      g ∈ (smallEdge eA eB Z Q Delta hZ hQ b).range := by
  intro b
  cases b with
  | false =>
      intro z hz
      change ↥Z at z
      obtain ⟨m, hm⟩ := hz
      change eA m = (z : A) at hm
      have hmDelta : m ∈ Delta := by
        rw [← hZ]
        change eA m ∈ Z
        rw [hm]
        exact z.property
      refine ⟨⟨m, hmDelta⟩, ?_⟩
      exact Subtype.ext hm
  | true =>
      intro q hq
      change ↥Q at q
      obtain ⟨m, hm⟩ := hq
      change eB m = (q : B) at hm
      have hmDelta : m ∈ Delta := by
        rw [← hQ]
        change eB m ∈ Q
        rw [hm]
        exact q.property
      refine ⟨⟨m, hmDelta⟩, ?_⟩
      exact Subtype.ext hm

/-- **Matched sub-amalgam embedding.**  Exact agreement of the two edge
intersections makes `Z *_Delta Q → A *_M B` injective. -/
theorem matchedMap_injective
    (heA : Function.Injective eA) (heB : Function.Injective eB)
    (hZ : Z.comap eA = Delta) (hQ : Q.comap eB = Delta) :
    Function.Injective (matchedMap eA eB Z Q Delta hZ hQ) := by
  apply PushoutBaseChange.map_injective_of_reflects_range
  · exact smallEdge_injective eA eB Z Q Delta heA heB hZ hQ
  · exact Amalgam.famHom_injective eA eB heA heB
  · exact Subtype.val_injective
  · intro b
    cases b <;> exact Subtype.val_injective
  · exact factorInclusion_reflects_range eA eB Z Q Delta hZ hQ

/-- The generating set in the large amalgam: the left copy of `Z` and the
right copy of `Q`. -/
def generatorSet : Set (Amalgam.Push eA eB) :=
  (bigInA eA eB '' (Z : Set A)) ∪ (bigInB eA eB '' (Q : Set B))

/-- The range of the small amalgam is exactly the subgroup generated by the
two matched factor subgroups. -/
theorem matchedMap_range_eq_closure
    (hZ : Z.comap eA = Delta) (hQ : Q.comap eB = Delta) :
    (matchedMap eA eB Z Q Delta hZ hQ).range =
      Subgroup.closure (generatorSet eA eB Z Q) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using PushoutI.induction_on with
    | of b g =>
        cases b with
        | false =>
            change ↥Z at g
            exact Subgroup.subset_closure
              (Or.inl ⟨(g : A), g.property, by
                exact (matchedMap_smallInZ eA eB Z Q Delta hZ hQ g).symm⟩)
        | true =>
            change ↥Q at g
            exact Subgroup.subset_closure
              (Or.inr ⟨(g : B), g.property, by
                exact (matchedMap_smallInQ eA eB Z Q Delta hZ hQ g).symm⟩)
    | base d =>
        have hfactor :
            PushoutI.base (smallEdge eA eB Z Q Delta hZ hQ) d =
              smallInZ eA eB Z Q Delta hZ hQ
                (edgeToZ eA Z Delta hZ d) :=
          (PushoutI.of_apply_eq_base
            (smallEdge eA eB Z Q Delta hZ hQ) false d).symm
        rw [hfactor]
        exact Subgroup.subset_closure
          (Or.inl ⟨eA d, (edgeToZ eA Z Delta hZ d).property,
            by
              exact (matchedMap_smallInZ eA eB Z Q Delta hZ hQ
                (edgeToZ eA Z Delta hZ d)).symm⟩)
    | mul x y hx hy =>
        rw [map_mul]
        exact Subgroup.mul_mem _ hx hy
  · refine (Subgroup.closure_le _).mpr ?_
    rintro x (⟨z, hz, rfl⟩ | ⟨q, hq, rfl⟩)
    · let zs : ↥Z := ⟨z, hz⟩
      refine ⟨smallInZ eA eB Z Q Delta hZ hQ zs, ?_⟩
      exact matchedMap_smallInZ eA eB Z Q Delta hZ hQ zs
    · let qs : ↥Q := ⟨q, hq⟩
      refine ⟨smallInQ eA eB Z Q Delta hZ hQ qs, ?_⟩
      exact matchedMap_smallInQ eA eB Z Q Delta hZ hQ qs

end MatchedSubgroupAmalgam
end Higman
end GroupApproximation
