import GroupApproximation.GroupTheory.HNNBrittonPinch
import GroupApproximation.Sofic.FreeGroupResiduallyFinite

/-!
# A free-label permutation action for an HNN extension with finite base

This is the algebraic engine for a literature-free finite model of the
twisted rope edge.  For an HNN extension of a finite group `G` along
isomorphic subgroups `A` and `B`, choose right-coset transversals for the two
edge groups.  The edge isomorphism and a bijection of the two transversal
sets give an equivariant permutation `V` of `G`.

The stable letter acts on

`G × FreeGroup (right transversal of A)`

by `V` on the first coordinate and by prepending the free generator labelled
by the current `A`-coset on the second.  The label is unchanged by left
multiplication from `A`, so this permutation intertwines the two regular edge
actions exactly.  Consequently it gives an honest action of the HNN
extension.  The next file will prove, directly from Britton reducedness, that
this action is faithful and then push each finite set of nontrivial free
labels through the already formalized residual finiteness of free groups.
-/

namespace GroupApproximation
namespace FiniteHNNFreeLabelAction

noncomputable section

universe u

variable {G : Type u} [Group G] [Fintype G]
variable {A B : Subgroup G} (phi : A ≃* B)

open HNNExtension

noncomputable local instance subgroupFintype (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H

noncomputable local instance setSubtypeFintype (S : Set G) : Fintype S :=
  Fintype.ofFinite S

/-- Passing between the subtype attached to a subgroup and the subtype of its
underlying set changes no data. -/
def subgroupSetEquiv (H : Subgroup G) : ↥(H : Set G) ≃ H where
  toFun x := ⟨x, x.property⟩
  invFun x := ⟨x, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The two transversal sets in a normal-form transversal pair have the same
finite cardinality when their subgroups are isomorphic. -/
theorem transversal_card_eq
    (phi : A ≃* B)
    (d : HNNExtension.NormalWord.TransversalPair G A B) :
    Fintype.card ↥(d.set (1 : ℤˣ)) =
      Fintype.card ↥(d.set (-1 : ℤˣ)) := by
  have hA : Fintype.card G = Fintype.card A *
      Fintype.card ↥(d.set (1 : ℤˣ)) := by
    rw [Fintype.card_congr (d.compl (1 : ℤˣ)).equiv]
    rw [Fintype.card_prod, HNNExtension.toSubgroup_one,
      Fintype.card_congr (subgroupSetEquiv A)]
  have hB : Fintype.card G = Fintype.card B *
      Fintype.card ↥(d.set (-1 : ℤˣ)) := by
    rw [Fintype.card_congr (d.compl (-1 : ℤˣ)).equiv]
    rw [Fintype.card_prod, HNNExtension.toSubgroup_neg_one,
      Fintype.card_congr (subgroupSetEquiv B)]
  have hAB : Fintype.card A = Fintype.card B :=
    Fintype.card_congr phi
  have hpos : 0 < Fintype.card A := Fintype.card_pos_iff.mpr ⟨1⟩
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc
    Fintype.card A * Fintype.card ↥(d.set (1 : ℤˣ)) = Fintype.card G := hA.symm
    _ = Fintype.card B * Fintype.card ↥(d.set (-1 : ℤˣ)) := hB
    _ = Fintype.card A * Fintype.card ↥(d.set (-1 : ℤˣ)) := by rw [hAB]

/-- A chosen bijection between the two finite transversal sets. -/
def transversalEquiv
    (phi : A ≃* B)
    (d : HNNExtension.NormalWord.TransversalPair G A B) :
    ↥(d.set (1 : ℤˣ)) ≃ ↥(d.set (-1 : ℤˣ)) :=
  Fintype.equivOfCardEq (transversal_card_eq phi d)

/-- The edge isomorphism on the underlying-set subtype coordinates. -/
def edgeEquiv (phi : A ≃* B) : ↥(A : Set G) ≃ ↥(B : Set G) :=
  (subgroupSetEquiv A).trans (phi.toEquiv.trans (subgroupSetEquiv B).symm)

/-- The same edge equivalence at the exact dependent types used by the HNN
normal-form transversals. -/
def rawEdgeEquiv (phi : A ≃* B) :
    ↥(HNNExtension.toSubgroup A B (1 : ℤˣ) : Set G) ≃
      ↥(HNNExtension.toSubgroup A B (-1 : ℤˣ) : Set G) := by
  simpa only [HNNExtension.toSubgroup_one, HNNExtension.toSubgroup_neg_one] using
    edgeEquiv phi

/-- The `A`- and `B`-coset decompositions, joined by `phi` and a bijection of
transversal representatives. -/
def baseIntertwiner
    (phi : A ≃* B)
    (d : HNNExtension.NormalWord.TransversalPair G A B) : G ≃ G :=
  (d.compl (1 : ℤˣ)).equiv |>.trans
    ((Equiv.prodCongr (rawEdgeEquiv phi) (transversalEquiv phi d)).trans
      (d.compl (-1 : ℤˣ)).equiv.symm)

omit [Fintype G] in
/-- Left multiplication by `A` does not change the chosen `A`-coset
representative. -/
theorem source_transversal_mul_left
    (d : HNNExtension.NormalWord.TransversalPair G A B)
    (a : A) (g : G) :
    ((d.compl (1 : ℤˣ)).equiv ((a : G) * g)).2 =
      ((d.compl (1 : ℤˣ)).equiv g).2 := by
  rw [(d.compl (1 : ℤˣ)).equiv_mul_left]

omit [Fintype G] in
/-- Equality of the selected source transversals detects membership in the
source edge subgroup.  This is the exact positive-to-negative seam test. -/
theorem source_transversal_eq_iff
    (d : HNNExtension.NormalWord.TransversalPair G A B) (g z : G) :
    ((d.compl (1 : ℤˣ)).equiv (g * z)).2 =
        ((d.compl (1 : ℤˣ)).equiv z).2 ↔ g ∈ A := by
  rw [(d.compl (1 : ℤˣ)).equiv_snd_eq_iff_rightCosetEquivalence]
  change RightCosetEquivalence (A : Set G) (g * z) z ↔ g ∈ A
  rw [RightCosetEquivalence, rightCoset_eq_iff]
  simp

/-- The chosen permutation of the base is equivariant for the edge
isomorphism. -/
theorem baseIntertwiner_mul_left
    (d : HNNExtension.NormalWord.TransversalPair G A B)
    (a : A) (g : G) :
    baseIntertwiner phi d ((a : G) * g) =
      ((phi a : B) : G) * baseIntertwiner phi d g := by
  apply (d.compl (-1 : ℤˣ)).equiv.injective
  rw [(d.compl (-1 : ℤˣ)).equiv_mul_left]
  simp only [baseIntertwiner, Equiv.trans_apply, Equiv.prodCongr_apply,
    Equiv.apply_symm_apply]
  rw [(d.compl (1 : ℤˣ)).equiv_mul_left]
  apply Prod.ext
  · apply Subtype.ext
    let q : A := subgroupSetEquiv A ((d.compl (1 : ℤˣ)).equiv g).1
    change ((phi (a * q) : B) : G) =
      ((phi a : B) : G) * ((phi q : B) : G)
    exact congrArg Subtype.val (phi.map_mul a q)
  · rfl

/-- Inverse equivariance, used when a Britton spelling crosses the stable
edge in the negative direction. -/
theorem baseIntertwiner_symm_mul_left
    (d : HNNExtension.NormalWord.TransversalPair G A B)
    (b : B) (g : G) :
    (baseIntertwiner phi d).symm ((b : G) * g) =
      ((phi.symm b : A) : G) * (baseIntertwiner phi d).symm g := by
  apply (baseIntertwiner phi d).injective
  rw [(baseIntertwiner phi d).apply_symm_apply]
  rw [baseIntertwiner_mul_left]
  simp

/-- The free labels are the selected right-coset representatives of `A`. -/
abbrev Label
    (d : HNNExtension.NormalWord.TransversalPair G A B) :=
  ↥(d.set (1 : ℤˣ))

/-- The infinite set on which the free-label action is initially defined. -/
abbrev Space
    (d : HNNExtension.NormalWord.TransversalPair G A B) :=
  G × FreeGroup (Label d)

/-- The left regular action of the finite base, leaving free labels fixed. -/
def basePerm
    (d : HNNExtension.NormalWord.TransversalPair G A B) (g : G) :
    Equiv.Perm (Space d) :=
  Equiv.prodCongr (Equiv.mulLeft g) (Equiv.refl _)

omit [Fintype G] in
@[simp] theorem basePerm_apply
    (d : HNNExtension.NormalWord.TransversalPair G A B)
    (g x : G) (w : FreeGroup (Label d)) :
    basePerm d g (x, w) = (g * x, w) := rfl

/-- The left regular permutations form a homomorphism. -/
def basePermHom
    (d : HNNExtension.NormalWord.TransversalPair G A B) :
    G →* Equiv.Perm (Space d) where
  toFun := basePerm d
  map_one' := by
    ext x <;> simp [basePerm]
  map_mul' g h := by
    ext x <;> simp [basePerm, mul_assoc]

/-- The stable permutation.  Its free coordinate remembers the current
`A`-coset before crossing the HNN edge. -/
def stablePerm
    (phi : A ≃* B)
    (d : HNNExtension.NormalWord.TransversalPair G A B) :
    Equiv.Perm (Space d) :=
  let V := baseIntertwiner phi d
  let label : G → FreeGroup (Label d) :=
    fun x => FreeGroup.of ((d.compl (1 : ℤˣ)).equiv x).2
  { toFun := fun p => (V p.1, label p.1 * p.2)
    invFun := fun p =>
      let x := V.symm p.1
      (x, (label x)⁻¹ * p.2)
    left_inv := by
      rintro ⟨x, w⟩
      simp [V, label]
    right_inv := by
      rintro ⟨x, w⟩
      simp [V, label] }

@[simp] theorem stablePerm_apply
    (d : HNNExtension.NormalWord.TransversalPair G A B)
    (x : G) (w : FreeGroup (Label d)) :
    stablePerm phi d (x, w) =
      (baseIntertwiner phi d x,
        FreeGroup.of ((d.compl (1 : ℤˣ)).equiv x).2 * w) := rfl

/-- The inverse stable permutation removes the label selected before the
reverse crossing. -/
@[simp] theorem stablePerm_symm_apply
    (d : HNNExtension.NormalWord.TransversalPair G A B)
    (x : G) (w : FreeGroup (Label d)) :
    (stablePerm phi d).symm (x, w) =
      let y := (baseIntertwiner phi d).symm x
      (y, (FreeGroup.of ((d.compl (1 : ℤˣ)).equiv y).2)⁻¹ * w) :=
  rfl

/-- Exact covariance of the stable permutation with the two edge actions. -/
theorem stablePerm_covariance
    (d : HNNExtension.NormalWord.TransversalPair G A B) (a : A) :
    stablePerm phi d * basePerm d (a : G) =
      basePerm d ((phi a : B) : G) * stablePerm phi d := by
  ext p <;> rcases p with ⟨x, w⟩
  · exact baseIntertwiner_mul_left phi d a x
  · simp only [Equiv.Perm.mul_apply, basePerm_apply, stablePerm_apply,
      source_transversal_mul_left]

/-- The resulting honest permutation action of the HNN extension. -/
def action
    (d : HNNExtension.NormalWord.TransversalPair G A B) :
    HNNExtension G A B phi →* Equiv.Perm (Space d) :=
  HNNExtension.lift (basePermHom d) (stablePerm phi d)
    (stablePerm_covariance phi d)

@[simp] theorem action_of
    (d : HNNExtension.NormalWord.TransversalPair G A B) (g : G) :
    action phi d (HNNExtension.of g) = basePerm d g := by
  change (basePermHom d) g = basePerm d g
  rfl

@[simp] theorem action_t
    (d : HNNExtension.NormalWord.TransversalPair G A B) :
    action phi d (HNNExtension.t : HNNExtension G A B phi) =
      stablePerm phi d := by
  simp [action]

end

end FiniteHNNFreeLabelAction
end GroupApproximation
