import GroupApproximation.GroupTheory.FiniteHNNFreeLabelAction
import GroupApproximation.Higman.HNNCentralizer

/-!
# Free coset labels for a central HNN extension

For `CentHNN M`, one right-coset transversal for `M` serves at both signs.
The stable letter fixes the base coordinate and prepends the label of its
current right coset.  No finiteness assumption on the base group is needed.
-/

namespace GroupApproximation
namespace Higman
namespace CentralHNNFreeLabel

open HNNExtension

variable {G : Type} [Group G] (M : Subgroup G)

noncomputable section

/-- The chosen positive-sign transversal labels. -/
abbrev Label (d : HNNExtension.NormalWord.TransversalPair G M M) :=
  ↥(d.set (1 : ℤˣ))

/-- The base coordinate together with the free coset-label word. -/
abbrev Space (d : HNNExtension.NormalWord.TransversalPair G M M) :=
  G × FreeGroup (Label M d)

/-- Left translation on the base coordinate. -/
def basePerm (d : HNNExtension.NormalWord.TransversalPair G M M) (g : G) :
    Equiv.Perm (Space M d) :=
  Equiv.prodCongr (Equiv.mulLeft g) (Equiv.refl _)

@[simp] theorem basePerm_apply
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    (g x : G) (w : FreeGroup (Label M d)) :
    basePerm M d g (x, w) = (g * x, w) := rfl

@[simp] theorem basePerm_symm_apply
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    (g x : G) (w : FreeGroup (Label M d)) :
    (basePerm M d g).symm (x, w) = (g⁻¹ * x, w) := rfl

@[simp] theorem basePerm_inv_apply
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    (g x : G) (w : FreeGroup (Label M d)) :
    (basePerm M d g)⁻¹ (x, w) = (g⁻¹ * x, w) := rfl

/-- The base action as a homomorphism. -/
def basePermHom (d : HNNExtension.NormalWord.TransversalPair G M M) :
    G →* Equiv.Perm (Space M d) where
  toFun := basePerm M d
  map_one' := by ext x <;> simp [basePerm]
  map_mul' g h := by ext x <;> simp [basePerm, mul_assoc]

/-- The stable letter fixes the base coordinate and records its `M`-coset. -/
def stablePerm (d : HNNExtension.NormalWord.TransversalPair G M M) :
    Equiv.Perm (Space M d) :=
  let label : G → FreeGroup (Label M d) :=
    fun x => FreeGroup.of ((d.compl (1 : ℤˣ)).equiv x).2
  { toFun := fun p => (p.1, label p.1 * p.2)
    invFun := fun p => (p.1, (label p.1)⁻¹ * p.2)
    left_inv := by rintro ⟨x, w⟩; simp [label]
    right_inv := by rintro ⟨x, w⟩; simp [label] }

@[simp] theorem stablePerm_apply
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    (x : G) (w : FreeGroup (Label M d)) :
    stablePerm M d (x, w) =
      (x, FreeGroup.of ((d.compl (1 : ℤˣ)).equiv x).2 * w) := rfl

/-- Left multiplication by an edge element does not change the coset label. -/
theorem label_mul_left
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    (m : M) (x : G) :
    ((d.compl (1 : ℤˣ)).equiv ((m : G) * x)).2 =
      ((d.compl (1 : ℤˣ)).equiv x).2 := by
  exact FiniteHNNFreeLabelAction.source_transversal_mul_left d m x

/-- The stable permutation centralizes the copy of `M`. -/
theorem stablePerm_covariance
    (d : HNNExtension.NormalWord.TransversalPair G M M) (m : M) :
    stablePerm M d * basePerm M d (m : G) =
      basePerm M d (m : G) * stablePerm M d := by
  ext p <;> rcases p with ⟨x, w⟩
  · rfl
  · simp only [Equiv.Perm.mul_apply, basePerm_apply, stablePerm_apply,
      label_mul_left]

/-- The free-label action of the central HNN extension. -/
def action (d : HNNExtension.NormalWord.TransversalPair G M M) :
    CentHNN M →* Equiv.Perm (Space M d) :=
  HNNExtension.lift (basePermHom M d) (stablePerm M d)
    (stablePerm_covariance M d)

@[simp] theorem action_of
    (d : HNNExtension.NormalWord.TransversalPair G M M) (g : G) :
    action M d (of g) = basePerm M d g := by
  exact HNNExtension.lift_of _ _ _ _

@[simp] theorem action_t
    (d : HNNExtension.NormalWord.TransversalPair G M M) :
    action M d (t : CentHNN M) = stablePerm M d := by
  exact HNNExtension.lift_t _ _ _

/-- A chosen transversal representative reads as its own label. -/
theorem label_self
    (d : HNNExtension.NormalWord.TransversalPair G M M) (q : Label M d) :
    ((d.compl (1 : ℤˣ)).equiv (q : G)).2 = q := by
  apply Subtype.ext
  exact (d.compl (1 : ℤˣ)).equiv_snd_eq_self_iff_mem
    (Subgroup.one_mem M) |>.2 q.property

/-- The conjugate of the stable letter indexed by a coset representative. -/
def stableConj
    (d : HNNExtension.NormalWord.TransversalPair G M M) (q : Label M d) :
    CentHNN M := of (q : G)⁻¹ * t * of (q : G)

/-- A stable conjugate prepends precisely its chosen free label. -/
theorem action_stableConj_apply
    (d : HNNExtension.NormalWord.TransversalPair G M M) (q : Label M d)
    (w : FreeGroup (Label M d)) :
    action M d (stableConj M d q) ((1 : G), w) =
      (1, FreeGroup.of q * w) := by
  simp only [stableConj, map_mul, map_inv, Equiv.Perm.mul_apply, action_of,
    action_t, basePerm_apply, stablePerm_apply, mul_one, basePerm_inv_apply]
  rw [label_self]
  congr 1
  group

theorem action_stableConj_apply_one
    (d : HNNExtension.NormalWord.TransversalPair G M M) (q : Label M d) :
    action M d (stableConj M d q)
        ((1 : G), (1 : FreeGroup (Label M d))) =
      (1, FreeGroup.of q) := by
  simpa using action_stableConj_apply M d q 1

/-- The free group on coset labels maps to the corresponding stable
conjugates. -/
def stableConjLift
    (d : HNNExtension.NormalWord.TransversalPair G M M) :
    FreeGroup (Label M d) →* CentHNN M :=
  FreeGroup.lift (stableConj M d)

/-- Evaluation of a word in stable conjugates is left multiplication by the
same free word on the label coordinate. -/
theorem action_stableConjLift_apply
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    (w v : FreeGroup (Label M d)) :
    action M d (stableConjLift M d w)
        ((1 : G), v) = (1, w * v) := by
  induction w using FreeGroup.induction_on generalizing v with
  | C1 => simp
  | of q => simpa [stableConjLift] using action_stableConj_apply M d q v
  | mul x y hx hy =>
      rw [map_mul (stableConjLift M d), map_mul (action M d),
        Equiv.Perm.mul_apply, hy, hx]
      congr 1
      group
  | inv_of q hq =>
      rw [map_inv]
      apply (action M d (stableConjLift M d (FreeGroup.of q))).symm_apply_eq.mpr
      simpa [stableConjLift, mul_assoc] using
        (action_stableConj_apply M d q ((FreeGroup.of q)⁻¹ * v)).symm

/-- Evaluation at the identity reads back the same free word. -/
theorem action_stableConjLift_apply_one
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    (w : FreeGroup (Label M d)) :
    action M d (stableConjLift M d w)
        ((1 : G), (1 : FreeGroup (Label M d))) = (1, w) := by
  simpa using action_stableConjLift_apply M d w 1

/-- **Stable conjugates are freely based by right cosets of `M`.** -/
theorem stableConjLift_injective
    (d : HNNExtension.NormalWord.TransversalPair G M M) :
    Function.Injective (stableConjLift M d) := by
  intro x y hxy
  have hact := congrArg (action M d) hxy
  have hpoint := DFunLike.congr_fun hact
    ((1 : G), (1 : FreeGroup (Label M d)))
  rw [action_stableConjLift_apply_one, action_stableConjLift_apply_one] at hpoint
  exact congrArg Prod.snd hpoint

end

end CentralHNNFreeLabel
end Higman
end GroupApproximation
