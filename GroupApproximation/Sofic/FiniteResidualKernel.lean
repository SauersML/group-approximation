import GroupApproximation.Sofic.HyperlinearResidualDetector
import GroupApproximation.Sofic.SoficPositiveControl
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.SemidirectProduct

/-!
# Finite normal subgroups of the sofic residual

This file proves the finite-kernel obstruction directly from the definition of
the sofic residual.  There is no external permanence theorem or classification
input: a finite conjugation target kills the residual, and an explicit finite
holomorph target detects the base of every split semidirect product.
-/

namespace GroupApproximation

universe u

variable {K F Q : Type u} [Group K] [Group F] [Group Q]

/-- A semidirect product of finite groups is finite, via its two coordinates.
The group law is irrelevant to this finiteness construction. -/
instance finiteSemidirectProduct [Finite F] [Finite Q]
    (alpha : Q →* MulAut F) : Finite (F ⋊[alpha] Q) := by
  apply Finite.of_injective (fun p : F ⋊[alpha] Q ↦ (p.left, p.right))
  intro x y hxy
  apply SemidirectProduct.ext
  · exact congrArg Prod.fst hxy
  · exact congrArg Prod.snd hxy

/-- A group with exactly two elements has no nonidentity automorphism. -/
theorem subsingleton_mulAut_of_natCard_eq_two (hcard : Nat.card F = 2) :
    Subsingleton (MulAut F) := by
  constructor
  intro a b
  ext x
  by_cases hx : x = 1
  · simp [hx]
  · let hunique := (Nat.card_eq_two_iff' (1 : F)).mp hcard
    exact hunique.unique
      ((MulEquiv.map_ne_one_iff a).mpr hx)
      ((MulEquiv.map_ne_one_iff b).mpr hx)

section NormalSubgroup

variable (N : Subgroup K) [N.Normal]

/-- Conjugation on a finite normal subgroup kills every element of the sofic
residual. -/
theorem conjNormal_eq_one_of_mem_soficResidual [Finite N]
    {x : K} (hx : x ∈ soficResidual K) :
    MulAut.conjNormal (H := N) x = 1 := by
  exact map_eq_one_of_mem_soficResidual
    (isSofic_of_finite' (MulAut N)) (MulAut.conjNormal (H := N)) hx

/-- Equivalently, the entire sofic residual lies in the kernel of the finite
conjugation action.  This is the precise algebraic meaning of saying that the
action factors through the maximal sofic image. -/
theorem soficResidual_le_conjNormal_ker [Finite N] :
    soficResidual K ≤ (MulAut.conjNormal (H := N)).ker := by
  intro x hx
  exact conjNormal_eq_one_of_mem_soficResidual N hx

/-- A finite normal subgroup contained in the sofic residual is abelian. -/
theorem finite_normal_subgroup_commute [Finite N]
    (hN : N ≤ soficResidual K) (x y : N) : Commute x y := by
  have hconjAut : MulAut.conjNormal (H := N) (x : K) = 1 :=
    conjNormal_eq_one_of_mem_soficResidual N (hN x.2)
  have hconjSubtype : MulAut.conjNormal (H := N) (x : K) y = y := by
    exact DFunLike.congr_fun hconjAut y
  have hconj : (x : K) * (y : K) * (x : K)⁻¹ = (y : K) := by
    simpa only [MulAut.conjNormal_apply] using congrArg Subtype.val hconjSubtype
  apply Subtype.ext
  change (x : K) * (y : K) = (y : K) * (x : K)
  calc
    (x : K) * (y : K) = ((x : K) * (y : K) * (x : K)⁻¹) * (x : K) := by
      group
    _ = (y : K) * (x : K) := by rw [hconj]

/-- Typeclass form of `finite_normal_subgroup_commute`. -/
theorem finite_normal_subgroup_isMulCommutative [Finite N]
    (hN : N ≤ soficResidual K) : IsMulCommutative N :=
  IsMulCommutative.of_comm fun x y ↦
    (finite_normal_subgroup_commute N hN x y).eq

/-- If a normal subgroup has no nontrivial automorphisms, it is central in the
ambient group.  This applies in particular to a subgroup of order two. -/
theorem normal_subgroup_le_center_of_subsingleton_mulAut
    [Subsingleton (MulAut N)] : N ≤ Subgroup.center K := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro k
  have hconjAut : MulAut.conjNormal (H := N) k = 1 :=
    Subsingleton.elim _ _
  have hconjSubtype : MulAut.conjNormal (H := N) k ⟨x, hx⟩ = ⟨x, hx⟩ := by
    exact DFunLike.congr_fun hconjAut ⟨x, hx⟩
  have hconj : k * x * k⁻¹ = x := by
    simpa only [MulAut.conjNormal_apply] using congrArg Subtype.val hconjSubtype
  calc
    k * x = (k * x * k⁻¹) * k := by group
    _ = x * k := by rw [hconj]

/-- In particular, every normal subgroup of order two is central.  The sofic
residual hypothesis is unnecessary for this final purely algebraic step. -/
theorem normal_subgroup_le_center_of_natCard_eq_two
    (hcard : Nat.card N = 2) : N ≤ Subgroup.center K := by
  letI : Subsingleton (MulAut N) :=
    subsingleton_mulAut_of_natCard_eq_two hcard
  exact normal_subgroup_le_center_of_subsingleton_mulAut N

end NormalSubgroup

section SplitExtensions

variable (alpha : Q →* MulAut F)

/-- The finite action image acts tautologically on the finite kernel. -/
abbrev actionRangeAction : alpha.range →* MulAut F :=
  alpha.range.subtype

/-- Every split extension with finite kernel maps to the finite holomorph
formed using the image of its action.  This map is injective on the kernel. -/
def finiteActionDetector :
    F ⋊[alpha] Q →* F ⋊[actionRangeAction alpha] alpha.range :=
  SemidirectProduct.map (MonoidHom.id F) alpha.rangeRestrict (by
    intro q
    ext f
    rfl)

@[simp] theorem finiteActionDetector_inl (f : F) :
    finiteActionDetector alpha (SemidirectProduct.inl f) =
      SemidirectProduct.inl f := by
  simp [finiteActionDetector]

/-- A nonidentity element of the finite kernel of a split extension is visible
in a finite group.  Hence it cannot lie in the full sofic residual. -/
theorem inl_not_mem_soficResidual_of_ne_one [Finite F]
    {f : F} (hf : f ≠ 1) :
    (SemidirectProduct.inl : F →* F ⋊[alpha] Q) f ∉
      soficResidual (F ⋊[alpha] Q) := by
  intro hres
  let T := F ⋊[actionRangeAction alpha] alpha.range
  have hkilled : finiteActionDetector alpha
      ((SemidirectProduct.inl : F →* F ⋊[alpha] Q) f) = 1 :=
    map_eq_one_of_mem_soficResidual
      (isSofic_of_finite' T) (finiteActionDetector alpha) hres
  apply hf
  have hleft := congrArg SemidirectProduct.left hkilled
  simpa using hleft

/-- No nontrivial finite kernel can be both the kernel of a split semidirect
product and contained in that product's sofic residual. -/
theorem not_inl_range_le_soficResidual [Finite F] [Nontrivial F] :
    ¬ SemidirectProduct.inl.range ≤ soficResidual (F ⋊[alpha] Q) := by
  intro hle
  obtain ⟨f, hf⟩ := exists_ne (1 : F)
  exact inl_not_mem_soficResidual_of_ne_one alpha hf
    (hle ⟨f, rfl⟩)

/-- Coordinate-free nonsplitting criterion.  If a proposed kernel inclusion
is carried to the canonical finite base by an isomorphism with a semidirect
product, that kernel cannot lie in the sofic residual.  Thus a nontrivial
finite normal subgroup of the residual admits no compatible splitting. -/
theorem not_kernel_range_le_soficResidual_of_split_equiv
    [Finite F] [Nontrivial F] (i : F →* K)
    (e : K ≃* (F ⋊[alpha] Q))
    (hbase : e.toMonoidHom.comp i = SemidirectProduct.inl) :
    ¬ i.range ≤ soficResidual K := by
  intro hle
  obtain ⟨f, hf⟩ := exists_ne (1 : F)
  have hres : i f ∈ soficResidual K :=
    hle ⟨f, rfl⟩
  let detector : K →* F ⋊[actionRangeAction alpha] alpha.range :=
    (finiteActionDetector alpha).comp e.toMonoidHom
  have hkilled : detector (i f) = 1 :=
    map_eq_one_of_mem_soficResidual
      (isSofic_of_finite' (F ⋊[actionRangeAction alpha] alpha.range))
      detector hres
  have heq : e (i f) =
      (SemidirectProduct.inl : F →* F ⋊[alpha] Q) f := by
    exact DFunLike.congr_fun hbase f
  have hleft := congrArg SemidirectProduct.left hkilled
  apply hf
  change ((finiteActionDetector alpha) (e (i f))).left = 1 at hleft
  rw [heq, finiteActionDetector_inl] at hleft
  simpa using hleft

end SplitExtensions

section ResidualExtension

variable (N : Subgroup K) [Finite N] [Nontrivial N]

/-- **Finite residual kernels do not split.**  If `N` is a nontrivial finite
normal subgroup contained in the sofic residual, there is no semidirect-product
isomorphism carrying the actual kernel inclusion to the canonical base
inclusion. -/
theorem finite_normal_residual_kernel_has_no_split_equiv
    (hN : N ≤ soficResidual K) (alpha : Q →* MulAut N)
    (e : K ≃* (N ⋊[alpha] Q))
    (hbase : e.toMonoidHom.comp N.subtype = SemidirectProduct.inl) : False := by
  apply not_kernel_range_le_soficResidual_of_split_equiv alpha N.subtype e hbase
  intro x hx
  obtain ⟨n, rfl⟩ := hx
  exact hN n.2

/-- An order-two finite residual kernel is central and nonsplit. -/
theorem order_two_residual_kernel_central_and_nonsplit
    [N.Normal]
    (hN : N ≤ soficResidual K) (hcard : Nat.card N = 2) :
    N ≤ Subgroup.center K ∧
      ∀ (alpha : Q →* MulAut N) (e : K ≃* (N ⋊[alpha] Q)),
        e.toMonoidHom.comp N.subtype = SemidirectProduct.inl → False := by
  constructor
  · exact normal_subgroup_le_center_of_natCard_eq_two N hcard
  · intro alpha e hbase
    exact finite_normal_residual_kernel_has_no_split_equiv N hN alpha e hbase

end ResidualExtension

end GroupApproximation
