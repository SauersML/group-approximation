import GroupApproximation.Algebra.FinitaryShiftWindow
import GroupApproximation.Sofic.LEF
import GroupApproximation.Meta.AxiomGuard

/-!
# `GL_fin(ℤ, F_2) ⋊ ℤ` is LEF

`non_mf_groups_exist.tex`, the remark after `cor:dynamic-rank-budget` (tex 1786–1789):

> This semidirect product is LEF: copy any finite table's finitary
> supports and the translated supports used in its products into a
> sufficiently long finite cycle, replacing the shift by cyclic translation.
> Products agree without wraparound; equal shift exponents are separated
> by their finitary parts, and different exponents by points outside
> those supports.

The model of `x = (g, n) ∈ GL_fin(ℤ, k) ⋊ ℤ` on the cycle `ℤ/N` through a window `W` is
`cycleModel N W x = (1 + copy of (g − 1)) · σ_N^n`, with `σ_N` the cyclic translation.

* `cycleModel_mul`: products agree when the window holds the table's supports and their
  translates by the table's exponents, and does not wrap around;
* `cycleModel_eq_imp`: different exponents are separated at a point outside the window, equal
  exponents by the finitary parts;
* `isLEF_finitaryShift`: `GL_fin(ℤ, k) ⋊ ℤ` is LEF for every finite nontrivial commutative ring;
* `printedFinitaryShiftLEF`: `GL_fin(ℤ, F_2) ⋊ ℤ` is LEF.
-/

namespace GroupApproximation

namespace FinitaryGL

open Finsupp
open Multiplicative (toAdd)

section Model

variable {k : Type*} [CommRing k]

/-- The finitary part `g − 1` of `g ∈ GL_fin(ℤ, k)`. -/
noncomputable abbrev deviation (g : GLfin k) : Module.End k (ℤ →₀ k) :=
  ((g : LinearMap.GeneralLinearGroup k (ℤ →₀ k)) : Module.End k (ℤ →₀ k)) - 1

theorem deviation_mul (g h : GLfin k) :
    deviation (g * h) = deviation g * deviation h + deviation g + deviation h :=
  ring_mul_sub_one (R := Module.End k (ℤ →₀ k))
    ((g : LinearMap.GeneralLinearGroup k (ℤ →₀ k)) : Module.End k (ℤ →₀ k))
    ((h : LinearMap.GeneralLinearGroup k (ℤ →₀ k)) : Module.End k (ℤ →₀ k))

theorem deviation_one : deviation (1 : GLfin k) = 0 := by
  show ((1 : LinearMap.GeneralLinearGroup k (ℤ →₀ k)) : Module.End k (ℤ →₀ k)) - 1 = 0
  rw [Units.val_one]
  exact sub_self (1 : Module.End k (ℤ →₀ k))

theorem deviation_mul_inv (g : GLfin k) :
    deviation g * deviation g⁻¹ + deviation g + deviation g⁻¹ = 0 := by
  rw [← deviation_mul, mul_inv_cancel, deviation_one]

theorem deviation_inv_mul (g : GLfin k) :
    deviation g⁻¹ * deviation g + deviation g⁻¹ + deviation g = 0 := by
  rw [← deviation_mul, inv_mul_cancel, deviation_one]

theorem deviation_shiftAction (a : Multiplicative ℤ) (h : GLfin k) :
    deviation (shiftAction k a h) =
      ((shiftGL k ^ toAdd a : LinearMap.GeneralLinearGroup k (ℤ →₀ k)) : Module.End k (ℤ →₀ k)) *
        deviation h *
          ((shiftGL k ^ (-toAdd a) : LinearMap.GeneralLinearGroup k (ℤ →₀ k)) :
            Module.End k (ℤ →₀ k)) := by
  have hxz : ((shiftGL k ^ toAdd a : LinearMap.GeneralLinearGroup k (ℤ →₀ k)) :
      Module.End k (ℤ →₀ k)) * ((shiftGL k ^ (-toAdd a) : LinearMap.GeneralLinearGroup k (ℤ →₀ k)) :
        Module.End k (ℤ →₀ k)) = 1 := by
    rw [← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one]
  show ((shiftGL k ^ toAdd a * (h : LinearMap.GeneralLinearGroup k (ℤ →₀ k)) *
      (shiftGL k ^ toAdd a)⁻¹ : LinearMap.GeneralLinearGroup k (ℤ →₀ k)) :
        Module.End k (ℤ →₀ k)) - 1 = _
  rw [← zpow_neg, Units.val_mul, Units.val_mul]
  exact ring_conj_sub_one (R := Module.End k (ℤ →₀ k)) hxz _

variable (N : ℕ)

open Classical in
/-- The copy of `g ∈ GL_fin(ℤ, k)` into `GL(k^{(ℤ/N)})` through the window `W`: `1` plus the copy
of `g − 1`, with inverse `1` plus the copy of `g⁻¹ − 1`, when `g − 1` is supported in `W` and `W`
does not wrap around; `1` otherwise. -/
noncomputable def windowUnit (W : Finset ℤ) (g : GLfin k) :
    LinearMap.GeneralLinearGroup k (ZMod N →₀ k) :=
  if h : SupportedIn k W (deviation g) ∧ Set.InjOn (Int.cast : ℤ → ZMod N) (W : Set ℤ) then
    { val := 1 + windowCopy N W (deviation g)
      inv := 1 + windowCopy N W (deviation g⁻¹)
      val_inv := by
        have hinv : SupportedIn k W (deviation g⁻¹) := supportedIn_inv h.1
        rw [one_add_windowCopy_mul N h.2 hinv, deviation_mul_inv, windowCopy_zero, add_zero]
      inv_val := by
        rw [one_add_windowCopy_mul N h.2 h.1, deviation_inv_mul, windowCopy_zero, add_zero] }
  else 1

theorem windowUnit_val {W : Finset ℤ} {g : GLfin k} (hg : SupportedIn k W (deviation g))
    (hinj : Set.InjOn (Int.cast : ℤ → ZMod N) (W : Set ℤ)) :
    ((windowUnit N W g : LinearMap.GeneralLinearGroup k (ZMod N →₀ k)) :
      Module.End k (ZMod N →₀ k)) = 1 + windowCopy N W (deviation g) := by
  rw [windowUnit, dif_pos ⟨hg, hinj⟩]

/-- The model of `(g, n) ∈ GL_fin(ℤ, k) ⋊ ℤ` on the cycle `ℤ/N`, through the window `W`. -/
noncomputable def cycleModel (W : Finset ℤ) (x : FinitaryShift k) :
    LinearMap.GeneralLinearGroup k (ZMod N →₀ k) :=
  windowUnit N W x.left * cycleShift N ^ toAdd x.right

/-- **Products agree without wraparound.** -/
theorem cycleModel_mul {W S : Finset ℤ} (hinj : Set.InjOn (Int.cast : ℤ → ZMod N) (W : Set ℤ))
    {x y : FinitaryShift k} (hx : SupportedIn k S (deviation x.left))
    (hy : SupportedIn k S (deviation y.left)) (hSW : S ⊆ W)
    (hSn : ∀ i ∈ S, i + toAdd x.right ∈ W) :
    cycleModel N W (x * y) = cycleModel N W x * cycleModel N W y := by
  have hx' : SupportedIn k W (deviation x.left) := hx.mono hSW
  have hy' : SupportedIn k W (deviation y.left) := hy.mono hSW
  have hφ : SupportedIn k W (deviation (shiftAction k x.right y.left)) := by
    rw [deviation_shiftAction]
    exact hy.conj _ hSn
  have hxy : SupportedIn k W (deviation (x * y).left) := by
    rw [SemidirectProduct.mul_left, deviation_mul]
    exact ((hx'.mul hφ).add hx').add hφ
  have hcomm : ((cycleShift N ^ toAdd x.right : LinearMap.GeneralLinearGroup k (ZMod N →₀ k)) :
      Module.End k (ZMod N →₀ k)) * (1 + windowCopy N W (deviation y.left)) =
      (1 + windowCopy N W (deviation (shiftAction k x.right y.left))) *
        ((cycleShift N ^ toAdd x.right : LinearMap.GeneralLinearGroup k (ZMod N →₀ k)) :
          Module.End k (ZMod N →₀ k)) := by
    rw [mul_add, add_mul, mul_one, one_mul, deviation_shiftAction,
      cycleShift_zpow_mul_windowCopy N hy hSW _ hSn]
  have hprod : (1 + windowCopy N W (deviation x.left)) *
      (1 + windowCopy N W (deviation (shiftAction k x.right y.left))) =
      1 + windowCopy N W (deviation (x * y).left) := by
    rw [one_add_windowCopy_mul N hinj hφ, SemidirectProduct.mul_left, deviation_mul]
  refine Units.ext ?_
  unfold cycleModel
  rw [SemidirectProduct.mul_right, toAdd_mul, zpow_add]
  simp only [Units.val_mul]
  rw [windowUnit_val N hxy hinj, windowUnit_val N hx' hinj, windowUnit_val N hy' hinj, ← hprod]
  simp only [mul_assoc]
  rw [← mul_assoc ((cycleShift N ^ toAdd x.right : LinearMap.GeneralLinearGroup k (ZMod N →₀ k)) :
    Module.End k (ZMod N →₀ k)), hcomm, mul_assoc]

theorem cycleModel_single_far {W : Finset ℤ}
    (hinj : Set.InjOn (Int.cast : ℤ → ZMod N) (W : Set ℤ)) {x : FinitaryShift k}
    (hx : SupportedIn k W (deviation x.left)) {p : ℤ}
    (hfar : ∀ j ∈ W, (j : ZMod N) ≠ (p : ZMod N) + ((toAdd x.right : ℤ) : ZMod N)) :
    ((cycleModel N W x : LinearMap.GeneralLinearGroup k (ZMod N →₀ k)) :
      Module.End k (ZMod N →₀ k)) (single (p : ZMod N) 1) =
      single ((p : ZMod N) + ((toAdd x.right : ℤ) : ZMod N)) 1 := by
  rw [cycleModel, Units.val_mul, Module.End.mul_apply, cycleShift_zpow_single,
    windowUnit_val N hx hinj, LinearMap.add_apply, Module.End.one_apply,
    windowCopy_single_eq_zero N hfar, add_zero]

/-- **Separation**: different exponents are separated at a point outside the window, equal
exponents by the finitary parts. -/
theorem cycleModel_eq_imp [Nontrivial k] {W : Finset ℤ}
    (hinj : Set.InjOn (Int.cast : ℤ → ZMod N) (W : Set ℤ)) {x y : FinitaryShift k}
    (hx : SupportedIn k W (deviation x.left)) (hy : SupportedIn k W (deviation y.left)) {p : ℤ}
    (hfarx : ∀ j ∈ W, (j : ZMod N) ≠ (p : ZMod N) + ((toAdd x.right : ℤ) : ZMod N))
    (hfary : ∀ j ∈ W, (j : ZMod N) ≠ (p : ZMod N) + ((toAdd y.right : ℤ) : ZMod N))
    (hsep : ((toAdd x.right : ℤ) : ZMod N) = ((toAdd y.right : ℤ) : ZMod N) →
      toAdd x.right = toAdd y.right)
    (h : cycleModel N W x = cycleModel N W y) : x = y := by
  have hright : x.right = y.right := by
    have hp := congrArg (fun u : LinearMap.GeneralLinearGroup k (ZMod N →₀ k) =>
      ((u : LinearMap.GeneralLinearGroup k (ZMod N →₀ k)) : Module.End k (ZMod N →₀ k))
        (single (p : ZMod N) 1)) h
    rw [cycleModel_single_far N hinj hx hfarx, cycleModel_single_far N hinj hy hfary,
      Finsupp.single_left_inj one_ne_zero, add_right_inj] at hp
    exact Multiplicative.toAdd.injective (hsep hp)
  have hw : windowUnit N W x.left = windowUnit N W y.left := by
    unfold cycleModel at h
    rw [hright] at h
    exact mul_right_cancel h
  have hcopy : windowCopy N W (deviation x.left) = windowCopy N W (deviation y.left) := by
    have hv := congrArg (fun u : LinearMap.GeneralLinearGroup k (ZMod N →₀ k) =>
      ((u : LinearMap.GeneralLinearGroup k (ZMod N →₀ k)) : Module.End k (ZMod N →₀ k))) hw
    rw [windowUnit_val N hx hinj, windowUnit_val N hy hinj] at hv
    refine LinearMap.ext fun v => ?_
    have hvv := LinearMap.congr_fun hv v
    rw [LinearMap.add_apply, LinearMap.add_apply, Module.End.one_apply] at hvv
    exact add_left_cancel hvv
  have hdev : deviation x.left = deviation y.left := by
    refine Finsupp.lhom_ext fun j a => ?_
    by_cases hj : j ∈ W
    · refine cyclePush_injOn N hinj (hx.1 _) (hy.1 _) ?_
      rw [← windowCopy_single_of_mem N hinj _ hj, ← windowCopy_single_of_mem N hinj _ hj, hcopy]
    · have hmem : single j a ∈ supported k k ((W : Set ℤ)ᶜ) :=
        single_mem_supported k a ((Set.mem_compl_iff _ _).2 fun h' => hj (Finset.mem_coe.1 h'))
      rw [hx.2 _ hmem, hy.2 _ hmem]
  exact SemidirectProduct.ext (Subtype.ext (Units.ext (sub_left_inj.1 hdev))) hright

end Model

/-- **`GL_fin(ℤ, k) ⋊ ℤ` is LEF** for every finite nontrivial commutative ring `k`, along the
printed route: the window holds the table's supports and their translates, and the cycle is
long enough that nothing wraps around and the exponents stay apart. -/
theorem isLEF_finitaryShift (k : Type) [CommRing k] [Finite k] [Nontrivial k] :
    IsLEF (FinitaryShift k) := by
  classical
  refine (isLEF_iff_textbook _).2 fun s => ?_
  choose S hS using fun g : GLfin k => (hasFiniteMatrixSupport_iff (deviation g)).1 g.2
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ x ∈ s, ∀ i ∈ S x.left, i.natAbs ≤ M :=
    ⟨s.sup fun x => (S x.left).sup Int.natAbs, fun x hx i hi =>
      (Finset.le_sup (f := Int.natAbs) hi).trans
        (Finset.le_sup (f := fun x : FinitaryShift k => (S x.left).sup Int.natAbs) hx)⟩
  obtain ⟨E, hE⟩ : ∃ E : ℕ, ∀ x ∈ s, (toAdd x.right).natAbs ≤ E :=
    ⟨s.sup fun x => (toAdd x.right).natAbs, fun x hx =>
      Finset.le_sup (f := fun x : FinitaryShift k => (toAdd x.right).natAbs) hx⟩
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = 2 * (M + E) + 2 * E + 2 := ⟨_, rfl⟩
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨W, hW⟩ : ∃ W : Finset ℤ, W = Finset.Icc (-((M + E : ℕ) : ℤ)) (M + E : ℕ) := ⟨_, rfl⟩
  have hinj : Set.InjOn (Int.cast : ℤ → ZMod N) (W : Set ℤ) := by
    rw [hW]
    exact intCast_injOn_Icc N (by omega)
  have hbound : ∀ (i : ℤ) (B : ℕ), i.natAbs ≤ B → -(B : ℤ) ≤ i ∧ i ≤ B := fun i B h => by
    rcases Int.natAbs_eq i with h' | h' <;> omega
  have hmemW : ∀ i : ℤ, -((M + E : ℕ) : ℤ) ≤ i → i ≤ (M + E : ℕ) → i ∈ W := fun i h1 h2 => by
    rw [hW, Finset.mem_Icc]
    exact ⟨h1, h2⟩
  have hsupp : ∀ x ∈ s, SupportedIn k W (deviation x.left) := fun x hx =>
    (hS x.left).mono fun i hi => by
      have := hbound i M (hM x hx i hi)
      exact hmemW i (by omega) (by omega)
  haveI : Finite (ZMod N →₀ k) := Finite.of_equiv _ Finsupp.equivFunOnFinite.symm
  haveI : Finite (Module.End k (ZMod N →₀ k)) := Finite.of_injective _ LinearMap.coe_injective
  let H : FiniteGroupModel :=
    { groupCarrier := LinearMap.GeneralLinearGroup k (ZMod N →₀ k)
      group := inferInstance
      fintype := Fintype.ofFinite _
      decidableEq := inferInstance }
  refine ⟨H, cycleModel N W, ?_, fun x hx y hy _ => ?_⟩
  · intro x hx y hy hxy
    have hx' := Finset.mem_coe.1 hx
    have hy' := Finset.mem_coe.1 hy
    have hfar : ∀ z ∈ s, ∀ j ∈ W,
        (j : ZMod N) ≠ ((((M + 2 * E + 1 : ℕ) : ℤ)) : ZMod N) + ((toAdd z.right : ℤ) : ZMod N) := by
      intro z hz j hj
      rw [hW, Finset.mem_Icc] at hj
      have hz' := hbound _ E (hE z hz)
      rw [← Int.cast_add]
      refine intCast_ne_of_ne N (by omega) ?_
      rw [abs_lt]
      constructor <;> omega
    have hsep : ((toAdd x.right : ℤ) : ZMod N) = ((toAdd y.right : ℤ) : ZMod N) →
        toAdd x.right = toAdd y.right := by
      intro hc
      by_contra hne
      have h1 := hbound _ E (hE x hx')
      have h2 := hbound _ E (hE y hy')
      refine intCast_ne_of_ne N hne ?_ hc
      rw [abs_lt]
      constructor <;> omega
    exact cycleModel_eq_imp N hinj (hsupp x hx') (hsupp y hy') (hfar x hx') (hfar y hy') hsep hxy
  · have hSW : S x.left ∪ S y.left ⊆ W := fun i hi => by
      rcases Finset.mem_union.1 hi with hi | hi
      · have := hbound i M (hM x hx i hi)
        exact hmemW i (by omega) (by omega)
      · have := hbound i M (hM y hy i hi)
        exact hmemW i (by omega) (by omega)
    have hSn : ∀ i ∈ S x.left ∪ S y.left, i + toAdd x.right ∈ W := fun i hi => by
      have hn := hbound _ E (hE x hx)
      rcases Finset.mem_union.1 hi with hi | hi
      · have := hbound i M (hM x hx i hi)
        exact hmemW _ (by omega) (by omega)
      · have := hbound i M (hM y hy i hi)
        exact hmemW _ (by omega) (by omega)
    exact cycleModel_mul N hinj ((hS x.left).mono Finset.subset_union_left)
      ((hS y.left).mono Finset.subset_union_right) hSW hSn

/-- **Printed sentence** (tex 1786–1789).

> This semidirect product is LEF: copy any finite table's finitary supports and the translated
> supports used in its products into a sufficiently long finite cycle, replacing the shift by
> cyclic translation.  Products agree without wraparound; equal shift exponents are separated by
> their finitary parts, and different exponents by points outside those supports.

`GL_fin(ℤ, F_2) ⋊ ℤ`, with `ℤ` acting by the bilateral shift, is LEF. -/
def PrintedFinitaryShiftLEF : Prop :=
  IsLEF (FinitaryShift (ZMod 2))

theorem printedFinitaryShiftLEF : PrintedFinitaryShiftLEF :=
  isLEF_finitaryShift (ZMod 2)

end FinitaryGL

end GroupApproximation

#audit_axioms GroupApproximation.FinitaryGL.cycleModel_mul
#audit_axioms GroupApproximation.FinitaryGL.cycleModel_eq_imp
#audit_axioms GroupApproximation.FinitaryGL.isLEF_finitaryShift
#audit_closed_axioms GroupApproximation.FinitaryGL.printedFinitaryShiftLEF
