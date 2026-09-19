import GroupApproximation.Dynamics.SubshiftCyclePeriodic
import GroupApproximation.Dynamics.ClopenCrossedProduct
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions

/-!
# Finite windows and the shift on a subshift

Tools for the subshift case of `lem:chain-core-models` (`non_mf_groups_exist.tex`, tex 1386–1400).
Let `X ⊆ A^ℤ` be closed and shift-invariant over a finite discrete alphabet `A`, and let
`T : X ≃ₜ X` act as the shift.

* `exists_radius`: a locally constant function on `X` is determined by a window `[-r, r]`
  ("choose a window determining all coefficient functions", tex 1388);
* `shiftHomeomorph hX : X ≃ₜ X`: the shift restricted to `X`, with `shiftHomeomorph_apply`;
* `zpow_apply_coord`: if `T` acts as the shift, then `(T ^ n) x` reads `x` from position `n`;
* `evalFamily T k w : ClopenCoeff T k →+* (κ → ι → k)`: evaluation of coefficients along a family
  of points `w : ι → κ → X`, the diagonal part of the finite models (tex 1395–1396).
-/

namespace GroupApproximation
namespace WordGraph

open SymbolicDynamics.FullShift

variable {A : Type*}

/-- **A window determines a locally constant function.**  On a closed set `X` of configurations
over a finite discrete alphabet, a locally constant function depends only on the coordinates in a
window `[-r, r]` (tex 1388). -/
theorem exists_radius [TopologicalSpace A] [DiscreteTopology A] [Finite A] {X : Set (ℤ → A)}
    (hXc : IsClosed X) {Y : Type*} (f : LocallyConstant ↥X Y) :
    ∃ r : ℕ, ∀ y z : ↥X, (∀ i : ℤ, |i| ≤ r → y.1 i = z.1 i) → f y = f z := by
  haveI : CompactSpace ↥X := isCompact_iff_compactSpace.mp hXc.isCompact
  have hloc : ∀ x : ↥X, ∃ I : Finset ℤ, ∀ y : ↥X, (∀ i ∈ I, y.1 i = x.1 i) → f y = f x := by
    intro x
    obtain ⟨t, ht, hts⟩ := isOpen_induced_iff.mp (f.isLocallyConstant.isOpen_fiber (f x))
    have hmem : ∀ y : ↥X, y.1 ∈ t ↔ f y = f x := fun y => Set.ext_iff.mp hts y
    obtain ⟨I, U, hU, hIU⟩ := isOpen_pi_iff.mp ht x.1 ((hmem x).mpr rfl)
    refine ⟨I, fun y hy => (hmem y).mp (hIU (Set.mem_pi.mpr fun i hi => ?_))⟩
    rw [hy i hi]
    exact (hU i hi).2
  choose J hJ using hloc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun z : ↥X => Subtype.val ⁻¹' ((J z : Set ℤ).pi fun i => {z.1 i}))
    (fun z => (isOpen_set_pi (J z).finite_toSet fun i _ => isOpen_discrete _).preimage
      continuous_subtype_val)
    (fun z _ => Set.mem_iUnion.mpr ⟨z, Set.mem_pi.mpr fun _ _ => Set.mem_singleton _⟩)
  refine ⟨(t.biUnion J).sup Int.natAbs, fun x y hxy => ?_⟩
  obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  have hxz' : ∀ i ∈ J z, x.1 i = z.1 i := hxz
  have hyz : ∀ i ∈ J z, y.1 i = z.1 i := fun i hi => by
    have h := Finset.le_sup (f := Int.natAbs) (Finset.mem_biUnion.mpr ⟨z, hz, hi⟩)
    rw [← hxz' i hi]
    exact (hxy i (abs_le.mpr ⟨by omega, by omega⟩)).symm
  exact (hJ z x hxz').trans (hJ z y hyz).symm

/-- The shift `x ↦ (i ↦ x (1 + i))` restricted to a shift-invariant set `X`. -/
def shiftHomeomorph [TopologicalSpace A] {X : Set (ℤ → A)}
    (hX : ∀ n : ℤ, Set.MapsTo (shift n) X X) : ↥X ≃ₜ ↥X where
  toFun x := ⟨shift 1 x.1, hX 1 x.2⟩
  invFun x := ⟨shift (-1) x.1, hX (-1) x.2⟩
  left_inv x := Subtype.ext <| funext fun i =>
    show x.1 (1 + (-1 + i)) = x.1 i from congrArg x.1 (add_neg_cancel_left 1 i)
  right_inv x := Subtype.ext <| funext fun i =>
    show x.1 (-1 + (1 + i)) = x.1 i from congrArg x.1 (neg_add_cancel_left 1 i)
  continuous_toFun :=
    ((continuous_shift (A := A) (1 : ℤ)).comp continuous_subtype_val).subtype_mk fun x => hX 1 x.2
  continuous_invFun :=
    ((continuous_shift (A := A) (-1 : ℤ)).comp continuous_subtype_val).subtype_mk
      fun x => hX (-1) x.2

theorem shiftHomeomorph_apply [TopologicalSpace A] {X : Set (ℤ → A)}
    (hX : ∀ n : ℤ, Set.MapsTo (shift n) X X) (x : ↥X) : (shiftHomeomorph hX x).1 = shift 1 x.1 :=
  rfl

/-- If `T` acts as the shift on `X`, then `(T ^ n) x` reads `x` from position `n`. -/
theorem zpow_apply_coord [TopologicalSpace A] {X : Set (ℤ → A)} {T : ↥X ≃ₜ ↥X}
    (hT : ∀ x : ↥X, (T x).1 = shift 1 x.1) (n : ℤ) (x : ↥X) (m : ℤ) :
    ((T ^ n) x).1 m = x.1 (n + m) := by
  have hsymm : ∀ (x : ↥X) (m : ℤ), (T.symm x).1 m = x.1 (-1 + m) := fun x m => by
    have h := congrFun (hT (T.symm x)) (-1 + m)
    rw [Homeomorph.apply_symm_apply, shift_apply] at h
    rw [h]
    exact congrArg (T.symm x).1 (add_neg_cancel_left 1 m).symm
  induction n generalizing x m with
  | zero => rw [zpow_zero, Homeomorph.one_apply, zero_add]
  | succ i ih =>
    rw [zpow_add_one, Homeomorph.mul_apply, ih, hT, shift_apply]
    exact congrArg x.1 (by ring)
  | pred i ih =>
    rw [zpow_sub_one, Homeomorph.mul_apply, ih, Homeomorph.inv_apply, hsymm]
    exact congrArg x.1 (by ring)

/-- Evaluation of coefficients along a family of points `w : ι → κ → Y`:
`a ↦ (n ↦ (s ↦ a (w s n)))`. -/
def evalFamily {Y : Type*} [TopologicalSpace Y] (T : Y ≃ₜ Y) (k : Type*) [Ring k] {ι κ : Type*}
    (w : ι → κ → Y) : ClopenCoeff T k →+* (κ → ι → k) where
  toFun a n s := (ClopenCoeff.of T k).symm a (w s n)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem evalFamily_apply {Y : Type*} [TopologicalSpace Y] (T : Y ≃ₜ Y) (k : Type*) [Ring k]
    {ι κ : Type*} (w : ι → κ → Y) (a : ClopenCoeff T k) (n : κ) (s : ι) :
    evalFamily T k w a n s = (ClopenCoeff.of T k).symm a (w s n) :=
  rfl

end WordGraph
end GroupApproximation

#audit_axioms GroupApproximation.WordGraph.exists_radius
#audit_axioms GroupApproximation.WordGraph.shiftHomeomorph_apply
#audit_axioms GroupApproximation.WordGraph.zpow_apply_coord
#audit_axioms GroupApproximation.WordGraph.evalFamily_apply
