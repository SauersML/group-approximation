import Mathlib.RingTheory.Valuation.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Mul
import GroupApproximation.Meta.AxiomGuard

/-!
# The distance function of the Bruhat--Tits tree of `GL_2` over a valued field

The tree step behind the rank-two remark after `prop:torsion-defect-ring` of
`non_mf_groups_exist.tex` (tex lines 1146--1150): `GL_2` over a field with a
discrete valuation acts on the Bruhat--Tits tree, and the displacement of the
standard vertex is computed from the valuations of the matrix entries.

Let `v : AddValuation K (WithTop ℤ)` be a discrete valuation on a field `K` and
`g ∈ GL_2(K)`.  With `μ(g)` the least valuation of a nonzero entry of `g`, put

`n(g) = v(det g) − 2 μ(g)`.

This module proves, with no tree in sight:

* `0 ≤ n(g)`, `n(g h) ≤ n(g) + n(h)`, `n(g⁻¹) = n(g)`, `n(1) = 0`;
* `S = {g : n(g) = 0}` is a subgroup (it is `K^× GL_2(O)`), and `n` is
  bi-invariant under `S`;
* `n(g⁻¹ h) = 1` forces `n(h) = n(g) ± 1` (`n` changes parity with `v(det)`).

So `(g S, h S) ↦ n(g⁻¹ h)` is a well-defined distance-like function on the coset
space, the graph with edges `n = 1` has a level function changing by exactly one
along edges, and left multiplication acts by graph automorphisms.
-/

namespace GroupApproximation
namespace ValuedMatrixTwo

open Matrix

universe u

variable {K : Type u} [Field K] (v : AddValuation K (WithTop ℤ))

/-! ## The integer valuation of a nonzero element -/

theorem exists_eq_coe {x : K} (hx : x ≠ 0) : ∃ k : ℤ, v x = (k : WithTop ℤ) := by
  have h : v x ≠ ⊤ := (AddValuation.ne_top_iff v).mpr hx
  induction hvx : v x using WithTop.recTopCoe with
  | top => exact absurd hvx h
  | coe k => exact ⟨k, rfl⟩

/-- The valuation of a nonzero element as an integer (junk value `0` at `0`). -/
noncomputable def vz (x : K) : ℤ :=
  if hx : x = 0 then 0 else Classical.choose (exists_eq_coe v hx)

theorem coe_vz {x : K} (hx : x ≠ 0) : ((vz v x : ℤ) : WithTop ℤ) = v x := by
  rw [vz, dif_neg hx]
  exact (Classical.choose_spec (exists_eq_coe v hx)).symm

theorem vz_mul {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) : vz v (x * y) = vz v x + vz v y := by
  have h := v.map_mul x y
  rw [← coe_vz v hx, ← coe_vz v hy, ← coe_vz v (mul_ne_zero hx hy)] at h
  exact_mod_cast h

theorem vz_one : vz v 1 = 0 := by
  have h := v.map_one
  rw [← coe_vz v one_ne_zero] at h
  exact_mod_cast h

theorem vz_neg {x : K} (hx : x ≠ 0) : vz v (-x) = vz v x := by
  have h := v.map_neg x
  rw [← coe_vz v hx, ← coe_vz v (neg_ne_zero.mpr hx)] at h
  exact_mod_cast h

theorem vz_inv {x : K} (hx : x ≠ 0) : vz v x⁻¹ = -vz v x := by
  have h := vz_mul v (inv_ne_zero hx) hx
  rw [inv_mul_cancel₀ hx, vz_one] at h
  omega

/-- The ultrametric inequality, with zero summands ignored. -/
theorem le_vz_add {k : ℤ} {x y : K} (hxy : x + y ≠ 0) (hx : x ≠ 0 → k ≤ vz v x)
    (hy : y ≠ 0 → k ≤ vz v y) : k ≤ vz v (x + y) := by
  by_cases hx0 : x = 0
  · subst hx0
    rw [zero_add] at hxy ⊢
    exact hy hxy
  by_cases hy0 : y = 0
  · subst hy0
    rw [add_zero] at hxy ⊢
    exact hx hx0
  have h := v.map_add x y
  rw [← coe_vz v hx0, ← coe_vz v hy0, ← coe_vz v hxy] at h
  have h1 : ((k : ℤ) : WithTop ℤ) ≤ min ((vz v x : ℤ) : WithTop ℤ) ((vz v y : ℤ) : WithTop ℤ) :=
    le_min (by exact_mod_cast hx hx0) (by exact_mod_cast hy hy0)
  exact_mod_cast h1.trans h

/-! ## Lower bounds on the entries of a `2 × 2` matrix -/

/-- Every nonzero entry of `g` has valuation at least `k`. -/
def EntriesGe (g : Matrix (Fin 2) (Fin 2) K) (k : ℤ) : Prop :=
  ∀ i j, g i j ≠ 0 → k ≤ vz v (g i j)

variable {v}

theorem EntriesGe.mono {g : Matrix (Fin 2) (Fin 2) K} {a b : ℤ} (hg : EntriesGe v g a)
    (hab : b ≤ a) : EntriesGe v g b :=
  fun i j hij ↦ hab.trans (hg i j hij)

theorem EntriesGe.mul {g h : Matrix (Fin 2) (Fin 2) K} {a b : ℤ} (hg : EntriesGe v g a)
    (hh : EntriesGe v h b) : EntriesGe v (g * h) (a + b) := by
  intro i j hij
  rw [Matrix.mul_apply, Fin.sum_univ_two] at hij ⊢
  refine le_vz_add v hij (fun h0 ↦ ?_) (fun h1 ↦ ?_)
  · rw [vz_mul v (left_ne_zero_of_mul h0) (right_ne_zero_of_mul h0)]
    exact add_le_add (hg i 0 (left_ne_zero_of_mul h0)) (hh 0 j (right_ne_zero_of_mul h0))
  · rw [vz_mul v (left_ne_zero_of_mul h1) (right_ne_zero_of_mul h1)]
    exact add_le_add (hg i 1 (left_ne_zero_of_mul h1)) (hh 1 j (right_ne_zero_of_mul h1))

theorem EntriesGe.two_mul_le_vz_det {g : Matrix (Fin 2) (Fin 2) K} {k : ℤ} (hg : EntriesGe v g k)
    (hdet : g.det ≠ 0) : 2 * k ≤ vz v g.det := by
  rw [Matrix.det_fin_two, sub_eq_add_neg] at hdet ⊢
  refine le_vz_add v hdet (fun h0 ↦ ?_) (fun h1 ↦ ?_)
  · rw [vz_mul v (left_ne_zero_of_mul h0) (right_ne_zero_of_mul h0)]
    have h00 := hg 0 0 (left_ne_zero_of_mul h0)
    have h11 := hg 1 1 (right_ne_zero_of_mul h0)
    omega
  · have hm : g 0 1 * g 1 0 ≠ 0 := neg_ne_zero.mp h1
    rw [vz_neg v hm, vz_mul v (left_ne_zero_of_mul hm) (right_ne_zero_of_mul hm)]
    have h01 := hg 0 1 (left_ne_zero_of_mul hm)
    have h10 := hg 1 0 (right_ne_zero_of_mul hm)
    omega

theorem EntriesGe.smul {g : Matrix (Fin 2) (Fin 2) K} {k : ℤ} (hg : EntriesGe v g k) {c : K}
    (hc : c ≠ 0) : EntriesGe v (c • g) (vz v c + k) := by
  intro i j hij
  rw [Matrix.smul_apply, smul_eq_mul] at hij ⊢
  rw [vz_mul v hc (right_ne_zero_of_mul hij)]
  have := hg i j (right_ne_zero_of_mul hij)
  omega

theorem EntriesGe.adjugate {g : Matrix (Fin 2) (Fin 2) K} {k : ℤ} (hg : EntriesGe v g k) :
    EntriesGe v g.adjugate k := by
  intro i j hij
  rw [Matrix.adjugate_fin_two] at hij ⊢
  fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · exact hg 1 1 hij
  · rw [vz_neg v hij]
    exact hg 0 1 hij
  · rw [vz_neg v hij]
    exact hg 1 0 hij
  · exact hg 0 0 hij

theorem entriesGe_one : EntriesGe v (1 : Matrix (Fin 2) (Fin 2) K) 0 := by
  intro i j hij
  by_cases h : i = j
  · subst h
    rw [Matrix.one_apply_eq, vz_one]
  · exact absurd (Matrix.one_apply_ne h) hij

/-! ## The invariant `n(g) = v(det g) − 2 μ(g)` on `GL_2(K)` -/

variable (v)

theorem det_ne_zero (g : GL (Fin 2) K) : (g : Matrix (Fin 2) (Fin 2) K).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero

theorem exists_entry_ne_zero (g : GL (Fin 2) K) : ∃ p : Fin 2 × Fin 2,
    (g : Matrix (Fin 2) (Fin 2) K) p.1 p.2 ≠ 0 := by
  by_contra h
  push Not at h
  apply det_ne_zero g
  rw [Matrix.det_fin_two, h (0, 0), h (0, 1), h (1, 0), h (1, 1)]
  ring

/-- The valuations of the nonzero entries of `g`. -/
noncomputable def entryVals (g : GL (Fin 2) K) : Finset ℤ :=
  (Finset.univ.filter fun p : Fin 2 × Fin 2 ↦ (g : Matrix (Fin 2) (Fin 2) K) p.1 p.2 ≠ 0).image
    fun p ↦ vz v ((g : Matrix (Fin 2) (Fin 2) K) p.1 p.2)

theorem entryVals_nonempty (g : GL (Fin 2) K) : (entryVals v g).Nonempty := by
  obtain ⟨p, hp⟩ := exists_entry_ne_zero g
  exact ⟨_, Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp⟩, rfl⟩⟩

/-- `μ(g)`: the least valuation of a nonzero entry. -/
noncomputable def entryMin (g : GL (Fin 2) K) : ℤ :=
  (entryVals v g).min' (entryVals_nonempty v g)

theorem entriesGe_entryMin (g : GL (Fin 2) K) :
    EntriesGe v (g : Matrix (Fin 2) (Fin 2) K) (entryMin v g) := by
  intro i j hij
  exact Finset.min'_le _ _
    (Finset.mem_image.mpr ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩, rfl⟩)

theorem le_entryMin {g : GL (Fin 2) K} {k : ℤ} (hg : EntriesGe v (g : Matrix (Fin 2) (Fin 2) K) k) :
    k ≤ entryMin v g := by
  obtain ⟨p, hp, hpv⟩ := Finset.mem_image.mp (Finset.min'_mem (entryVals v g) (entryVals_nonempty v g))
  rw [entryMin, ← hpv]
  exact hg p.1 p.2 (Finset.mem_filter.mp hp).2

/-- **The Bruhat--Tits displacement** `n(g) = v(det g) − 2 μ(g)`. -/
noncomputable def dispInt (g : GL (Fin 2) K) : ℤ :=
  vz v (g : Matrix (Fin 2) (Fin 2) K).det - 2 * entryMin v g

theorem dispInt_nonneg (g : GL (Fin 2) K) : 0 ≤ dispInt v g := by
  have := (entriesGe_entryMin v g).two_mul_le_vz_det (det_ne_zero g)
  unfold dispInt
  omega

theorem vz_det_mul (g h : GL (Fin 2) K) :
    vz v ((g * h : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det =
      vz v (g : Matrix (Fin 2) (Fin 2) K).det + vz v (h : Matrix (Fin 2) (Fin 2) K).det := by
  rw [Units.val_mul, Matrix.det_mul, vz_mul v (det_ne_zero g) (det_ne_zero h)]

theorem dispInt_mul_le (g h : GL (Fin 2) K) : dispInt v (g * h) ≤ dispInt v g + dispInt v h := by
  have hmin : entryMin v g + entryMin v h ≤ entryMin v (g * h) := by
    refine le_entryMin v ?_
    rw [Units.val_mul]
    exact (entriesGe_entryMin v g).mul (entriesGe_entryMin v h)
  unfold dispInt
  rw [vz_det_mul]
  omega

theorem vz_det_inv (g : GL (Fin 2) K) :
    vz v ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det =
      -vz v (g : Matrix (Fin 2) (Fin 2) K).det := by
  have h := vz_det_mul v g⁻¹ g
  rw [inv_mul_cancel, Units.val_one, Matrix.det_one, vz_one] at h
  omega

theorem val_inv_eq (g : GL (Fin 2) K) :
    ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      ((g : Matrix (Fin 2) (Fin 2) K).det)⁻¹ • (g : Matrix (Fin 2) (Fin 2) K).adjugate := by
  rw [Matrix.coe_units_inv]
  refine Matrix.inv_eq_left_inv ?_
  rw [Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, inv_mul_cancel₀ (det_ne_zero g), one_smul]

theorem dispInt_inv_le (g : GL (Fin 2) K) : dispInt v g⁻¹ ≤ dispInt v g := by
  have hmin : -vz v (g : Matrix (Fin 2) (Fin 2) K).det + entryMin v g ≤ entryMin v g⁻¹ := by
    refine le_entryMin v ?_
    rw [val_inv_eq, ← vz_inv v (det_ne_zero g)]
    exact (entriesGe_entryMin v g).adjugate.smul (inv_ne_zero (det_ne_zero g))
  unfold dispInt
  rw [vz_det_inv]
  omega

theorem dispInt_inv (g : GL (Fin 2) K) : dispInt v g⁻¹ = dispInt v g := by
  refine le_antisymm (dispInt_inv_le v g) ?_
  have h := dispInt_inv_le v g⁻¹
  rwa [inv_inv] at h

theorem dispInt_one : dispInt v (1 : GL (Fin 2) K) = 0 := by
  have hmin : 0 ≤ entryMin v (1 : GL (Fin 2) K) := le_entryMin v (by
    rw [Units.val_one]
    exact entriesGe_one)
  have hnn := dispInt_nonneg v (1 : GL (Fin 2) K)
  unfold dispInt at hnn ⊢
  rw [Units.val_one, Matrix.det_one, vz_one] at hnn ⊢
  omega

/-! ## The stabilizer `S = K^× GL_2(O)` -/

/-- The stabilizer of the standard vertex: `n(g) = 0`. -/
def stab : Subgroup (GL (Fin 2) K) where
  carrier := {g | dispInt v g = 0}
  one_mem' := dispInt_one v
  mul_mem' := by
    intro g h hg hh
    have h1 := dispInt_mul_le v g h
    have h2 := dispInt_nonneg v (g * h)
    simp only [Set.mem_setOf_eq] at hg hh ⊢
    omega
  inv_mem' := by
    intro g hg
    simp only [Set.mem_setOf_eq] at hg ⊢
    rw [dispInt_inv, hg]

theorem mem_stab {g : GL (Fin 2) K} : g ∈ stab v ↔ dispInt v g = 0 := Iff.rfl

theorem dispInt_mul_stab {g s : GL (Fin 2) K} (hs : s ∈ stab v) : dispInt v (g * s) = dispInt v g := by
  have h1 := dispInt_mul_le v g s
  have h2 := dispInt_mul_le v (g * s) s⁻¹
  rw [mul_inv_cancel_right, dispInt_inv] at h2
  rw [mem_stab] at hs
  omega

theorem dispInt_stab_mul {g s : GL (Fin 2) K} (hs : s ∈ stab v) : dispInt v (s * g) = dispInt v g := by
  rw [← dispInt_inv v (s * g), mul_inv_rev, dispInt_mul_stab v ((stab v).inv_mem hs), dispInt_inv]

/-- Adjacent cosets have levels differing by exactly one. -/
theorem dispInt_adj {g h : GL (Fin 2) K} (hgh : dispInt v (g⁻¹ * h) = 1) :
    dispInt v h = dispInt v g + 1 ∨ dispInt v g = dispInt v h + 1 := by
  have t1 := dispInt_mul_le v g (g⁻¹ * h)
  rw [mul_inv_cancel_left] at t1
  have t2 := dispInt_mul_le v h (g⁻¹ * h)⁻¹
  rw [mul_inv_rev, inv_inv, mul_inv_cancel_left, dispInt_inv] at t2
  have hdet : vz v (((g⁻¹ * h : GL (Fin 2) K)) : Matrix (Fin 2) (Fin 2) K).det =
      vz v (h : Matrix (Fin 2) (Fin 2) K).det - vz v (g : Matrix (Fin 2) (Fin 2) K).det := by
    rw [vz_det_mul, vz_det_inv]
    ring
  unfold dispInt at hgh t1 t2 ⊢
  rw [hdet] at hgh
  omega

end ValuedMatrixTwo
end GroupApproximation

#audit_axioms GroupApproximation.ValuedMatrixTwo.dispInt_mul_le
#audit_axioms GroupApproximation.ValuedMatrixTwo.dispInt_adj
