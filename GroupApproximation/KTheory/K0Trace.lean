import GroupApproximation.KTheory.K0Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# The trace on `K₀`

For a commutative `*`-ring `R`, the trace of a projection matrix is invariant under stable
isomorphism (`tr (v^* v) = tr (v v^*)` for a rectangular `v`) and additive under block sums, so it
descends to an additive map `KZero.trace : K₀(R) →+ R` with `trace [p] = tr p` and `trace [1] = 1`.

* `Cycle.trace_eq_of_rectMvN`, `Cycle.trace_eq_of_rel`: stably isomorphic projections have equal
  traces.
* `KZero.trace`, `KZero.trace_mk`, `KZero.trace_unitClass`, `KZero.trace_zsmul_unitClass`.
* `KZero.zsmul_unitClass_injective`: in characteristic zero, `k ↦ k • [1]` is injective.
* `KZero.mem_of_forall_mk_mem`: an additive subgroup of `K₀(A)` containing the class of every
  projection is all of `K₀(A)`.
-/

namespace GroupApproximation
namespace KTheory

open scoped Matrix

/-- The trace of a block sum is the sum of the traces. -/
theorem blockSum_trace {R : Type*} [AddCommMonoid R] {m n : ℕ} (p : Matrix (Fin m) (Fin m) R)
    (q : Matrix (Fin n) (Fin n) R) : (blockSum p q).trace = p.trace + q.trace := by
  show ∑ i, blockSum p q i i = ∑ i, p i i + ∑ i, q i i
  rw [Fin.sum_univ_add]
  simp only [blockSum_apply_castAdd_castAdd, blockSum_apply_natAdd_natAdd]

namespace Cycle

variable {R : Type*} [CommSemiring R] [StarRing R]

/-- Rectangularly Murray–von Neumann equivalent projections have equal traces. -/
theorem trace_eq_of_rectMvN {x y : Cycle R} (h : RectMvN x y) : x.proj.trace = y.proj.trace := by
  obtain ⟨v, hv₁, hv₂⟩ := h
  rw [← hv₁, ← hv₂, Matrix.trace_mul_comm]

/-- Stably isomorphic projections have equal traces. -/
theorem trace_eq_of_rel {x y : Cycle R} (h : Rel x y) : x.proj.trace = y.proj.trace :=
  trace_eq_of_rectMvN (rel_iff_rectMvN.mp h)

theorem trace_proj_add (x y : Cycle R) : (x + y).proj.trace = x.proj.trace + y.proj.trace :=
  blockSum_trace x.proj y.proj

end Cycle

namespace VMonoid

variable {R : Type*} [CommSemiring R] [StarRing R]

/-- The trace on stable isomorphism classes of projections. -/
def trace : VMonoid R →+ R where
  toFun := Quotient.lift (fun x : Cycle R => x.proj.trace) fun _ _ h => Cycle.trace_eq_of_rel h
  map_zero' := by
    show Matrix.trace (0 : Matrix (Fin 0) (Fin 0) R) = 0
    simp
  map_add' a b := Quotient.inductionOn₂ a b fun x y => Cycle.trace_proj_add x y

@[simp] theorem trace_mk (x : Cycle R) : trace (mk x) = x.proj.trace := rfl

end VMonoid

namespace KZero

section Trace

variable {R : Type*} [CommRing R] [StarRing R]

/-- **The trace on `K₀`**: `trace [p] = tr p`. -/
noncomputable def trace : KZero R →+ R :=
  Algebra.GrothendieckAddGroup.lift VMonoid.trace

@[simp] theorem trace_mk (x : Cycle R) : trace (mk x) = x.proj.trace :=
  DFunLike.congr_fun (Algebra.GrothendieckAddGroup.lift.symm_apply_apply VMonoid.trace)
    (VMonoid.mk x)

theorem trace_unitClass : trace (unitClass R) = 1 := by
  show trace (mk Cycle.one) = 1
  rw [trace_mk]
  show Matrix.trace (1 : Matrix (Fin 1) (Fin 1) R) = 1
  simp

theorem trace_zsmul_unitClass (k : ℤ) : trace (k • unitClass R) = k := by
  rw [map_zsmul, trace_unitClass, Int.smul_one_eq_cast]

/-- In characteristic zero the multiples of `[1]` are pairwise distinct. -/
theorem zsmul_unitClass_injective [CharZero R] :
    Function.Injective fun k : ℤ => k • unitClass R := fun a b h =>
  Int.cast_injective (α := R) <| by
    simpa only [trace_zsmul_unitClass] using congrArg trace h

end Trace

section Generation

variable {A : Type*} [NonUnitalSemiring A] [StarRing A]

/-- An additive subgroup of `K₀(A)` containing the class of every projection is everything. -/
theorem mem_of_forall_mk_mem {S : AddSubgroup (KZero A)} (h : ∀ x : Cycle A, mk x ∈ S)
    (y : KZero A) : y ∈ S := by
  have hq : (QuotientAddGroup.mk' S : KZero A →+ KZero A ⧸ S) = 0 :=
    hom_ext fun x => (QuotientAddGroup.eq_zero_iff (N := S) (mk x)).mpr (h x)
  exact (QuotientAddGroup.eq_zero_iff (N := S) y).mp (DFunLike.congr_fun hq y)

end Generation

end KZero

end KTheory
end GroupApproximation
