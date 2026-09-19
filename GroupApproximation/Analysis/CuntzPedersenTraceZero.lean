import GroupApproximation.Analysis.CuntzPedersenCoronaObstruction
import GroupApproximation.Analysis.HNNTraceTracialStateContinuous

/-!
# Elementary facts about the Cuntz--Pedersen trace-zero space

This file develops the part of Cuntz--Pedersen separation that follows from
the existing Mathlib functional-analysis API.  In particular, it proves
unconditionally that finite sums of additive self-commutators are
self-adjoint and are annihilated by every tracial state, and that the same is
true after taking norm closure.

The converse separation statement is substantially stronger: it requires the
Jordan decomposition of a bounded hermitian functional on a C-star algebra,
which is not presently available in Mathlib.  Nothing in this file assumes
that theorem.
-/

namespace GroupApproximation
namespace CuntzPedersenTraceZero

open CuntzPedersenCoronaObstruction

noncomputable section

universe u

variable {A : Type u} [CStarAlgebra A]

/-- An additive self-commutator is self-adjoint. -/
theorem star_selfCommutator (z : A) :
    star (selfCommutator z) = selfCommutator z := by
  simp [selfCommutator, star_sub, star_mul]

/-- Taking the adjoint reverses an additive self-commutator. -/
theorem selfCommutator_star (z : A) :
    selfCommutator (star z) = -selfCommutator z := by
  simp [selfCommutator, star_star, neg_sub]

/-- Rescaling an input by the square root of a nonnegative real rescales its
self-commutator by that real. -/
theorem selfCommutator_sqrt_smul (r : ℝ) (hr : 0 ≤ r) (z : A) :
    selfCommutator ((Real.sqrt r : ℂ) • z) = r • selfCommutator z := by
  simp [selfCommutator, star_smul, ← mul_smul, Complex.coe_smul, smul_sub]
  rw [Real.mul_self_sqrt hr]

/-- Hence every finite sum of additive self-commutators is self-adjoint. -/
theorem isSelfAdjoint_of_isFiniteSelfCommutatorSum {x : A}
    (hx : IsFiniteSelfCommutatorSum x) : IsSelfAdjoint x := by
  obtain ⟨ell, z, rfl⟩ := hx
  rw [isSelfAdjoint_iff]
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact star_selfCommutator (z j)

/-- Zero is the empty sum of self-commutators. -/
theorem isFiniteSelfCommutatorSum_zero :
    IsFiniteSelfCommutatorSum (0 : A) := by
  refine ⟨0, Fin.elim0, ?_⟩
  simp

/-- Finite self-commutator sums are closed under addition. -/
theorem IsFiniteSelfCommutatorSum.add {x y : A}
    (hx : IsFiniteSelfCommutatorSum x) (hy : IsFiniteSelfCommutatorSum y) :
    IsFiniteSelfCommutatorSum (x + y) := by
  obtain ⟨ell, z, rfl⟩ := hx
  obtain ⟨m, w, rfl⟩ := hy
  refine ⟨ell + m, Fin.addCases z w, ?_⟩
  simp [Fin.sum_univ_add]
  abel

/-- Finite self-commutator sums are closed under negation. -/
theorem IsFiniteSelfCommutatorSum.neg {x : A}
    (hx : IsFiniteSelfCommutatorSum x) :
    IsFiniteSelfCommutatorSum (-x) := by
  obtain ⟨ell, z, rfl⟩ := hx
  refine ⟨ell, fun j ↦ star (z j), ?_⟩
  simp

/-- Finite self-commutator sums are closed under multiplication by a
nonnegative real scalar. -/
theorem IsFiniteSelfCommutatorSum.nonneg_smul {x : A}
    (hx : IsFiniteSelfCommutatorSum x) {r : ℝ} (hr : 0 ≤ r) :
    IsFiniteSelfCommutatorSum (r • x) := by
  obtain ⟨ell, z, rfl⟩ := hx
  refine ⟨ell, fun j ↦ (Real.sqrt r : ℂ) • z j, ?_⟩
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact (selfCommutator_sqrt_smul r hr (z j)).symm

/-- Finite self-commutator sums form a convex subset of the underlying real
normed space. -/
theorem convex_isFiniteSelfCommutatorSum :
    Convex ℝ {x : A | IsFiniteSelfCommutatorSum x} := by
  rw [convex_iff_add_mem]
  intro x hx y hy a b ha hb _
  exact IsFiniteSelfCommutatorSum.add
    (IsFiniteSelfCommutatorSum.nonneg_smul hx ha)
    (IsFiniteSelfCommutatorSum.nonneg_smul hy hb)

/-- Therefore the Cuntz--Pedersen trace-zero space is closed and convex. -/
theorem closed_convex_traceZeroSpace :
    IsClosed (traceZeroSpace A) ∧ Convex ℝ (traceZeroSpace A) :=
  ⟨isClosed_closure, convex_isFiniteSelfCommutatorSum.closure⟩

/-- The self-adjoint part is norm closed.  This direct formulation keeps the
result usable without choosing a bundled real self-adjoint subspace. -/
theorem isClosed_setOf_isSelfAdjoint :
    IsClosed {x : A | IsSelfAdjoint x} := by
  change IsClosed {x : A | star x = x}
  exact isClosed_eq continuous_star continuous_id

/-- The norm-closed Cuntz--Pedersen trace-zero set consists of self-adjoint
elements. -/
theorem isSelfAdjoint_of_mem_traceZeroSpace {x : A}
    (hx : x ∈ traceZeroSpace A) : IsSelfAdjoint x := by
  apply ((isClosed_setOf_isSelfAdjoint (A := A)).closure_subset_iff.mpr ?_) hx
  intro y hy
  exact isSelfAdjoint_of_isFiniteSelfCommutatorSum hy

/-- Traciality annihilates one additive self-commutator. -/
@[simp] theorem tracialState_selfCommutator (tau : TracialState A) (z : A) :
    tau (selfCommutator z) = 0 := by
  rw [selfCommutator, tau.map_sub, tau.map_mul_comm]
  exact sub_self _

/-- Traciality annihilates every finite sum of additive
self-commutators. -/
theorem tracialState_eq_zero_of_isFiniteSelfCommutatorSum
    (tau : TracialState A) {x : A} (hx : IsFiniteSelfCommutatorSum x) :
    tau x = 0 := by
  obtain ⟨ell, z, rfl⟩ := hx
  calc
    tau (∑ j, selfCommutator (z j)) =
        ∑ j, tau (selfCommutator (z j)) :=
      map_sum tau.toLinearMap (fun j ↦ selfCommutator (z j)) Finset.univ
    _ = 0 := Finset.sum_eq_zero fun j _ ↦ tracialState_selfCommutator tau (z j)

/-- Every tracial state annihilates the norm closure of finite sums of
additive self-commutators.  Continuity is not an assumption: it follows from
positivity and normalization by the repository's GNS proof. -/
theorem tracialState_eq_zero_of_mem_traceZeroSpace
    (tau : TracialState A) {x : A} (hx : x ∈ traceZeroSpace A) :
    tau x = 0 := by
  let f : A →L[ℂ] ℂ := HNNTrace.tracialStateCLM tau
  have hclosed : IsClosed {y : A | f y = 0} :=
    isClosed_singleton.preimage f.continuous
  have hsubset : {y : A | IsFiniteSelfCommutatorSum y} ⊆ {y : A | f y = 0} := by
    intro y hy
    exact tracialState_eq_zero_of_isFiniteSelfCommutatorSum tau hy
  have : x ∈ {y : A | f y = 0} :=
    (closure_minimal hsubset hclosed) hx
  exact this

/-- Detection by a tracial state is a certificate for being outside the
Cuntz--Pedersen trace-zero space. -/
theorem not_mem_traceZeroSpace_of_tracialState_ne_zero
    (tau : TracialState A) {x : A} (hx : tau x ≠ 0) :
    x ∉ traceZeroSpace A := by
  intro hmem
  exact hx (tracialState_eq_zero_of_mem_traceZeroSpace tau hmem)

end

end CuntzPedersenTraceZero
end GroupApproximation
