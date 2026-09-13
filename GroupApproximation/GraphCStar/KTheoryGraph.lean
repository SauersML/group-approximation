import GroupApproximation.GraphCStar.KTheoryIntegers
import GroupApproximation.GraphCStar.LoopGraph
import GroupApproximation.GraphCStar.Universal

/-!
# The unit classes of `C*(E(1,2))` and `C*(E(1,1,2))` in `K₀`

This file connects the Cuntz–Krieger families of `GraphCStar.Graph` to the cokernels of
`KTheoryRelations` and `KTheoryIntegers`.

* `CKFamily.toCuntzKriegerFamily`: a unital Cuntz–Krieger `G`-family, viewed as a family in the
  sense of `KTheoryRelations`.
* `exists_loopGraph_src_eq`: every vertex of `E(u)` emits its loop, so `E(u)` has no sinks.
* `vertexMatrix_loopGraph`: the vertex matrix of `E(u)` is `KirchbergLoops.graphMatrix u`.
* `CKFamily.loopCokernelToKZero`: given a Cuntz–Krieger `E(u)`-family in `R`, the homomorphism
  `coker(1 - M(u)ᵀ) → K₀(R)` with `δ_v ↦ [p_v]`. `loopCokernelToKZero_one` shows that it sends the
  class of `(1, …, 1)` to `[1]`.
* `kZeroHomB`, `kZeroHomB_one`: a homomorphism `ℤ → K₀(C*(E(1,2)))` with `1 ↦ [1]`.
* `kZeroHomC`, `kZeroHomC_one`: a homomorphism `ℤ² → K₀(C*(E(1,1,2)))` with `(1,0) ↦ [1]`.

Not proved here: whether these homomorphisms are injective or surjective, anything about `K₁`,
and anything about `C*(E(1,2)) ⊗ C*(E(1,2))`.
-/

universe u

namespace GroupApproximation
namespace GraphCStar

open KirchbergLoops (graphMatrix)

section Bridge

variable {V E : Type u} [Fintype V] [Fintype E] [DecidableEq V] {G : Graph V E}
  {R : Type*} [Ring R] [StarRing R]

/-- A unital Cuntz–Krieger `G`-family, as a family in the sense of `KTheoryRelations`. -/
def CKFamily.toCuntzKriegerFamily (F : CKFamily G R) : CuntzKriegerFamily G.src G.rng R where
  p := F.p
  S := F.s
  isStarProjection_p v := ⟨F.p_mul_p_self v, F.star_p v⟩
  p_mul_p_of_ne := F.p_mul_p_of_ne
  star_S_mul_S_self := F.star_s_mul_s_self
  star_S_mul_S_of_ne := F.star_s_mul_s_of_ne
  S_mul_p := F.s_mul_p_rng
  sum_S_mul_star_S := F.sum_s_mul_star_s

@[simp]
theorem CKFamily.toCuntzKriegerFamily_p (F : CKFamily G R) (v : V) :
    F.toCuntzKriegerFamily.p v = F.p v :=
  rfl

end Bridge

section LoopGraph

variable {n : ℕ} (u : Fin n → ℕ)

/-- Every vertex `v` of `E(u)` emits its loop `Sum.inl v`, so `E(u)` has no sinks. -/
theorem exists_loopGraph_src_eq (v : Fin n) : ∃ e, (loopGraph u).src e = v :=
  ⟨.inl v, rfl⟩

/-- **The vertex matrix of `E(u)` is `M(u) = 1 + u 1ᵀ`.** -/
theorem vertexMatrix_loopGraph :
    vertexMatrix (loopGraph u).src (loopGraph u).rng = graphMatrix fun j => (u j : ℤ) := by
  ext v w
  have hM : (graphMatrix fun j => (u j : ℤ)) v w = (if v = w then 1 else 0) + (u w : ℤ) := rfl
  rw [hM, vertexMatrix_apply, ← Finset.filter_filter, Finset.natCast_card_filter, sum_filter_src,
    Fintype.sum_sigma, Finset.sum_eq_single w]
  · show (if v = w then (1 : ℤ) else 0) + ∑ _k : Fin (u w), (if w = w then (1 : ℤ) else 0) = _
    rw [if_pos (rfl : w = w), Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_one]
  · intro b _ hb
    exact Finset.sum_eq_zero fun _ _ => if_neg hb
  · intro hw
    exact absurd (Finset.mem_univ w) hw

/-- The image of `1 - Aᵀ` for the vertex matrix `A` of `E(u)` is the image of `1 - M(w)ᵀ`, whenever
`w` is `u` cast to `ℤ`. -/
theorem range_relationHom_loopGraph {w : Fin n → ℤ} (hw : ∀ j, (u j : ℤ) = w j) :
    (relationHom (vertexMatrix (loopGraph u).src (loopGraph u).rng)).range =
      (relationHom (graphMatrix w)).range :=
  congrArg (fun M => (relationHom M).range)
    ((vertexMatrix_loopGraph u).trans (congrArg graphMatrix (funext hw)))

namespace CKFamily

variable {u} {R : Type*} [Ring R] [StarRing R] (F : CKFamily (loopGraph u) R)

/-- **The homomorphism `coker(1 - M(u)ᵀ) → K₀(R)`, `δ_v ↦ [p_v]`**, for a Cuntz–Krieger
`E(u)`-family `F` in `R`. It is not claimed to be injective or surjective. -/
noncomputable def loopCokernelToKZero {w : Fin n → ℤ} (hw : ∀ j, (u j : ℤ) = w j) :
    cokernel (graphMatrix w) →+ KTheory.KZero R :=
  (F.toCuntzKriegerFamily.cokernelToKZero (exists_loopGraph_src_eq u)).comp
    (QuotientAddGroup.quotientAddEquivOfEq (range_relationHom_loopGraph u hw).symm).toAddMonoidHom

theorem loopCokernelToKZero_mk {w : Fin n → ℤ} (hw : ∀ j, (u j : ℤ) = w j) (x : Fin n → ℤ) :
    F.loopCokernelToKZero hw (QuotientAddGroup.mk x) = F.toCuntzKriegerFamily.vertexClass x :=
  rfl

/-- **The class of `(1, …, 1)` maps to `[1]`.** -/
theorem loopCokernelToKZero_one {w : Fin n → ℤ} (hw : ∀ j, (u j : ℤ) = w j) :
    F.loopCokernelToKZero hw (QuotientAddGroup.mk fun _ => 1) = projClass (1 : R) :=
  (F.loopCokernelToKZero_mk hw _).trans
    (F.toCuntzKriegerFamily.vertexClass_const_one.trans
      (F.toCuntzKriegerFamily.projClass_one F.sum_p).symm)

end CKFamily

end LoopGraph

section B

theorem natCast_B (j : Fin 2) : ((![1, 2] : Fin 2 → ℕ) j : ℤ) = (![1, 2] : Fin 2 → ℤ) j := by
  fin_cases j <;> rfl

/-- **A homomorphism `ℤ → K₀(C*(E(1,2)))` with `1 ↦ [1]`**: `cokernelEquivB⁻¹` followed by
`loopCokernelToKZero` for the generating family. It is not claimed to be an isomorphism. -/
noncomputable def kZeroHomB : ℤ →+ KTheory.KZero (GraphCStarAlgebra (loopGraph ![1, 2])) :=
  ((ckFamily (loopGraph ![1, 2])).loopCokernelToKZero natCast_B).comp
    cokernelEquivB.symm.toAddMonoidHom

theorem kZeroHomB_one : kZeroHomB 1 = projClass (1 : GraphCStarAlgebra (loopGraph ![1, 2])) := by
  have h : cokernelEquivB.symm 1 = QuotientAddGroup.mk fun _ => 1 :=
    cokernelEquivB.symm_apply_eq.2 cokernelEquivB_one.symm
  show (ckFamily (loopGraph ![1, 2])).loopCokernelToKZero natCast_B (cokernelEquivB.symm 1) = _
  rw [h]
  exact (ckFamily (loopGraph ![1, 2])).loopCokernelToKZero_one natCast_B

end B

section C

theorem natCast_C (j : Fin 3) :
    ((![1, 1, 2] : Fin 3 → ℕ) j : ℤ) = (![1, 1, 2] : Fin 3 → ℤ) j := by
  fin_cases j <;> rfl

/-- **A homomorphism `ℤ² → K₀(C*(E(1,1,2)))` with `(1,0) ↦ [1]`**: `cokernelEquivC⁻¹` followed by
`loopCokernelToKZero` for the generating family. It is not claimed to be an isomorphism. -/
noncomputable def kZeroHomC :
    (Fin 2 → ℤ) →+ KTheory.KZero (GraphCStarAlgebra (loopGraph ![1, 1, 2])) :=
  ((ckFamily (loopGraph ![1, 1, 2])).loopCokernelToKZero natCast_C).comp
    cokernelEquivC.symm.toAddMonoidHom

theorem kZeroHomC_one :
    kZeroHomC ![1, 0] = projClass (1 : GraphCStarAlgebra (loopGraph ![1, 1, 2])) := by
  have h : cokernelEquivC.symm ![1, 0] = QuotientAddGroup.mk fun _ => 1 :=
    cokernelEquivC.symm_apply_eq.2 cokernelEquivC_one.symm
  show (ckFamily (loopGraph ![1, 1, 2])).loopCokernelToKZero natCast_C
    (cokernelEquivC.symm ![1, 0]) = _
  rw [h]
  exact (ckFamily (loopGraph ![1, 1, 2])).loopCokernelToKZero_one natCast_C

end C

end GraphCStar
end GroupApproximation
