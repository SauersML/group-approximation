import GroupApproximation.KTheory.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# The vertex relations in `K₀` of a Cuntz–Krieger family

Let `(V, E, s, r)` be a finite directed graph with vertex matrix
`A(v, w) = #{e | s e = v ∧ r e = w}`. For a graph with no sinks, graph-algebra K-theory gives
`K₀(C*(E)) ≅ coker(1 - Aᵀ)` on `ℤ^V`, with `[p_v] ↦ δ_v` and `[1] ↦ ∑_v δ_v`. This file proves
the algebraic half of that computation. In every `*`-ring `R` carrying a Cuntz–Krieger family of
the graph, the vertex classes in the projection-picture `K₀(R)` (`KTheory.KZero`) satisfy
`[p_v] = ∑_w A(v, w) • [p_w]`. So `δ_v ↦ [p_v]` descends to a homomorphism
`coker(1 - Aᵀ) → K₀(R)`, which sends the class of `∑_v δ_v` to `[1]` when `∑_v p_v = 1`.

The file does not construct the universal graph C*-algebra `C*(E)`, and it does not prove that this
homomorphism is an isomorphism for `R = C*(E)`. That needs the gauge-invariant uniqueness theorem
and a six-term exact sequence, and neither is formalized here. Nothing is said about `K₁`.

* `projClass`: the class in `K₀(R)` of a projection of `R`, as a `1 × 1` cycle.
* `projClass_eq_of_murrayVonNeumannEquiv`, `projClass_add`, `projClass_sum`: Murray–von Neumann
  equivalent projections have the same class, and orthogonal sums of projections add.
* `mul_eq_self_of_star_mul_self_eq`: in a C*-ring, `x* x = q` for a projection `q` gives `x q = x`,
  so the field `S_mul_p` below holds automatically there.
* `CuntzKriegerFamily`: projections `p v`, elements `S e` with `S e* S e = p (r e)`, `S e* S f = 0`
  for `e ≠ f`, `S e p (r e) = S e`, and `∑_{s e = v} S e S e* = p v` at every vertex that emits.
* `CuntzKriegerFamily.projClass_p`: `[p_v] = ∑_w A(v, w) • [p_w]` at every vertex that emits.
* `relationHom`, `cokernel`: `x ↦ (1 - Mᵀ) x` on `ℤ^V`, and its cokernel.
* `CuntzKriegerFamily.cokernelToKZero`: the descended homomorphism, with `cokernelToKZero_single`
  (`δ_v ↦ [p_v]`) and `cokernelToKZero_one` (`∑_v δ_v ↦ [1]`).
-/

namespace GroupApproximation
namespace GraphCStar

open scoped Matrix

section Projections

variable {R : Type*} [NonUnitalSemiring R] [StarRing R]

/-- A constant diagonal matrix with a projection on the diagonal is a projection. -/
theorem isStarProjection_diagonal_const {n : ℕ} {p : R} (hp : IsStarProjection p) :
    IsStarProjection (Matrix.diagonal fun _ : Fin n => p) := by
  refine ⟨?_, ?_⟩
  · show Matrix.diagonal (fun _ : Fin n => p) * Matrix.diagonal (fun _ : Fin n => p) =
      Matrix.diagonal fun _ => p
    simp only [Matrix.diagonal_mul_diagonal, hp.isIdempotentElem.eq]
  · show star (Matrix.diagonal fun _ : Fin n => p) = Matrix.diagonal fun _ => p
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    exact hp.isSelfAdjoint.star_eq

/-- **The class of a projection** `p` of `R` in `K₀(R)`: the class of the `1 × 1` cycle `(p)`.
An element that is not a projection is sent to `0`; every statement below assumes a projection. -/
noncomputable def projClass (p : R) : KTheory.KZero R := by
  classical
  exact if hp : IsStarProjection p then
    KTheory.KZero.mk ⟨1, Matrix.diagonal fun _ => p, isStarProjection_diagonal_const hp⟩ else 0

theorem projClass_eq {p : R} (hp : IsStarProjection p) :
    projClass p =
      KTheory.KZero.mk ⟨1, Matrix.diagonal fun _ => p, isStarProjection_diagonal_const hp⟩ := by
  classical
  rw [projClass, dif_pos hp]

theorem kZero_mk_eq_of_rel {x y : KTheory.Cycle R} (h : KTheory.Cycle.Rel x y) :
    KTheory.KZero.mk x = KTheory.KZero.mk y := by
  unfold KTheory.KZero.mk
  rw [KTheory.VMonoid.mk_eq_mk_of_rel h]

/-- **Murray–von Neumann equivalent projections have the same class.** -/
theorem projClass_eq_of_murrayVonNeumannEquiv {p q : R} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (h : MurrayVonNeumannEquiv p q) : projClass p = projClass q := by
  obtain ⟨x, hx₁, hx₂⟩ := h
  have hmvn : MurrayVonNeumannEquiv (Matrix.diagonal fun _ : Fin 1 => p)
      (Matrix.diagonal fun _ : Fin 1 => q) := by
    refine ⟨Matrix.diagonal fun _ => x, ?_, ?_⟩ <;>
      rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        Matrix.diagonal_mul_diagonal] <;>
      congr 1 <;> funext i
    · exact hx₁
    · exact hx₂
  rw [projClass_eq hp, projClass_eq hq]
  exact kZero_mk_eq_of_rel (KTheory.Cycle.rel_of_step (KTheory.Cycle.Step.mvn hmvn))

/-- The `2 × 2` implementer of `(p + q) ⊕ 0 ∼ p ⊕ q` for orthogonal projections `p` and `q`: it is
the block matrix with first column `(p, q)` and second column `0`. -/
theorem murrayVonNeumannEquiv_blockSum_orthogonal {p q : R} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hpq : p * q = 0) :
    MurrayVonNeumannEquiv
      (KTheory.blockSum (Matrix.diagonal fun _ : Fin 1 => p + q) (0 : Matrix (Fin 1) (Fin 1) R))
      (KTheory.blockSum (Matrix.diagonal fun _ : Fin 1 => p) (Matrix.diagonal fun _ : Fin 1 => q)) := by
  have hps : star p = p := hp.isSelfAdjoint.star_eq
  have hqs : star q = q := hq.isSelfAdjoint.star_eq
  have hpp : p * p = p := hp.isIdempotentElem.eq
  have hqq : q * q = q := hq.isIdempotentElem.eq
  have hqp : q * p = 0 := by
    have h := congrArg star hpq
    rwa [star_mul, hps, hqs, star_zero] at h
  refine ⟨Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks (Matrix.diagonal fun _ : Fin 1 => p) 0
      (Matrix.diagonal fun _ : Fin 1 => q) 0), ?_, ?_⟩ <;>
    simp only [KTheory.blockSum, Matrix.reindex_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_conjTranspose,
      Matrix.fromBlocks_multiply, Matrix.diagonal_conjTranspose, Matrix.conjTranspose_zero,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_zero, Matrix.mul_zero,
      Matrix.zero_mul, add_zero, Pi.star_def, hps, hqs, hpp, hqq, hpq, hqp]

/-- **Orthogonal projections add in `K₀`.** -/
theorem projClass_add {p q : R} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpq : p * q = 0) : projClass (p + q) = projClass p + projClass q := by
  have hs : IsStarProjection (p + q) := hp.add hq hpq
  rw [projClass_eq hs, projClass_eq hp, projClass_eq hq, ← KTheory.KZero.mk_add]
  have h₁ : KTheory.Cycle.Rel
      (⟨1, Matrix.diagonal fun _ => p + q, isStarProjection_diagonal_const hs⟩ : KTheory.Cycle R)
      ⟨1 + 1, KTheory.blockSum (Matrix.diagonal fun _ : Fin 1 => p + q)
          (0 : Matrix (Fin 1) (Fin 1) R),
        KTheory.isStarProjection_blockSum (isStarProjection_diagonal_const hs)
          (IsStarProjection.zero _)⟩ :=
    KTheory.Cycle.rel_of_step (KTheory.Cycle.Step.pad 1)
  have h₂ : KTheory.Cycle.Rel
      (⟨1 + 1, KTheory.blockSum (Matrix.diagonal fun _ : Fin 1 => p + q)
          (0 : Matrix (Fin 1) (Fin 1) R),
        KTheory.isStarProjection_blockSum (isStarProjection_diagonal_const hs)
          (IsStarProjection.zero _)⟩ : KTheory.Cycle R)
      ⟨1 + 1, KTheory.blockSum (Matrix.diagonal fun _ : Fin 1 => p)
          (Matrix.diagonal fun _ : Fin 1 => q),
        KTheory.isStarProjection_blockSum (isStarProjection_diagonal_const hp)
          (isStarProjection_diagonal_const hq)⟩ :=
    KTheory.Cycle.rel_of_step
      (KTheory.Cycle.Step.mvn (murrayVonNeumannEquiv_blockSum_orthogonal hp hq hpq))
  exact kZero_mk_eq_of_rel (KTheory.Cycle.rel_trans h₁ h₂)

@[simp]
theorem projClass_zero : projClass (0 : R) = 0 := by
  have h := projClass_add (IsStarProjection.zero _) (IsStarProjection.zero _) (mul_zero (0 : R))
  simpa using h

/-- **Finite orthogonal sums of projections add in `K₀`.** -/
theorem projClass_sum {ι : Type*} [DecidableEq ι] (t : Finset ι) (f : ι → R)
    (hf : ∀ i ∈ t, IsStarProjection (f i))
    (horth : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → f i * f j = 0) :
    IsStarProjection (∑ i ∈ t, f i) ∧ projClass (∑ i ∈ t, f i) = ∑ i ∈ t, projClass (f i) := by
  induction t using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact ⟨IsStarProjection.zero _, projClass_zero⟩
  | insert a t ha ih =>
      obtain ⟨hp, hcl⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
        (fun i hi j hj => horth i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))
      have ha' : IsStarProjection (f a) := hf a (Finset.mem_insert_self a t)
      have hmul : f a * ∑ i ∈ t, f i = 0 := by
        rw [Finset.mul_sum]
        refine Finset.sum_eq_zero fun i hi => ?_
        refine horth a (Finset.mem_insert_self a t) i (Finset.mem_insert_of_mem hi) fun h => ?_
        exact ha (by rw [h]; exact hi)
      rw [Finset.sum_insert ha, Finset.sum_insert ha, projClass_add ha' hp hmul, hcl]
      exact ⟨ha'.add hp hmul, rfl⟩

end Projections

/-- In a C*-ring, `x* x = q` for a projection `q` forces `x q = x`: `(x - x q)* (x - x q) = 0`. -/
theorem mul_eq_self_of_star_mul_self_eq {A : Type*} [NonUnitalNormedRing A] [StarRing A]
    [CStarRing A] {x q : A} (hq : IsStarProjection q) (hx : star x * x = q) : x * q = x := by
  have hqq : q * q = q := hq.isIdempotentElem.eq
  have hqs : star q = q := hq.isSelfAdjoint.star_eq
  have e₁ : star x * (x * q) = q := by rw [← mul_assoc, hx, hqq]
  have e₂ : q * star x * x = q := by rw [mul_assoc, hx, hqq]
  have e₃ : q * star x * (x * q) = q := by
    rw [mul_assoc, ← mul_assoc (star x), hx, hqq, hqq]
  have h : star (x - x * q) * (x - x * q) = 0 := by
    rw [star_sub, star_mul, hqs, sub_mul, mul_sub, mul_sub, hx, e₁, e₂, e₃]
    simp only [sub_self]
  exact (sub_eq_zero.1 ((CStarRing.star_mul_self_eq_zero_iff _).1 h)).symm

section Graph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] (s r : E → V)

/-- **The vertex matrix** `A(v, w) = #{e | s e = v ∧ r e = w}` of the finite graph `(V, E, s, r)`. -/
def vertexMatrix : Matrix V V ℤ :=
  Matrix.of fun v w => ((Finset.univ.filter fun e => s e = v ∧ r e = w).card : ℤ)

omit [Fintype V] in
theorem vertexMatrix_apply (v w : V) :
    vertexMatrix s r v w = ((Finset.univ.filter fun e => s e = v ∧ r e = w).card : ℤ) :=
  rfl

/-- `x ↦ (1 - Mᵀ) x` on `ℤ^V`. -/
def relationHom (M : Matrix V V ℤ) : (V → ℤ) →+ (V → ℤ) where
  toFun x := (1 - Mᵀ) *ᵥ x
  map_zero' := Matrix.mulVec_zero _
  map_add' := Matrix.mulVec_add _

theorem relationHom_apply (M : Matrix V V ℤ) (x : V → ℤ) : relationHom M x = (1 - Mᵀ) *ᵥ x :=
  rfl

theorem relationHom_eq_sub_vecMul (M : Matrix V V ℤ) (x : V → ℤ) :
    relationHom M x = x - x ᵥ* M := by
  rw [relationHom_apply, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_transpose]

/-- **`coker(1 - Mᵀ)`** on `ℤ^V`. -/
abbrev cokernel (M : Matrix V V ℤ) : Type _ := (V → ℤ) ⧸ (relationHom M).range

variable (R : Type*) [NonUnitalSemiring R] [StarRing R]

/-- **A Cuntz–Krieger family of the graph `(V, E, s, r)` in a `*`-ring `R`.** The relation at a
vertex is imposed only when the vertex emits an edge. `S_mul_p` is automatic in a C*-ring
(`mul_eq_self_of_star_mul_self_eq`). -/
structure CuntzKriegerFamily where
  /-- The vertex projections. -/
  p : V → R
  /-- The edge partial isometries. -/
  S : E → R
  isStarProjection_p : ∀ v, IsStarProjection (p v)
  p_mul_p_of_ne : ∀ v w, v ≠ w → p v * p w = 0
  star_S_mul_S_self : ∀ e, star (S e) * S e = p (r e)
  star_S_mul_S_of_ne : ∀ e f, e ≠ f → star (S e) * S f = 0
  S_mul_p : ∀ e, S e * p (r e) = S e
  sum_S_mul_star_S : ∀ v, (∃ e, s e = v) →
    ∑ e ∈ Finset.univ.filter (fun e => s e = v), S e * star (S e) = p v

namespace CuntzKriegerFamily

variable {s r R} (F : CuntzKriegerFamily s r R)

omit [Fintype V] in
theorem isStarProjection_S_mul_star_S (e : E) : IsStarProjection (F.S e * star (F.S e)) := by
  refine ⟨?_, ?_⟩
  · show F.S e * star (F.S e) * (F.S e * star (F.S e)) = F.S e * star (F.S e)
    rw [mul_assoc, ← mul_assoc (star (F.S e)), F.star_S_mul_S_self, ← mul_assoc, F.S_mul_p]
  · show star (F.S e * star (F.S e)) = F.S e * star (F.S e)
    rw [star_mul, star_star]

omit [Fintype V] in
theorem S_mul_star_S_mul_of_ne {e f : E} (h : e ≠ f) :
    F.S e * star (F.S e) * (F.S f * star (F.S f)) = 0 := by
  rw [mul_assoc, ← mul_assoc (star (F.S e)), F.star_S_mul_S_of_ne e f h, zero_mul, mul_zero]

omit [Fintype V] in
/-- `S e S e* ∼ S e* S e = p (r e)`. -/
theorem murrayVonNeumannEquiv_S (e : E) :
    MurrayVonNeumannEquiv (F.S e * star (F.S e)) (F.p (r e)) :=
  ⟨star (F.S e), by rw [star_star], by rw [star_star, F.star_S_mul_S_self]⟩

/-- **The vertex relation** `[p_v] = ∑_w A(v, w) • [p_w]` at a vertex that emits an edge. -/
theorem projClass_p {v : V} (hv : ∃ e, s e = v) :
    projClass (F.p v) = ∑ w, vertexMatrix s r v w • projClass (F.p w) := by
  classical
  obtain ⟨-, hcl⟩ := projClass_sum (Finset.univ.filter fun e => s e = v)
    (fun e => F.S e * star (F.S e)) (fun e _ => F.isStarProjection_S_mul_star_S e)
    (fun e _ f _ hef => F.S_mul_star_S_mul_of_ne hef)
  calc projClass (F.p v)
      = projClass (∑ e ∈ Finset.univ.filter (fun e => s e = v), F.S e * star (F.S e)) := by
        rw [F.sum_S_mul_star_S v hv]
    _ = ∑ e ∈ Finset.univ.filter (fun e => s e = v), projClass (F.S e * star (F.S e)) := hcl
    _ = ∑ e ∈ Finset.univ.filter (fun e => s e = v), projClass (F.p (r e)) :=
        Finset.sum_congr rfl fun e _ => projClass_eq_of_murrayVonNeumannEquiv
          (F.isStarProjection_S_mul_star_S e) (F.isStarProjection_p _) (F.murrayVonNeumannEquiv_S e)
    _ = ∑ w, ∑ e ∈ (Finset.univ.filter fun e => s e = v).filter (fun e => r e = w),
          projClass (F.p w) :=
        (Finset.sum_fiberwise' _ r fun w => projClass (F.p w)).symm
    _ = ∑ w, vertexMatrix s r v w • projClass (F.p w) := by
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [Finset.sum_const, Finset.filter_filter, vertexMatrix_apply, natCast_zsmul]

/-- `δ_v ↦ [p_v]`, extended additively. -/
noncomputable def vertexClass : (V → ℤ) →+ KTheory.KZero R where
  toFun x := ∑ v, x v • projClass (F.p v)
  map_zero' := by simp
  map_add' x y := by simp only [Pi.add_apply, add_zsmul, Finset.sum_add_distrib]

theorem vertexClass_apply (x : V → ℤ) : F.vertexClass x = ∑ v, x v • projClass (F.p v) :=
  rfl

theorem vertexClass_vecMul (hE : ∀ v, ∃ e, s e = v) (x : V → ℤ) :
    F.vertexClass (x ᵥ* vertexMatrix s r) = F.vertexClass x := by
  rw [vertexClass_apply, vertexClass_apply]
  calc ∑ w, (x ᵥ* vertexMatrix s r) w • projClass (F.p w)
      = ∑ w, ∑ v, (x v * vertexMatrix s r v w) • projClass (F.p w) := by
        refine Finset.sum_congr rfl fun w _ => ?_
        show (∑ v, x v * vertexMatrix s r v w) • projClass (F.p w) = _
        exact Finset.sum_smul
    _ = ∑ v, ∑ w, (x v * vertexMatrix s r v w) • projClass (F.p w) := Finset.sum_comm
    _ = ∑ v, x v • projClass (F.p v) := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [F.projClass_p (hE v), Finset.smul_sum]
        exact Finset.sum_congr rfl fun w _ => mul_smul _ _ _

/-- **`δ_v ↦ [p_v]` kills the image of `1 - Aᵀ`** when the graph has no sinks. -/
theorem vertexClass_relationHom (hE : ∀ v, ∃ e, s e = v) (x : V → ℤ) :
    F.vertexClass (relationHom (vertexMatrix s r) x) = 0 := by
  rw [relationHom_eq_sub_vecMul, map_sub, F.vertexClass_vecMul hE, sub_self]

/-- **The homomorphism `coker(1 - Aᵀ) → K₀(R)`, `δ_v ↦ [p_v]`**, for a graph with no sinks. It is not
claimed to be an isomorphism. -/
noncomputable def cokernelToKZero (hE : ∀ v, ∃ e, s e = v) :
    cokernel (vertexMatrix s r) →+ KTheory.KZero R :=
  QuotientAddGroup.lift _ F.vertexClass (by
    intro y hy
    obtain ⟨x, rfl⟩ := AddMonoidHom.mem_range.1 hy
    exact AddMonoidHom.mem_ker.2 (F.vertexClass_relationHom hE x))

theorem cokernelToKZero_mk (hE : ∀ v, ∃ e, s e = v) (x : V → ℤ) :
    F.cokernelToKZero hE (QuotientAddGroup.mk x) = F.vertexClass x :=
  rfl

theorem vertexClass_single (v : V) : F.vertexClass (Pi.single v 1) = projClass (F.p v) := by
  rw [vertexClass_apply, Finset.sum_eq_single v, Pi.single_eq_same, one_zsmul]
  · intro w _ hw
    rw [Pi.single_eq_of_ne hw, zero_zsmul]
  · intro hv
    exact absurd (Finset.mem_univ v) hv

theorem cokernelToKZero_single (hE : ∀ v, ∃ e, s e = v) (v : V) :
    F.cokernelToKZero hE (QuotientAddGroup.mk (Pi.single v 1)) = projClass (F.p v) :=
  F.vertexClass_single v

theorem vertexClass_const_one : F.vertexClass (fun _ => 1) = ∑ v, projClass (F.p v) := by
  rw [vertexClass_apply]
  simp only [one_zsmul]

end CuntzKriegerFamily

end Graph

section Unital

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] {s r : E → V}
  {R : Type*} [Semiring R] [StarRing R]

namespace CuntzKriegerFamily

variable (F : CuntzKriegerFamily s r R)

/-- `[1] = ∑_v [p_v]` when `∑_v p_v = 1`. -/
theorem projClass_one (h1 : ∑ v, F.p v = 1) : projClass (1 : R) = ∑ v, projClass (F.p v) := by
  rw [← h1]
  exact (projClass_sum Finset.univ F.p (fun v _ => F.isStarProjection_p v)
    (fun v _ w _ hvw => F.p_mul_p_of_ne v w hvw)).2

/-- **The class of `∑_v δ_v` maps to `[1]`.** -/
theorem cokernelToKZero_one (hE : ∀ v, ∃ e, s e = v) (h1 : ∑ v, F.p v = 1) :
    F.cokernelToKZero hE (QuotientAddGroup.mk fun _ => 1) = projClass (1 : R) := by
  rw [F.projClass_one h1]
  exact F.vertexClass_const_one

end CuntzKriegerFamily

end Unital

end GraphCStar
end GroupApproximation
