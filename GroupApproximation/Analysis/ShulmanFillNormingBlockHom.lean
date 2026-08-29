import GroupApproximation.Analysis.ShulmanFillNormingBlockHilbert

/-!
# The block operator as a `*`-homomorphism

`Analysis/ShulmanFillNormingBlockHilbert` builds `hBlockOp`, a matrix of
operators read as one operator on the block space.  This module proves it is a
unital `*`-homomorphism `M_n(B(E)) → B(E^n)`.

Two things make the rest of the `M₂` amplification cheap once this is in place.
Contractivity — the `hnorm` clause of Shulman's `𝒟` — is automatic, because a
`*`-homomorphism of C-star algebras is contractive
(`NonUnitalStarAlgHom.norm_apply_le`); nothing about the block norm has to be
computed.  And the flip `((0,1),(1,0))` is a unitary of `M₂` over the models,
so its image is a unitary of `B(E²)` and its constant sequence is the
conjugating unitary that
`Analysis/ShulmanFillNormingConjugationLift.conjugate` asks for.

Everything below is a coordinate computation, and every coordinate is read off
by pairing with an inclusion: `⟪ι_i y, T w⟫ = ⟪y, (T w) i⟫`.  That is the same
idiom `Analysis/LanceBlockOperator` uses, so no new Mathlib surface is
touched.
-/

namespace GroupApproximation
namespace ShulmanFill

open scoped InnerProductSpace

noncomputable section

section BlockHom

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E] {n : ℕ}

/-- The sesquilinear form of the block operator is the sum of the entry
forms. -/
theorem inner_hBlockOp (X : CStarMatrix (Fin n) (Fin n) (E →L[ℂ] E))
    (v w : BlockSpace E n) :
    ⟪v, hBlockOp X w⟫_ℂ = ∑ i : Fin n, ∑ j : Fin n, ⟪v i, X i j (w j)⟫_ℂ := by
  rw [hBlockOp, sum_apply, inner_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [sum_apply, inner_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have h : (((hBlockIncl E n i).comp ((X i j).comp (hBlockProj E n j))) w)
      = hBlockIncl E n i ((X i j) (w j)) := rfl
  rw [h, inner_hBlockIncl_right]

/-- The same form with the operator on the left of the pairing, which is the
side `ContinuousLinearMap.eq_adjoint_iff` puts it on. -/
theorem inner_hBlockOp_left (X : CStarMatrix (Fin n) (Fin n) (E →L[ℂ] E))
    (v w : BlockSpace E n) :
    ⟪hBlockOp X v, w⟫_ℂ
      = ∑ i : Fin n, ∑ j : Fin n, ⟪(X i j) (v j), w i⟫_ℂ := by
  rw [← inner_conj_symm (hBlockOp X v) w, inner_hBlockOp, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ ↦ inner_conj_symm _ _

/-- **Coordinatewise description of the block operator.**  Pairing with the
`i`-th inclusion picks out the `i`-th coordinate, and only the `i`-th row of
the matrix survives. -/
theorem hBlockOp_coord (X : CStarMatrix (Fin n) (Fin n) (E →L[ℂ] E))
    (w : BlockSpace E n) (i : Fin n) :
    hBlockOp X w i = ∑ j : Fin n, (X i j) (w j) := by
  -- The test vector has to be introduced at `E` rather than at the type of the
  -- goal's equation, which is the unreduced `(fun _ ↦ E) i` of the `PiLp`
  -- family: taken from there, `hBlockIncl` is applied to that type instead and
  -- lands in a different block space.
  have key : ∀ y : E,
      ⟪y, hBlockOp X w i⟫_ℂ = ⟪y, ∑ j : Fin n, (X i j) (w j)⟫_ℂ := by
    intro y
    rw [← inner_hBlockIncl_left i y (hBlockOp X w), inner_hBlockOp, inner_sum]
    refine (Finset.sum_eq_single i (fun p _ hp ↦ ?_)
      (fun h ↦ absurd (Finset.mem_univ i) h)).trans ?_
    · refine Finset.sum_eq_zero fun q _ ↦ ?_
      rw [hBlockIncl_coord_ne hp, inner_zero_left]
    · refine Finset.sum_congr rfl fun q _ ↦ ?_
      rw [hBlockIncl_coord_same]
  exact ext_inner_left ℂ key

omit [CompleteSpace E] in
/-- Two operators of the block space agreeing in every coordinate on every
vector are equal. -/
theorem blockOp_ext {S T : BlockSpace E n →L[ℂ] BlockSpace E n}
    (h : ∀ (w : BlockSpace E n) (i : Fin n), S w i = T w i) : S = T := by
  refine ContinuousLinearMap.ext fun w ↦ ?_
  refine ext_inner_left ℂ fun v ↦ ?_
  rw [inner_block_eq_sum, inner_block_eq_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [h w i]

/-! ## The algebra laws -/

theorem hBlockOp_add (X Y : CStarMatrix (Fin n) (Fin n) (E →L[ℂ] E)) :
    hBlockOp (X + Y) = hBlockOp X + hBlockOp Y := by
  refine blockOp_ext fun w i ↦ ?_
  rw [hBlockOp_coord, _root_.add_apply]
  show ∑ j : Fin n, ((X + Y) i j) (w j) =
    hBlockOp X w i + hBlockOp Y w i
  rw [hBlockOp_coord, hBlockOp_coord, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [CStarMatrix.add_apply, _root_.add_apply]

theorem hBlockOp_smul (z : ℂ) (X : CStarMatrix (Fin n) (Fin n) (E →L[ℂ] E)) :
    hBlockOp (z • X) = z • hBlockOp X := by
  refine blockOp_ext fun w i ↦ ?_
  rw [hBlockOp_coord, _root_.smul_apply]
  show ∑ j : Fin n, ((z • X) i j) (w j) = z • (hBlockOp X w i)
  rw [hBlockOp_coord, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [CStarMatrix.smul_apply, _root_.smul_apply]

theorem hBlockOp_zero :
    hBlockOp (0 : CStarMatrix (Fin n) (Fin n) (E →L[ℂ] E)) = 0 := by
  refine blockOp_ext fun w i ↦ ?_
  rw [hBlockOp_coord]
  show ∑ j : Fin n, ((0 : CStarMatrix (Fin n) (Fin n) (E →L[ℂ] E)) i j) (w j)
    = (0 : BlockSpace E n →L[ℂ] BlockSpace E n) w i
  refine (Finset.sum_eq_zero fun j _ ↦ ?_).trans rfl
  rw [CStarMatrix.zero_apply, _root_.zero_apply]

theorem hBlockOp_one :
    hBlockOp (1 : CStarMatrix (Fin n) (Fin n) (E →L[ℂ] E)) = 1 := by
  refine blockOp_ext fun w i ↦ ?_
  rw [hBlockOp_coord]
  show ∑ j : Fin n, ((1 : CStarMatrix (Fin n) (Fin n) (E →L[ℂ] E)) i j) (w j)
    = w i
  refine (Finset.sum_eq_single i (fun j _ hj ↦ ?_)
    (fun h ↦ absurd (Finset.mem_univ i) h)).trans ?_
  · rw [CStarMatrix.one_apply_ne (Ne.symm hj),
      _root_.zero_apply]
  · rw [CStarMatrix.one_apply_eq,
      _root_.one_apply_eq_self]

theorem hBlockOp_mul (X Y : CStarMatrix (Fin n) (Fin n) (E →L[ℂ] E)) :
    hBlockOp (X * Y) = hBlockOp X * hBlockOp Y := by
  refine blockOp_ext fun w i ↦ ?_
  rw [hBlockOp_coord, _root_.mul_apply_eq_comp, hBlockOp_coord]
  have hinner : ∀ j : Fin n, (X i j) (hBlockOp Y w j) =
      ∑ q : Fin n, (X i j) ((Y j q) (w q)) := by
    intro j
    rw [hBlockOp_coord, map_sum]
  rw [Finset.sum_congr rfl fun j _ ↦ hinner j, Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [CStarMatrix.mul_apply, sum_apply]
  rfl

theorem hBlockOp_star (X : CStarMatrix (Fin n) (Fin n) (E →L[ℂ] E)) :
    hBlockOp (star X) = star (hBlockOp X) := by
  have key : hBlockOp (star X)
      = ContinuousLinearMap.adjoint (hBlockOp X) := by
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    rw [inner_hBlockOp_left, inner_hBlockOp]
    have hentry : ∀ i j : Fin n,
        ⟪(star X i j) (x j), y i⟫_ℂ = ⟪x j, (X j i) (y i)⟫_ℂ := by
      intro i j
      rw [CStarMatrix.star_apply, ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_left]
    calc ∑ i : Fin n, ∑ j : Fin n, ⟪(star X i j) (x j), y i⟫_ℂ
        = ∑ i : Fin n, ∑ j : Fin n, ⟪x j, (X j i) (y i)⟫_ℂ :=
          Finset.sum_congr rfl fun i _ ↦
            Finset.sum_congr rfl fun j _ ↦ hentry i j
      _ = ∑ j : Fin n, ∑ i : Fin n, ⟪x j, (X j i) (y i)⟫_ℂ := Finset.sum_comm
  rw [ContinuousLinearMap.star_eq_adjoint, key]

/-- **The block operator, as a unital `*`-homomorphism `M_n(B(E)) → B(E^n)`.**
Contractivity is not proved here and does not have to be: a
`*`-homomorphism of C-star algebras is contractive. -/
def hBlockOpHom :
    CStarMatrix (Fin n) (Fin n) (E →L[ℂ] E) →⋆ₐ[ℂ]
      (BlockSpace E n →L[ℂ] BlockSpace E n) where
  toFun := hBlockOp
  map_one' := hBlockOp_one
  map_mul' := hBlockOp_mul
  map_zero' := hBlockOp_zero
  map_add' := hBlockOp_add
  commutes' z := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      hBlockOp_smul, hBlockOp_one]
  map_star' := hBlockOp_star

@[simp] theorem hBlockOpHom_apply
    (X : CStarMatrix (Fin n) (Fin n) (E →L[ℂ] E)) :
    hBlockOpHom (E := E) (n := n) X = hBlockOp X := rfl

end BlockHom

end

end ShulmanFill
end GroupApproximation
