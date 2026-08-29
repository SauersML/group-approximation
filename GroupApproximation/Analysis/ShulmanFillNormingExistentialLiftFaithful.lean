import GroupApproximation.Analysis.ShulmanFillNormingExistentialLiftTwoLeg

/-!
# The symmetry step: faithfulness on `H` suffices

`Analysis/ShulmanFillNormingExistentialLiftTwoLeg` wires Shulman's Theorem 10 to
one doubled lift, but leaves the faithfulness hypothesis where
`isMFAlgebra_amalgam_of_glue` had it: injectivity of the glued limit at the
*doubled* pair `(pairRep ρ₁ ρ₂, pairRep ρ₂ ρ₁)`, on `H ⊕ H`.  The paper does not
assume that.  It assumes `π = π₁ * π₂` faithful on the double, on `H`, and says
the doubled pair inherits it "by symmetry".  This module proves that.

Write `Λ` for the evaluation of `D *_C D` at `(ρ₁, ρ₂)`, valued in `B(H)`, and
`Λ'` for its evaluation at `(pairRep ρ₁ ρ₂, pairRep ρ₂ ρ₁)`, valued in
`B(H ⊕ H)`.  Both factor through one map into `B(H) × B(H)`:

    `Θ = pairAmalgamEval`, the evaluation at `((ρ₁, ρ₂), (ρ₂, ρ₁))` ,

because `Λ = fst ∘ Θ` and `Λ' = hBlockOp ∘ diag ∘ Θ`, each by the uniqueness half
of the universal property (`universalCStarAmalgam_existsUnique_lift`): the two
sides are homomorphisms out of the amalgam agreeing on both factor images.  So
`Λ'` separates whatever `Θ` separates, and `Θ` separates whatever `Λ` does, as
soon as the two maps that carry `Θ` to `Λ'` are injective.

Both are, and neither is analytic:

* `diagonalPairHom2_injective` — a diagonal is determined by its two entries,
  which is `diagonalPairHom2_entry_self` read at `0` and at `1`;
* `hBlockOp_injective` — a matrix of operators is determined by the block
  operator it defines, because `hBlockOp X (ι_j v) i = X i j v`
  (`hBlockOp_apply_hBlockIncl`, from `hBlockOp_coord` together with
  `hBlockIncl_coord_same` and `hBlockIncl_coord_ne`).

`isMFAlgebra_amalgam_of_doubleLR_of_faithful` is then Theorem 10 with the
paper's own hypotheses: two lifts on `H` into one `𝒟`, their asymptotic
agreement on `C`, MF-ness of the doubled `𝒟`, and faithfulness of `ρ₁ * ρ₂` on
`H`.  Nothing about `H ⊕ H` is assumed any more; the doubling is entirely
internal to the proof.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology

noncomputable section

/-! ## A matrix of operators is determined by its block operator -/

section BlockInjective

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E] {n : ℕ}

/-- **The entries of a block operator are recovered by testing on the
inclusions.**  Only the `j`-th column survives `ι_j v`, and only its `i`-th
coordinate is read. -/
theorem hBlockOp_apply_hBlockIncl (X : CStarMatrix (Fin n) (Fin n) (E →L[ℂ] E))
    (i j : Fin n) (v : E) :
    hBlockOp X (hBlockIncl E n j v) i = (X i j) v := by
  rw [hBlockOp_coord]
  refine (Finset.sum_eq_single j (fun p _ hp ↦ ?_)
    (fun h ↦ absurd (Finset.mem_univ j) h)).trans ?_
  · rw [hBlockIncl_coord_ne hp, map_zero]
  · rw [hBlockIncl_coord_same]

/-- **The block operator determines the matrix.** -/
theorem hBlockOp_injective :
    Function.Injective (hBlockOp (E := E) (n := n)) := by
  intro X Y hXY
  refine CStarMatrix.ext fun i j ↦ ?_
  refine ContinuousLinearMap.ext fun v ↦ ?_
  rw [← hBlockOp_apply_hBlockIncl X i j v, ← hBlockOp_apply_hBlockIncl Y i j v,
    hXY]

end BlockInjective

/-! ## A diagonal is determined by its entries -/

section DiagonalPairInjective

variable {E : Type} [CStarAlgebra E]

/-- **The diagonal of a pair is faithful.**  Its `(0,0)` and `(1,1)` entries are
the two coordinates. -/
theorem diagonalPairHom2_injective :
    Function.Injective (diagonalPairHom2 (E := E)) := by
  intro p q h
  refine Prod.ext ?_ ?_
  · have h0 : (diagonalPairHom2 p : CStarMatrix (Fin 2) (Fin 2) E) 0 0
        = (diagonalPairHom2 q : CStarMatrix (Fin 2) (Fin 2) E) 0 0 :=
      congrArg (fun M : CStarMatrix (Fin 2) (Fin 2) E ↦ M 0 0) h
    rw [diagonalPairHom2_entry_self p 0, diagonalPairHom2_entry_self q 0] at h0
    exact h0
  · have h1 : (diagonalPairHom2 p : CStarMatrix (Fin 2) (Fin 2) E) 1 1
        = (diagonalPairHom2 q : CStarMatrix (Fin 2) (Fin 2) E) 1 1 :=
      congrArg (fun M : CStarMatrix (Fin 2) (Fin 2) E ↦ M 1 1) h
    rw [diagonalPairHom2_entry_self p 1, diagonalPairHom2_entry_self q 1] at h1
    exact h1

/-- The first coordinate of a product, as a `*`-homomorphism.  Every clause is
`rfl`, because the operations of a product are the coordinate operations. -/
def starAlgHomFst : E × E →⋆ₐ[ℂ] E where
  toFun p := p.1
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

@[simp] theorem starAlgHomFst_apply (p : E × E) :
    starAlgHomFst p = p.1 := rfl

end DiagonalPairInjective

/-! ## Compatibility of the paired homomorphism -/

section PairCompatibility

variable {C D E : Type} [CStarAlgebra C] [CStarAlgebra D] [CStarAlgebra E]

/-- **The pair of two compatible legs is compatible with itself swapped.**  On
the image of `C` the two legs agree, so both pairs are the same pair there. -/
theorem starAlgHomPair_comp_eq (k : C →⋆ₐ[ℂ] D) {ρ₁ ρ₂ : D →⋆ₐ[ℂ] E}
    (hρ : ρ₁.comp k = ρ₂.comp k) :
    (starAlgHomPair ρ₁ ρ₂).comp k = (starAlgHomPair ρ₂ ρ₁).comp k := by
  apply StarAlgHom.ext
  intro c
  have h : ρ₁ (k c) = ρ₂ (k c) := DFunLike.congr_fun hρ c
  show ((ρ₁ (k c), ρ₂ (k c)) : E × E) = (ρ₂ (k c), ρ₁ (k c))
  rw [h]

end PairCompatibility

/-! ## The common factorisation, and the transfer of faithfulness -/

section Faithful

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H] [Nontrivial (H →L[ℂ] H)]
variable [Nontrivial (BlockSpace H 2 →L[ℂ] BlockSpace H 2)]
variable {C D : Type} [CStarAlgebra C] [CStarAlgebra D]
variable (k : C →⋆ₐ[ℂ] D) {ρ₁ ρ₂ : D →⋆ₐ[ℂ] (H →L[ℂ] H)}
variable [Nonempty (CStarAmalgamRepresentation k k)]

/-- **The evaluation both legs factor through.**  The amalgam evaluated at the
pair of pairs `((ρ₁, ρ₂), (ρ₂, ρ₁))`, valued in `B(H) × B(H)`. -/
def pairAmalgamEval (hρ : ρ₁.comp k = ρ₂.comp k) :
    UniversalCStarAmalgam k k →⋆ₐ[ℂ] (H →L[ℂ] H) × (H →L[ℂ] H) :=
  universalCStarAmalgamEval k k
    (CStarAmalgamRepresentation.ofCompatiblePair k k
      (starAlgHomPair ρ₁ ρ₂) (starAlgHomPair ρ₂ ρ₁)
      (starAlgHomPair_comp_eq k hρ))

omit [Nontrivial (BlockSpace H 2 →L[ℂ] BlockSpace H 2)] in
@[simp] theorem pairAmalgamEval_left (hρ : ρ₁.comp k = ρ₂.comp k) (d : D) :
    pairAmalgamEval k hρ (universalCStarAmalgamLeft k k d) = (ρ₁ d, ρ₂ d) := rfl

omit [Nontrivial (BlockSpace H 2 →L[ℂ] BlockSpace H 2)] in
@[simp] theorem pairAmalgamEval_right (hρ : ρ₁.comp k = ρ₂.comp k) (d : D) :
    pairAmalgamEval k hρ (universalCStarAmalgamRight k k d) = (ρ₂ d, ρ₁ d) := rfl

omit [Nontrivial (BlockSpace H 2 →L[ℂ] BlockSpace H 2)] in
/-- **The undoubled evaluation is the first coordinate of `Θ`.**  Both sides are
homomorphisms out of the amalgam sending the left factor to `ρ₁` and the right
to `ρ₂`, so the universal property identifies them. -/
theorem limitRep_eval_eq_fst_pairAmalgamEval (hρ : ρ₁.comp k = ρ₂.comp k)
    (x : UniversalCStarAmalgam k k) :
    universalCStarAmalgamEval k k (StarStrongAsymptoticLift.limitRep k hρ) x
      = (pairAmalgamEval k hρ x).1 := by
  obtain ⟨f, _hf, huniq⟩ := universalCStarAmalgam_existsUnique_lift k k ρ₁ ρ₂ hρ
  have hleft := huniq
    (universalCStarAmalgamEval k k (StarStrongAsymptoticLift.limitRep k hρ))
    ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩
  have hright := huniq
    ((starAlgHomFst (E := H →L[ℂ] H)).comp (pairAmalgamEval k hρ))
    ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩
  exact DFunLike.congr_fun (hleft.trans hright.symm) x

/-- **The doubled evaluation is the block diagonal of `Θ`.**  Same argument, one
universe of homomorphisms up: both sides send the left factor to `pairRep ρ₁ ρ₂`
and the right to `pairRep ρ₂ ρ₁`. -/
theorem pairRep_limitRep_eval_eq (hρ : ρ₁.comp k = ρ₂.comp k)
    (x : UniversalCStarAmalgam k k) :
    universalCStarAmalgamEval k k
        (StarStrongAsymptoticLift.limitRep k (pairRep_comp_eq k hρ)) x
      = hBlockOp (diagonalPairHom2 (pairAmalgamEval k hρ x)) := by
  obtain ⟨f, _hf, huniq⟩ :=
    universalCStarAmalgam_existsUnique_lift k k (pairRep ρ₁ ρ₂) (pairRep ρ₂ ρ₁)
      (pairRep_comp_eq k hρ)
  have hleft := huniq
    (universalCStarAmalgamEval k k
      (StarStrongAsymptoticLift.limitRep k (pairRep_comp_eq k hρ)))
    ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩
  have hright := huniq
    (((hBlockOpHom (E := H) (n := 2)).comp
      (diagonalPairHom2 (E := H →L[ℂ] H))).comp (pairAmalgamEval k hρ))
    ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩
  exact DFunLike.congr_fun (hleft.trans hright.symm) x

/-- **The symmetry step.**  Faithfulness of the pair of limits on `H` gives
faithfulness of the doubled pair on `H ⊕ H`: the doubled evaluation is the
block diagonal of `Θ`, and both the diagonal and the block operator are
injective, so `Θ` is separated wherever the doubled evaluation is, and the
undoubled evaluation is a coordinate of `Θ`. -/
theorem injective_pairRep_eval_of_injective (hρ : ρ₁.comp k = ρ₂.comp k)
    (hΛ : Function.Injective
      (universalCStarAmalgamEval k k (StarStrongAsymptoticLift.limitRep k hρ))) :
    Function.Injective (universalCStarAmalgamEval k k
      (StarStrongAsymptoticLift.limitRep k (pairRep_comp_eq k hρ))) := by
  intro x y hxy
  apply hΛ
  rw [limitRep_eval_eq_fst_pairAmalgamEval k hρ x,
    limitRep_eval_eq_fst_pairAmalgamEval k hρ y]
  have hblock : hBlockOp (diagonalPairHom2 (pairAmalgamEval k hρ x))
      = hBlockOp (diagonalPairHom2 (pairAmalgamEval k hρ y)) := by
    rw [← pairRep_limitRep_eval_eq k hρ x, ← pairRep_limitRep_eval_eq k hρ y]
    exact hxy
  have hpair : pairAmalgamEval k hρ x = pairAmalgamEval k hρ y :=
    diagonalPairHom2_injective (hBlockOp_injective hblock)
  rw [hpair]

end Faithful

/-! ## Theorem 10 with the paper's hypotheses -/

section Consumer

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H] [Nontrivial (H →L[ℂ] H)]
variable [Nontrivial (BlockSpace H 2 →L[ℂ] BlockSpace H 2)]
variable {A : ℕ → Type} [∀ n, CStarAlgebra (A n)]
variable [∀ n, PartialOrder (A n)] [∀ n, StarOrderedRing (A n)]
variable [∀ n, Nontrivial (A n)]
variable (ι : ∀ n, A n →⋆ₙₐ[ℂ] (H →L[ℂ] H))
variable (hnorm : ∀ (n : ℕ) (x : A n), ‖ι n x‖ ≤ ‖x‖)
variable (hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v))
variable {C D : Type} [CStarAlgebra C] [CStarAlgebra D]
variable [TopologicalSpace.SeparableSpace D]
variable (k : C →⋆ₐ[ℂ] D) {ρ₁ ρ₂ : D →⋆ₐ[ℂ] (H →L[ℂ] H)}
variable [Nonempty (CStarAmalgamRepresentation k k)]

/-- **Shulman's Theorem 10, with the paper's own hypotheses.**  Two asymptotic
lifts of `ρ₁` and `ρ₂` into one `𝒟` on `H`, agreeing asymptotically on `C`, an
MF doubled `𝒟`, and faithfulness of the pair of limits **on `H`**.  The doubling
and the flip are internal to the proof: `doubleLR` supplies the lift of
`diag(ρ₁, ρ₂)`, the flip supplies the second leg exactly, and
`injective_pairRep_eval_of_injective` supplies the faithfulness the glued map
needs. -/
theorem isMFAlgebra_amalgam_of_doubleLR_of_faithful
    (hD : HasMFEmbedding (StarStrong.starStrongSubalgebra (doubledIota ι)
      (doubled_norm_le ι) (doubled_hone ι hone)))
    (φ₁ : StarStrongAsymptoticLift ι hnorm hone ρ₁)
    (φ₂ : StarStrongAsymptoticLift ι hnorm hone ρ₂)
    (hagree : ∀ c : C, Tendsto
      (fun t ↦ ‖φ₁.toFun t (k c) - φ₂.toFun t (k c)‖) atTop (𝓝 0))
    (hρ : ρ₁.comp k = ρ₂.comp k)
    (hΛ : Function.Injective
      (universalCStarAmalgamEval k k (StarStrongAsymptoticLift.limitRep k hρ))) :
    IsMFAlgebra (UniversalCStarAmalgam k k) :=
  isMFAlgebra_amalgam_of_doubleLR ι hnorm hone k hD φ₁ φ₂ hagree hρ
    (injective_pairRep_eval_of_injective k hρ hΛ)

end Consumer

end

end ShulmanFill
end GroupApproximation
