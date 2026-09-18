import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.StableReduction.FiveStepCorner
import GroupApproximation.Meta.AxiomGuard

/-!
# Corner endomorphisms commute with index embeddings (sk-leavitt-34c)

Let `σ_r = fiveStepCornerHom L r` be the corner endomorphism of `St_n(R)` (`FiveStepCorner.lean`).
For an injection of index sets `e : Fin n ↪ Fin m`, the index map `indexMap e` intertwines the
corner endomorphisms:

  `σ_{e r} ∘ indexMap e = indexMap e ∘ σ_r`   (`fiveStepCornerInj_cornerHom_comp_indexMap`).

On generators both sides send `xᵢⱼ(a)` to `x_{e i, e j}(c)` with the same corner coefficient `c`,
because `e i = e r ↔ i = r`.  For a transposition `e = (p q)` this makes `σ_p` and `σ_q`
conjugate by the involution `indexMap (p q)` (`fiveStepCornerInj_indexMap_swap_swap`).
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open GroupApproximation.SteinbergGroup

variable {R : Type*} [Ring R] (L : LeavittFamily R) {n : ℕ}

/-- Corner coefficients are invariant under an injection of index sets. -/
theorem fiveStepCornerInj_coeff_embedding {m : ℕ} (e : Fin n ↪ Fin m) (r i j : Fin n) (a : R) :
    fiveStepCornerCoeff L (e r) (e i) (e j) a = fiveStepCornerCoeff L r i j a := by
  by_cases hi : i = r
  · rw [fiveStepCornerCoeff_of_row L (e r) (j := e j) a (congrArg (⇑e) hi),
      fiveStepCornerCoeff_of_row L r (j := j) a hi]
  · have hi' : ¬ e i = e r := fun h => hi (e.injective h)
    by_cases hj : j = r
    · rw [fiveStepCornerCoeff_of_col L (e r) a hi' (congrArg (⇑e) hj),
        fiveStepCornerCoeff_of_col L r a hi hj]
    · have hj' : ¬ e j = e r := fun h => hj (e.injective h)
      rw [fiveStepCornerCoeff_of_plain L (e r) a hi' hj',
        fiveStepCornerCoeff_of_plain L r a hi hj]

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepCornerInj_coeff_embedding

/-- Corner coefficients are invariant under `Fin.castSucc`. -/
theorem fiveStepCornerInj_coeff_castSucc (r i j : Fin n) (a : R) :
    fiveStepCornerCoeff L (Fin.castSucc r) (Fin.castSucc i) (Fin.castSucc j) a =
      fiveStepCornerCoeff L r i j a :=
  fiveStepCornerInj_coeff_embedding L
    (⟨Fin.castSucc, Fin.castSucc_injective n⟩ : Fin n ↪ Fin (n + 1)) r i j a

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepCornerInj_coeff_castSucc

/-- **Index embeddings intertwine corner endomorphisms**:
`σ_{e r} ∘ indexMap e = indexMap e ∘ σ_r`. -/
theorem fiveStepCornerInj_cornerHom_comp_indexMap {m : ℕ} (e : Fin n ↪ Fin m) (r : Fin n) :
    (fiveStepCornerHom L (e r)).comp (indexMap (R := R) e) =
      (indexMap (R := R) e).comp (fiveStepCornerHom L r) := by
  apply PresentedGroup.ext
  rintro ⟨i, j, hij, a⟩
  change fiveStepCornerHom L (e r) (indexMap e (x i j hij a)) =
    indexMap e (fiveStepCornerHom L r (x i j hij a))
  rw [indexMap_x, fiveStepCornerHom_x, fiveStepCornerHom_x, indexMap_x,
    fiveStepCornerInj_coeff_embedding]

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepCornerInj_cornerHom_comp_indexMap

/-- Pointwise form, with the target index `q = e r` named. -/
theorem fiveStepCornerInj_cornerHom_indexMap {m : ℕ} (e : Fin n ↪ Fin m) (r : Fin n) (q : Fin m)
    (hq : e r = q) (u : SteinbergGroup (Fin n) R) :
    fiveStepCornerHom L q (indexMap e u) = indexMap e (fiveStepCornerHom L r u) := by
  subst hq
  exact DFunLike.congr_fun (fiveStepCornerInj_cornerHom_comp_indexMap L e r) u

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepCornerInj_cornerHom_indexMap

/-- The index map of a transposition is an involution of `St_m(R)`. -/
theorem fiveStepCornerInj_indexMap_swap_swap {m : ℕ} (p q : Fin m)
    (w : SteinbergGroup (Fin m) R) :
    indexMap (Equiv.swap p q).toEmbedding (indexMap (Equiv.swap p q).toEmbedding w) = w := by
  have h : (indexMap (R := R) (Equiv.swap p q).toEmbedding).comp
      (indexMap (R := R) (Equiv.swap p q).toEmbedding) = MonoidHom.id _ := by
    apply PresentedGroup.ext
    rintro ⟨i, j, hij, c⟩
    change indexMap (Equiv.swap p q).toEmbedding
        (indexMap (Equiv.swap p q).toEmbedding (x i j hij c)) = x i j hij c
    rw [indexMap_x, indexMap_x]
    exact usedRankFour_x_congr (Equiv.swap_apply_self p q i) (Equiv.swap_apply_self p q j)
  exact DFunLike.congr_fun h w

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepCornerInj_indexMap_swap_swap

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
