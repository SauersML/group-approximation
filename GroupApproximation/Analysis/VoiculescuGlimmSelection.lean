import GroupApproximation.Analysis.VoiculescuGlimmEscape
import GroupApproximation.Analysis.VoiculescuGlimmExpansion

/-!
# (V2) The successive selection: vectors whose cross terms vanish

This is the last construction in Glimm's lemma.  The separation delivers the
state's values as a convex combination of vector states; the expansion says a
superposition reproduces that combination up to its cross terms
`⟪a ξᵢ, ξⱼ⟫`; and this module chooses the vectors so those cross terms are not
merely small but **zero**.

The choice is successive, and the induction carries the obstruction rather than
the vectors: having picked `ξ₀`, enlarge the subspace to

    `V' = V ⊔ span {ξ₀} ⊔ span {a_p ξ₀}` ,

still finite-dimensional, and pick the remaining vectors orthogonal to *that*.
Everything then follows from one fact — a vector orthogonal to `V'` is
orthogonal to `ξ₀` and to every `a_p ξ₀` — which is what makes the induction go
through with no estimates anywhere.

## Where self-adjointness is spent

The construction kills only one order of cross term: `ξⱼ ⊥ a_p ξ₀` gives
`⟪a_p ξ₀, ξⱼ⟫ = 0`, and says nothing directly about `⟪a_p ξⱼ, ξ₀⟫`.  The reverse
comes from self-adjointness, `⟪a ξⱼ, ξ₀⟫ = ⟪ξⱼ, a ξ₀⟫ = conj ⟪a ξ₀, ξⱼ⟫`.  So
the self-adjoint restriction that `Analysis/VoiculescuGlimmSeparation` took for
an unrelated reason — keeping the tuples real — is exactly what makes the
selection work.  A general family would have to orthogonalise against `a⋆_p ξ₀`
as well, doubling the obstruction at every step.

The infinite-dimensionality of `H` is the hypothesis that keeps vectors
available, and it is not an extra assumption: `A ∩ K(H) = 0` forces it, which
is `not_finiteDimensional_of_compactMem_eq_zero`.
-/

namespace GroupApproximation
namespace ShulmanFill

open scoped InnerProductSpace
open scoped ComplexOrder

noncomputable section

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The obstruction subspace after one choice: the old one together with the
chosen vector and its images. -/
def selectionObstruction {m : ℕ} (a : Fin m → (H →L[ℂ] H)) (V : Submodule ℂ H)
    (x : H) : Submodule ℂ H :=
  V ⊔ Submodule.span ℂ (insert x (Set.range fun p ↦ a p x))

omit [CompleteSpace H] in
theorem finite_selectionSet {m : ℕ} (a : Fin m → (H →L[ℂ] H)) (x : H) :
    (insert x (Set.range fun p ↦ a p x)).Finite :=
  (Set.finite_range _).insert x

instance finiteDimensional_selectionObstruction {m : ℕ} (a : Fin m → (H →L[ℂ] H))
    (V : Submodule ℂ H) [FiniteDimensional ℂ V] (x : H) :
    FiniteDimensional ℂ (selectionObstruction a V x) := by
  have : FiniteDimensional ℂ
      (Submodule.span ℂ (insert x (Set.range fun p ↦ a p x))) :=
    FiniteDimensional.span_of_finite ℂ (finite_selectionSet a x)
  exact Submodule.finiteDimensional_sup _ _

omit [CompleteSpace H] in
theorem le_selectionObstruction {m : ℕ} (a : Fin m → (H →L[ℂ] H))
    (V : Submodule ℂ H) (x : H) : V ≤ selectionObstruction a V x :=
  le_sup_left

omit [CompleteSpace H] in
theorem mem_selectionObstruction {m : ℕ} (a : Fin m → (H →L[ℂ] H))
    (V : Submodule ℂ H) (x : H) : x ∈ selectionObstruction a V x :=
  Submodule.mem_sup_right (Submodule.subset_span (Set.mem_insert x _))

omit [CompleteSpace H] in
theorem apply_mem_selectionObstruction {m : ℕ} (a : Fin m → (H →L[ℂ] H))
    (V : Submodule ℂ H) (x : H) (p : Fin m) :
    a p x ∈ selectionObstruction a V x :=
  Submodule.mem_sup_right (Submodule.subset_span (Set.mem_insert_of_mem _ ⟨p, rfl⟩))

/-- **The selection.**  On an infinite-dimensional space, a self-adjoint family
admits arbitrarily long orthonormal sequences off any finite-dimensional
subspace whose cross terms all vanish. -/
theorem exists_orthogonal_selection {m : ℕ} (a : Fin m → (H →L[ℂ] H))
    (hsa : ∀ p, IsSelfAdjoint (a p)) (hH : ¬ FiniteDimensional ℂ H) :
    ∀ (k : ℕ) (V : Submodule ℂ H), FiniteDimensional ℂ V →
      ∃ ξ : Fin k → H, (∀ i, ‖ξ i‖ = 1) ∧ (∀ i, ξ i ∈ Vᗮ) ∧
        (∀ i j, i ≠ j → ⟪ξ i, ξ j⟫_ℂ = 0) ∧
        (∀ i j, i ≠ j → ∀ p, ⟪a p (ξ i), ξ j⟫_ℂ = 0) := by
  have htop : ¬ FiniteDimensional ℂ (⊤ : Submodule ℂ H) := by
    intro hfin
    exact hH (Submodule.topEquiv.finiteDimensional)
  intro k
  induction k with
  | zero =>
    intro V _
    exact ⟨Fin.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0,
      fun i ↦ i.elim0⟩
  | succ k ih =>
    intro V hV
    obtain ⟨x, -, hxV, hxnorm⟩ :=
      exists_norm_eq_one_mem_orthogonal (W := (⊤ : Submodule ℂ H)) (V := V) htop
    haveI : FiniteDimensional ℂ (selectionObstruction a V x) := inferInstance
    obtain ⟨ξ', hnorm', hmem', horth', hcross'⟩ :=
      ih (selectionObstruction a V x) inferInstance
    have hxperp : ∀ i, ⟪x, ξ' i⟫_ℂ = 0 := fun i ↦
      (Submodule.mem_orthogonal _ _).mp (hmem' i) x (mem_selectionObstruction a V x)
    have haperp : ∀ (p : Fin m) (i), ⟪a p x, ξ' i⟫_ℂ = 0 := fun p i ↦
      (Submodule.mem_orthogonal _ _).mp (hmem' i) (a p x)
        (apply_mem_selectionObstruction a V x p)
    refine ⟨Fin.cons x ξ', ?_, ?_, ?_, ?_⟩
    · refine Fin.cases ?_ ?_
      · rw [Fin.cons_zero]; exact hxnorm
      · intro i; rw [Fin.cons_succ]; exact hnorm' i
    · refine Fin.cases ?_ ?_
      · rw [Fin.cons_zero]; exact hxV
      · intro i
        rw [Fin.cons_succ]
        exact Submodule.orthogonal_le (le_selectionObstruction a V x) (hmem' i)
    · refine Fin.cases (fun j ↦ ?_) (fun i j ↦ ?_)
      · refine Fin.cases (fun h ↦ absurd rfl h) (fun j _ ↦ ?_) j
        rw [Fin.cons_zero, Fin.cons_succ]
        exact hxperp j
      · refine Fin.cases (fun _ ↦ ?_) (fun j hij ↦ ?_) j
        · rw [Fin.cons_zero, Fin.cons_succ, inner_eq_zero_symm]
          exact hxperp i
        · rw [Fin.cons_succ, Fin.cons_succ]
          exact horth' i j (fun h ↦ hij (by rw [h]))
    · refine Fin.cases (fun j ↦ ?_) (fun i j ↦ ?_)
      · refine Fin.cases (fun h ↦ absurd rfl h) (fun j _ p ↦ ?_) j
        rw [Fin.cons_zero, Fin.cons_succ]
        exact haperp p j
      · refine Fin.cases (fun _ p ↦ ?_) (fun j hij p ↦ ?_) j
        · rw [Fin.cons_zero, Fin.cons_succ]
          have hswap : ⟪a p (ξ' i), x⟫_ℂ = ⟪ξ' i, a p x⟫_ℂ := by
            rw [← ContinuousLinearMap.adjoint_inner_left,
              ← ContinuousLinearMap.star_eq_adjoint, (hsa p).star_eq]
          rw [hswap, inner_eq_zero_symm]
          exact haperp p i
        · rw [Fin.cons_succ, Fin.cons_succ]
          exact hcross' i j (fun h ↦ hij (by rw [h])) p

end

end ShulmanFill
end GroupApproximation
