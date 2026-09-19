import GroupApproximation.CharClass.CartanEvalMor
import GroupApproximation.CharClass.CartanComparison

/-!
# The two composites, evaluated against `α ⊗ β ⊗ α ⊗ β`

The comparison says the two composites differ by a homotopy.  Evaluating the
functional kills two of the three terms: the `d ∘ s` term because the functional
annihilates boundaries, and the `1 + t` half of the source differential because
the functional is linear over the group ring into a module with trivial action
and `2 = 0`.  What is left is a single term, and it is the coboundary.

The source differential on a generator is `(1 + t)·(e_{n-1} ⊗ σ) + e_n ⊗ ∂σ`.
`wDiffWitness` names the first summand's witness, so that the split the
comparison wants is available on the nose rather than up to a rearrangement.

## Main results

* `wDiff_single_split` — the source differential on a generator, split.
* `fourEval_compA_eq_compB` — **the master identity**.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

/-! ## 1. The source differential, split -/

/-- The witness of the `1 + t` half of the source differential: the same simplex
one `W`-index down, and nothing at all when the index is already `0`. -/
noncomputable def wDiffWitness (X : TopCat.{0}) (k : ℕ) :
    ∀ n : Fin (k + 2), (stdSimplexTop n.val ⟶ X) → WTensorSMod X k :=
  Fin.lastCases (motive := fun n : Fin (k + 2) => (stdSimplexTop n.val ⟶ X) → WTensorSMod X k)
    (fun _ => 0)
    (fun j σ => Finsupp.single (⟨j, σ⟩ : WSIndex k X) (1 : GroupRingZ2))

@[simp] theorem wDiffWitness_last (X : TopCat.{0}) (k : ℕ)
    (σ : stdSimplexTop (Fin.last (k + 1)).val ⟶ X) :
    wDiffWitness X k (Fin.last (k + 1)) σ = 0 := by
  rw [wDiffWitness, Fin.lastCases_last]

@[simp] theorem wDiffWitness_castSucc (X : TopCat.{0}) (k : ℕ) (j : Fin (k + 1))
    (σ : stdSimplexTop (Fin.castSucc j).val ⟶ X) :
    wDiffWitness X k (Fin.castSucc j) σ
      = Finsupp.single (⟨j, σ⟩ : WSIndex k X) (1 : GroupRingZ2) := by
  rw [wDiffWitness, Fin.lastCases_castSucc]

theorem wDiffW_eq_smul (X : TopCat.{0}) (k : ℕ) (n : Fin (k + 2)) :
    ∀ σ : stdSimplexTop n.val ⟶ X,
      wDiffW X k n σ = (1 + groupRingGen) • wDiffWitness X k n σ := by
  induction n using Fin.lastCases with
  | last =>
      intro σ
      rw [wDiffW_last, wDiffWitness_last, smul_zero]
  | cast j =>
      intro σ
      rw [wDiffW_castSucc, wDiffWitness_castSucc]

/-- **The source differential on a generator, split** into the `1 + t` half and
the simplicial half. -/
theorem wDiff_single_split (data : SingularBoundaryData) (X : TopCat.{0}) (k : ℕ)
    (n : Fin (k + 2)) (σ : stdSimplexTop n.val ⟶ X) :
    wDiff data X k (Finsupp.single (⟨n, σ⟩ : WSIndex (k + 1) X) (1 : GroupRingZ2))
      = (1 + groupRingGen) • wDiffWitness X k n σ + wDiffS data X k n σ := by
  rw [wDiff_single]
  show wDiffW X k n σ + wDiffS data X k n σ = _
  rw [wDiffW_eq_smul X k n σ]

/-! ## 2. The master identity -/

variable (compB : src singularBoundary ⟶ four)
variable (hzero : ∀ X : TopCat.{0}, (compA.app X).f 0 = (compB.app X).f 0)

/-- **The master identity.**  Evaluated against `α ⊗ β ⊗ α ⊗ β` for a pair of
cocycles, the two composites differ on a generator by exactly one term: the
homotopy applied to the simplicial half of the differential.  As a function of
the simplex that term is a coboundary, which is what makes the two cochains
cohomologous. -/
theorem fourEval_compA_eq_compB (X : TopCat.{0}) (p q : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    (hα : cochainCoboundary (ZMod 2) X p α = 0)
    (hβ : cochainCoboundary (ZMod 2) X q β = 0)
    (n : ℕ) (i : Fin (n + 2)) (σ : stdSimplexTop i.val ⟶ X) :
    fourEvalF2 X p q α β (n + 1)
        (((compA.app X).f (n + 1)).hom
          (Finsupp.single (⟨i, σ⟩ : WSIndex (n + 1) X) (1 : GroupRingZ2)))
      = fourEvalF2 X p q α β (n + 1)
          (((compB.app X).f (n + 1)).hom
            (Finsupp.single (⟨i, σ⟩ : WSIndex (n + 1) X) (1 : GroupRingZ2)))
        + fourEvalF2 X p q α β (n + 1)
            (((cartanHomotopy compB hzero).s n X).hom
              (wDiffS singularBoundary X n i σ)) := by
  have hx : (((src singularBoundary).obj X).d (n + 1) n).hom
        (Finsupp.single (⟨i, σ⟩ : WSIndex (n + 1) X) (1 : GroupRingZ2))
      = (1 + groupRingGen) • wDiffWitness X n i σ + wDiffS singularBoundary X n i σ := by
    show ((srcComplex singularBoundary X).d (n + 1) n).hom _ = _
    rw [srcComplex_d]
    exact wDiff_single_split singularBoundary X n i σ
  have h := cartan_eval compB hzero X n (fourEvalMor X p q α β (n + 1))
    (fourEvalMor_comp_d X p q α β hα hβ n) trivialCoeffMod_gen_smul
    (Finsupp.single (⟨i, σ⟩ : WSIndex (n + 1) X) (1 : GroupRingZ2))
    (wDiffWitness X n i σ) (wDiffS singularBoundary X n i σ) hx
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply, ModuleCat.comp_apply] at h
  exact h

end

end GroupApproximation.CharClass
