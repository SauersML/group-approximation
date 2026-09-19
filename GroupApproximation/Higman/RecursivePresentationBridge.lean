import GroupApproximation.Higman.RelatorRE
import GroupApproximation.Higman.REPredNormalForm

/-!
# A recursive presentation *is* a presentation with enumerable relators

`Higman.RecursivePresentation` records a group by its *word problem*: a
generating family and recursive enumerability of the raw words that die.
Everything that builds new groups --- free products, HNN extensions --- works
instead with *relators*.  The two formulations are equivalent, and this file
supplies the direction that was missing, which is the one every construction
needs:

> a group with a spanning family and a recursively enumerable word problem is
> `PresentedGroup S` for a relator set `S` whose membership is a
> primitive-recursive search.

The relator set is simply the kernel of the evaluation map.  It is normal, so
it is its own normal closure and the presented group it defines is the
quotient; and membership in it *is* the word problem, so its enumerability is
the hypothesis.  Turning that enumerability into a search is
`Higman.exists_primrec_of_rePred`, the Kleene normal form.

With this and `Higman.recursivePresentationPresentedGroup` the two formulations
convert freely, which is what lets a `RecursivePresentation` hypothesis be
consumed by a construction that produces relators --- the composition that
input (4), `BridgeRecursive`, needs.
-/

namespace GroupApproximation
namespace Higman

variable {A : Type} [Group A]

/-! ## 1.  Evaluation factors through the free group -/

theorem lift_freeEval (gen : ℕ → A) (w : RawWord) :
    FreeGroup.lift gen (freeEval w) = evalRaw gen w := by
  unfold freeEval
  rw [map_evalRaw]
  simp only [FreeGroup.lift_apply_of]

theorem range_lift (gen : ℕ → A) :
    (FreeGroup.lift gen).range = Subgroup.closure (Set.range gen) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    obtain ⟨w, rfl⟩ :=
      (mem_closure_iff_exists_evalRaw FreeGroup.of x).1
        (by rw [FreeGroup.closure_range_of]; exact Subgroup.mem_top x)
    show FreeGroup.lift gen (freeEval w) ∈ _
    rw [lift_freeEval]
    exact evalRaw_mem_closure gen w
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨k, rfl⟩
    exact ⟨FreeGroup.of k, by simp⟩

theorem lift_surjective {gen : ℕ → A} (hspan : Subgroup.closure (Set.range gen) = ⊤) :
    Function.Surjective (FreeGroup.lift gen) := by
  rw [← MonoidHom.range_eq_top, range_lift, hspan]

/-! ## 2.  The kernel as a relator set -/

/-- The relator set of a group with a chosen generating family: the kernel of
the evaluation map. -/
def relatorSetOf (gen : ℕ → A) : Set (FreeGroup ℕ) :=
  (MonoidHom.ker (FreeGroup.lift gen) : Set (FreeGroup ℕ))

theorem mem_relatorSetOf (gen : ℕ → A) (w : RawWord) :
    freeEval w ∈ relatorSetOf gen ↔ evalRaw gen w = 1 := by
  show FreeGroup.lift gen (freeEval w) = 1 ↔ _
  rw [lift_freeEval]

theorem normalClosure_relatorSetOf (gen : ℕ → A) :
    Subgroup.normalClosure (relatorSetOf gen) = MonoidHom.ker (FreeGroup.lift gen) :=
  le_antisymm
    (Subgroup.normalClosure_le_normal (fun _ h => h))
    Subgroup.subset_normalClosure

/-- **The group is presented by its kernel.** -/
noncomputable def presentedGroupEquiv {gen : ℕ → A}
    (hspan : Subgroup.closure (Set.range gen) = ⊤) :
    PresentedGroup (relatorSetOf gen) ≃* A := by
  refine MulEquiv.trans ?_
    (QuotientGroup.quotientKerEquivOfSurjective _ (lift_surjective hspan))
  exact QuotientGroup.quotientMulEquivOfEq (normalClosure_relatorSetOf gen)

/-! ## 3.  The relator set is enumerable -/

/-- **A recursive presentation gives a presentation with an enumerable relator
set.**  The two formulations of "recursively presented" convert into one
another; this is the direction the constructions need. -/
theorem exists_enumerable_relators (P : RecursivePresentation A) :
    ∃ f : RawWord → ℕ → Bool, Primrec₂ f ∧
      (∀ v : RawWord,
        freeEval v ∈ relatorSetOf P.gen ↔ ∃ n, f v n = true) := by
  obtain ⟨f, hf, hspec⟩ := exists_primrec_of_rePred P.re
  refine ⟨f, hf, fun v => ?_⟩
  rw [mem_relatorSetOf]
  exact hspec v

/-- The symmetrized relator set is enumerable too, which is the form
`Higman.RelatorRE` consumes: a word lies in it exactly when it or its formal
inverse is a relator. -/
theorem symmetrize_relatorSetOf (gen : ℕ → A) (v : RawWord) :
    freeEval v ∈ symmetrize (relatorSetOf gen) ↔ evalRaw gen v = 1 := by
  constructor
  · rintro (hv | ⟨x, hx, hxv⟩)
    · exact (mem_relatorSetOf gen v).1 hv
    · have : freeEval v = x⁻¹ := hxv.symm
      have hx' : FreeGroup.lift gen x = 1 := hx
      show evalRaw gen v = 1
      rw [← lift_freeEval, this, map_inv, hx', inv_one]
  · intro hv
    exact Or.inl ((mem_relatorSetOf gen v).2 hv)

end Higman
end GroupApproximation
