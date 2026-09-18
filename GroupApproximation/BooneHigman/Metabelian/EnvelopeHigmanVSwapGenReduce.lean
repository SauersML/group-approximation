import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVGenReduce
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVSwapGenAll
import GroupApproximation.Meta.AxiomGuard

/-!
# Splitting the swap-section statement: generation (proved) and finite presentation

`HigmanVSwapSectionStatement` (`EnvelopeHigmanVGenReduce.lean`) asks for two things about a finite
family `g` of elements of `V_d` whose closure contains every cone swap:
* (A) `Subgroup.closure (Set.range g) = ⊤`;
* (B) a finite set of relators with a unital intertwining section.

Part (A) is proved in `EnvelopeHigmanVSwapGenAll.lean` (`swapGen_closure_eq_top`).  This file
isolates part (B).
* `SwapGenSectionStatement`: (B) for every finite generating family.  It gives the swap-section
  statement (`higmanVSwapSection_of_swapGen`) and follows from it
  (`swapGen_of_higmanVSwapSection`), so it is exactly the residue of that statement once generation
  is discharged.  It is strictly smaller in proof content: the generation of `V_d` by cone swaps is
  no longer part of it.
* `SwapGenShortSectionStatement`: (B) only for the explicit family `vgenShortSwaps (Fin d)` of
  short cone swaps.  It is logically weaker (`swapGenShort_of_swapGen`), and it already gives
  `HigmanVFinSectionStatement` (`higmanVFinSection_of_swapGenShort`).

*Truth.*  Both are true.  By Higman's theorem `V_d` is finitely presented.  For a finite
generating family `g`, the kernel of `FreeGroup.lift g` is then the normal closure of a finite
set `R` (B. H. Neumann), and the inverse `s` of the isomorphism `FreeGroup (Fin n) ⧸ ⟨⟨R⟩⟩ ≃* V_d`
satisfies `s 1 = 1` and `s (v * g i) = s v * of i`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **Part (B) for every finite generating family.** For `d ≥ 2`, every finite generating family of
`higmanThompsonV (Fin d)` has a finite set of relators carrying a unital intertwining section. -/
def SwapGenSectionStatement : Prop :=
  ∀ d : ℕ, 1 < d → ∀ (n : ℕ) (g : Fin n → ↥(higmanThompsonV (Fin d))),
    Subgroup.closure (Set.range g) = ⊤ →
      ∃ R : Set (FreeGroup (Fin n)), R.Finite ∧ R ⊆ (FreeGroup.lift g).ker ∧
        ∃ s : ↥(higmanThompsonV (Fin d)) → FreeGroup (Fin n) ⧸ Subgroup.normalClosure R,
          s 1 = 1 ∧
            ∀ (v : ↥(higmanThompsonV (Fin d))) (i : Fin n),
              s v * ((FreeGroup.of i : FreeGroup (Fin n)) :
                FreeGroup (Fin n) ⧸ Subgroup.normalClosure R) = s (v * g i)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.SwapGenSectionStatement

/-- **The split.** Part (B) for generating families, together with the proved generation of
`V_d` by cone swaps, gives the swap-section statement. -/
theorem higmanVSwapSection_of_swapGen (h : SwapGenSectionStatement) :
    HigmanVSwapSectionStatement := by
  intro d hd n g hg
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr hd
  have htop : Subgroup.closure (Set.range g) = ⊤ := swapGen_closure_eq_top hg
  exact ⟨htop, h d hd n g htop⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVSwapSection_of_swapGen

/-- Conversely, the swap-section statement gives part (B) for generating families. -/
theorem swapGen_of_higmanVSwapSection (h : HigmanVSwapSectionStatement) :
    SwapGenSectionStatement := by
  intro d hd n g hg
  exact (h d hd n g fun v w h1 h2 => by
    rw [hg]
    exact Subgroup.mem_top _).2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.swapGen_of_higmanVSwapSection

/-- **Part (B) for the short cone swaps only.** For `d ≥ 2`, the explicit family
`vgenShortSwaps (Fin d)` has a finite set of relators carrying a unital intertwining section. -/
def SwapGenShortSectionStatement : Prop :=
  ∀ d : ℕ, 1 < d →
    ∃ R : Set (FreeGroup (Fin (Nat.card ↥(vgenShortPairs (Fin d))))), R.Finite ∧
      R ⊆ (FreeGroup.lift (vgenShortSwaps (Fin d))).ker ∧
        ∃ s : ↥(higmanThompsonV (Fin d)) →
            FreeGroup (Fin (Nat.card ↥(vgenShortPairs (Fin d)))) ⧸ Subgroup.normalClosure R,
          s 1 = 1 ∧
            ∀ (v : ↥(higmanThompsonV (Fin d))) (i : Fin (Nat.card ↥(vgenShortPairs (Fin d)))),
              s v * ((FreeGroup.of i : FreeGroup (Fin (Nat.card ↥(vgenShortPairs (Fin d))))) :
                FreeGroup (Fin (Nat.card ↥(vgenShortPairs (Fin d)))) ⧸
                  Subgroup.normalClosure R) = s (v * vgenShortSwaps (Fin d) i)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.SwapGenShortSectionStatement

/-- The short cone swaps generate `V_d`. -/
theorem swapGen_shortSwaps_closure_eq_top (d : ℕ) (hd : 1 < d) :
    Subgroup.closure (Set.range (vgenShortSwaps (Fin d))) = ⊤ := by
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr hd
  exact swapGen_closure_eq_top fun _ _ h1 h2 => vgenShortSwaps_closure h1 h2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.swapGen_shortSwaps_closure_eq_top

/-- Part (B) for generating families gives part (B) for the short cone swaps. -/
theorem swapGenShort_of_swapGen (h : SwapGenSectionStatement) :
    SwapGenShortSectionStatement :=
  fun d hd => h d hd _ (vgenShortSwaps (Fin d)) (swapGen_shortSwaps_closure_eq_top d hd)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.swapGenShort_of_swapGen

/-- Part (B) for the short cone swaps gives the normal-form section statement. -/
theorem higmanVFinSection_of_swapGenShort (h : SwapGenShortSectionStatement) :
    HigmanVFinSectionStatement :=
  fun d hd => ⟨_, vgenShortSwaps (Fin d), swapGen_shortSwaps_closure_eq_top d hd, h d hd⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVFinSection_of_swapGenShort

end GroupApproximation.BooneHigman.Metabelian.Envelope
