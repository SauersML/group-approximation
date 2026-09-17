import GroupApproximation.Manuscript.SimpleKazhdanSofic.LamplighterWP.Reduction
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LamplighterWP.Generation
import GroupApproximation.Meta.AxiomGuard

/-!
# `lem:halfline` (b): the word problem of `G_Δ` is Turing reducible to that of `Δ`

`simple_kazhdan_sofic_group.tex`, `lem:halfline`, l.609–610:

> \textup{(b)} The word problem of $G_\Delta$ is Turing reducible to that of $\Delta$.

and `cor:lef`, proof of the second statement, l.448–455 (`Lamplighter.PrintedLamplighterHostSolvableWordProblem`):
if `Δ` has solvable word problem then so has `G_Δ = EL_3(LC(Ω, F_2) ⋊ Λ)`.

## Proof route

* Spelling (as in `HalflineA/WordProblemReduction.lean`): the word problem of a finite family `s` is
  `wordProblemOracle s`, and "Turing reducible" is `TuringReducible`. The statement is made for every finite
  generating family `t` of `Δ` and every finite family `s` of `G_Δ`, together with the existence of a finite
  generating family of `G_Δ` (`hostGen t`, `closure_range_hostGen`).
* A word in `s` is trivial in `G_Δ` iff it is trivial in `(M₃(R_Δ))ˣ` (`wordProblemOracle_comp_injective`), and
  for families of units the truth-table reduction of `LamplighterWP.Reduction` gives
  `WP(v) ≤_T WP(Λ) ≤_T WP(Δ)` (`unitsReduction`).
* Solvable means reducible to a computable oracle (`partrec_iff_forall_turingReducible`), so `hostProof` follows.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace LamplighterWP

open Lamplighter

/-- **`lem:halfline` (b)** (tex l.609–610): for every finite generating family `t` of `Δ`, the group
`G_Δ = EL_3(R_Δ)` has a finite generating family, and the word problem of every finite family of `G_Δ` is Turing
reducible to the word problem of `Δ` in `t`. -/
theorem manuscriptSentence_halflineHostWordProblemReduction (Δ : Type) [Group Δ]
    (ι : Type) [Primcodable ι] [Finite ι] (t : ι → Δ) (ht : Subgroup.closure (Set.range t) = ⊤) :
    (∃ (κ : Type) (_ : Primcodable κ) (_ : Finite κ) (s : κ → ↥(elementaryGroup (Fin 3) (LampRing Δ))),
      Subgroup.closure (Set.range s) = ⊤) ∧
    ∀ (κ : Type) [Primcodable κ] [Finite κ] (s : κ → ↥(elementaryGroup (Fin 3) (LampRing Δ))),
      TuringReducible (wordProblemOracle s) (wordProblemOracle t) := by
  refine ⟨⟨HGen ι, inferInstance, inferInstance, hostGen t, closure_range_hostGen t ht⟩, fun κ _ _ s => ?_⟩
  rw [← wordProblemOracle_comp_injective s (elementaryGroup (Fin 3) (LampRing Δ)).subtype
    (elementaryGroup (Fin 3) (LampRing Δ)).subtype_injective]
  exact unitsReduction t ht _

#audit_axioms GroupApproximation.SimpleKazhdanSofic.LamplighterWP.manuscriptSentence_halflineHostWordProblemReduction

/-- **`G_Δ` has solvable word problem when `Δ` has** (tex l.448–455). -/
theorem hostProof : Lamplighter.PrintedLamplighterHostSolvableWordProblem := by
  intro Δ _ hΔ
  obtain ⟨ι, _, _, t, ht, hpart⟩ := hΔ
  obtain ⟨⟨κ, _, _, s, hs⟩, hred⟩ := manuscriptSentence_halflineHostWordProblemReduction Δ ι t ht
  exact ⟨κ, inferInstance, inferInstance, s, hs, partrec_iff_forall_turingReducible.mpr fun o =>
    (hred κ s).trans (partrec_iff_forall_turingReducible.mp hpart o)⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.LamplighterWP.hostProof

end LamplighterWP
end SimpleKazhdanSofic
end GroupApproximation
