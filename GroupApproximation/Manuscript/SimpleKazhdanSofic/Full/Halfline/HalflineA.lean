import GroupApproximation.Manuscript.SimpleKazhdanSofic.HalflineA.Embedding
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFSolvableWordProblem
import GroupApproximation.Meta.AxiomGuard

/-!
# `lem:halfline` (a), in the printed form

`simple_kazhdan_sofic_group.tex`, `lem:halfline`, tex l.606–608:

> (a) Every finitely generated LEF group Γ is a subgroup of [Δ,Δ] for an infinite finitely generated LEF group Δ
> whose word problem is Turing reducible to that of Γ.

The word problem of a finitely generated group does not depend on the finite generating family up to Turing
equivalence (`turingReducible_wordProblemOracle_of_generates`). So "the word problem of Δ is Turing reducible to that
of Γ" is stated here for every finite family `t` of elements of `Δ` and every finite generating family `s` of `Γ`.

## Proof route

* Pick a generating family `s₀ : Fin n → Γ` (`exists_fin_generators`).
* `HalflineA.manuscriptSentence_halflineEmbedding` builds `Δ = ⟨β, h_γ⟩ ≤ Perm (Γ × ℤ)` from `s₀`. It gives: `Δ` is
  infinite, finitely generated and LEF, `Γ` embeds in `[Δ, Δ]`, and the word problem of every finite family of `Δ`
  reduces to the word problem of `s₀`.
* For any other finite generating family `s` of `Γ`, the word problem of `s₀` reduces to that of `s`.
-/

namespace GroupApproximation.Full.SK11

open GroupApproximation.SimpleKazhdanSofic

/-- **`lem:halfline` (a)** (`simple_kazhdan_sofic_group.tex`, tex l.606–608). Every finitely generated LEF group `Γ`
embeds, by an injective homomorphism, in the commutator subgroup `[Δ, Δ]` of an infinite finitely generated LEF group
`Δ`. The word problem of `Δ` is Turing reducible to that of `Γ`: for every finite family `t` of elements of `Δ` and
every finite generating family `s` of `Γ`, the word problem of `t` is Turing reducible to the word problem of `s`. -/
theorem halflineA (Γ : Type) [Group Γ] (hfg : Group.FG Γ) (hLEF : IsLEF Γ) :
    ∃ (Δ : Type) (_ : Group Δ), Infinite Δ ∧ Group.FG Δ ∧ IsLEF Δ ∧
      (∃ f : Γ →* Δ, Function.Injective f ∧ ∀ γ, f γ ∈ commutator Δ) ∧
      ∀ (ι κ : Type) [Primcodable ι] [Finite ι] [Primcodable κ] [Finite κ] (s : ι → Γ) (t : κ → Δ),
        Subgroup.closure (Set.range s) = ⊤ → TuringReducible (wordProblemOracle t) (wordProblemOracle s) := by
  obtain ⟨n, s₀, hs₀⟩ := exists_fin_generators Γ hfg
  obtain ⟨Δ, instΔ, hinf, hfgΔ, hlefΔ, hemb, -, hred⟩ :=
    HalflineA.manuscriptSentence_halflineEmbedding Γ (Fin n) s₀ hs₀ hLEF
  refine ⟨Δ, instΔ, hinf, hfgΔ, hlefΔ, hemb, fun _ κ _ _ _ _ s t hs => ?_⟩
  exact TuringReducible.trans (hred κ t) (turingReducible_wordProblemOracle_of_generates hs s₀)

#audit_axioms GroupApproximation.Full.SK11.halflineA

/-- **`lem:halfline` (a), solvable form** (tex l.606–608, together with the definition of solvable word problem).
If `Γ` is a finitely generated LEF group with solvable word problem, then `Γ` embeds in `[Δ, Δ]` for an infinite
finitely generated LEF group `Δ` with solvable word problem. -/
theorem halflineA_solvable (Γ : Type) [Group Γ] (hfg : Group.FG Γ) (hLEF : IsLEF Γ)
    (hWP : HasSolvableWordProblem Γ) :
    ∃ (Δ : Type) (_ : Group Δ), Infinite Δ ∧ Group.FG Δ ∧ IsLEF Δ ∧
      (∃ f : Γ →* Δ, Function.Injective f ∧ ∀ γ, f γ ∈ commutator Δ) ∧ HasSolvableWordProblem Δ := by
  obtain ⟨ι, _, _, s, hs, hpart⟩ := hWP
  obtain ⟨Δ, instΔ, hinf, hfgΔ, hlefΔ, hemb, hred⟩ := halflineA Γ hfg hLEF
  obtain ⟨m, t, ht⟩ := exists_fin_generators Δ hfgΔ
  refine ⟨Δ, instΔ, hinf, hfgΔ, hlefΔ, hemb, Fin m, inferInstance, inferInstance, t, ht, ?_⟩
  exact partrec_iff_forall_turingReducible.mpr fun _ =>
    TuringReducible.trans (hred ι (Fin m) s t hs) hpart.turingReducible

#audit_axioms GroupApproximation.Full.SK11.halflineA_solvable

end GroupApproximation.Full.SK11
