import GroupApproximation.Manuscript.SimpleKazhdanSofic.HalflineB.Reduction
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFSolvableWordProblem
import GroupApproximation.Meta.AxiomGuard

/-!
# `lem:halfline` (b), in the printed form

`simple_kazhdan_sofic_group.tex`, `lem:halfline`, tex l.609–610:

> (b) The word problem of G_Δ is Turing reducible to that of Δ.

Here `G_Δ = EL_3(R_Δ)` with `R_Δ = LC(Ω, F_2) ⋊ Λ` (`lem:host`, tex l.527–532). In Lean this is
`elementaryGroup (Fin 3) (LampRing Δ)`.

The word problem of a finitely generated group does not depend on the finite generating family up to Turing
equivalence. So "the word problem of `G_Δ` is Turing reducible to that of `Δ`" is stated here for every finite family
`u` of elements of `G_Δ` and every finite generating family `s` of `Δ`.

## Proof route

`HalflineB.manuscriptSentence_hostWordProblemReduction` (tex l.657–665):

* a word in `u` multiplies out to a matrix of tables of monomials in the atoms `u_ξ e_U u_ξ⁻¹`;
* the word is trivial iff every collected coefficient of its difference from `I₃` vanishes at finitely many
  assignments of the variables;
* checking this only asks equalities in `Λ`, a truth-table reduction to the word problem of `Λ`, which reduces to the
  word problem of `Δ` (tex l.654–657).
-/

namespace GroupApproximation.Full.SK11

open GroupApproximation.SimpleKazhdanSofic GroupApproximation.SimpleKazhdanSofic.Lamplighter

/-- **`lem:halfline` (b)** (`simple_kazhdan_sofic_group.tex`, tex l.609–610). The word problem of
`G_Δ = EL_3(R_Δ)` is Turing reducible to that of `Δ`: for every finite generating family `s` of `Δ` and every finite
family `u` of elements of `G_Δ`, the word problem of `u` is Turing reducible to the word problem of `s`. -/
theorem halflineB (Δ : Type) [Group Δ] :
    ∀ (ι κ : Type) [Primcodable ι] [Finite ι] [Primcodable κ] [Finite κ] (s : ι → Δ)
      (u : κ → ↥(elementaryGroup (Fin 3) (LampRing Δ))),
      Subgroup.closure (Set.range s) = ⊤ → TuringReducible (wordProblemOracle u) (wordProblemOracle s) :=
  fun _ _ _ _ _ _ s u hs =>
    GroupApproximation.Manuscript.SimpleKazhdanSofic.HalflineB.manuscriptSentence_hostWordProblemReduction s hs u

#audit_axioms GroupApproximation.Full.SK11.halflineB

/-- **`lem:halfline` (b), solvable form** (tex l.609–610, together with the definition of solvable word problem).
If `Δ` has solvable word problem, then every finite family of elements of `G_Δ = EL_3(R_Δ)` has solvable word
problem. -/
theorem halflineB_solvable (Δ : Type) [Group Δ] (hWP : HasSolvableWordProblem Δ) (κ : Type) [Primcodable κ]
    [Finite κ] (u : κ → ↥(elementaryGroup (Fin 3) (LampRing Δ))) : Partrec (wordProblemOracle u) := by
  obtain ⟨ι, _, _, s, hs, hpart⟩ := hWP
  exact partrec_iff_forall_turingReducible.mpr fun _ =>
    TuringReducible.trans (halflineB Δ ι κ s u hs) hpart.turingReducible

#audit_axioms GroupApproximation.Full.SK11.halflineB_solvable

end GroupApproximation.Full.SK11
