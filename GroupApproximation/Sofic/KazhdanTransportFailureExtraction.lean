import GroupApproximation.Sofic.ManuscriptKazhdanTransport
import GroupApproximation.Sofic.UltrafilterSubsequence

/-!
# The opening move of `thm:kazhdan-transport`, at the printed objects

The printed proof begins

> Suppose the conclusion fails: there are `γ₀ ∈ Γ`, `δ > 0`, and an infinite set
> `I ⊆ ℕ` with `‖[Uₙ(s)xₙUₙ(s)*, Uₙ(ι(γ₀))]‖₂ ≥ δ` for `n ∈ I`.

Ledger row `KT.01` grades that MISMATCH over **substituted** objects, and its
note says exactly why: `UltrafilterSubsequence.exists_index_infinite_defect`
proves the extraction "for an arbitrary finite index set and an arbitrary real
defect `f n γ`, not instantiated at the printed commutator".

This file instantiates it.  `exists_gamma_infinite_commutator_defect` is the
printed sentence with the printed quantities in it: the group element is an
element of `Γ`, and the defect is the normalized Hilbert--Schmidt norm of the
commutator of the conjugated sequence with `Uₙ(ι(γ₀))`, which is what the
theorem's conclusion is about.

## Where the pigeonhole went

The general lemma's finite index set and its pigeonhole are not needed here, and
the note is worth reading with that in mind.  The conclusion of
`thm:kazhdan-transport` is universally quantified over `Γ`, so its failure hands
over a single `γ₀` with nothing to choose between — the finite Kazhdan set and
the pigeonhole belong to a *different* step, the spectral gap, where finiteness
of `S` is what bounds the constant.  Instantiating at a singleton is therefore
not a weakening of the general lemma but the shape the printed sentence actually
has.

## What this does not do

It does not make the step *consumed*.  The Lean transport proof runs directly
rather than by contradiction, so this is the printed opening available as a
declaration, not the route the badged theorem travels — exactly as the row's
note records for the proof column.
-/

namespace GroupApproximation
namespace KazhdanTransportFailureExtraction

open Filter Topology Matrix
open KazhdanAsymptoticCommutant
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

variable {Γ : Type} [Group Γ] {H : Type u} [Group H]

/-- **`KT.01`, at the printed objects.**

> Suppose the conclusion fails: there are `γ₀ ∈ Γ`, `δ > 0`, and an infinite set
> `I ⊆ ℕ` with the commutator norm at least `δ` on `I`.

The hypothesis is the negation of the theorem's own conclusion, and the defect
is the printed one: the normalized Hilbert--Schmidt norm of the commutator of
the conjugated sequence `Uₙ(s) xₙ Uₙ(s)*` with `Uₙ(ι γ₀)`. -/
theorem exists_gamma_infinite_commutator_defect
    (d : ℕ → ℕ)
    (U : ∀ n, H → Matrix.unitaryGroup (naturalFiniteModel (d n)) ℂ)
    (x : ∀ n, Matrix (naturalFiniteModel (d n)) (naturalFiniteModel (d n)) ℂ)
    (iota : Γ →* H) (s : H)
    (hfail : ¬ ∀ γ : Γ, NaturalHSCommutatorVanishing d U (fun n ↦
      (U n s : Matrix (naturalFiniteModel (d n))
        (naturalFiniteModel (d n)) ℂ) * x n *
        (U n s : Matrix (naturalFiniteModel (d n))
          (naturalFiniteModel (d n)) ℂ)ᴴ) (iota γ)) :
    ∃ γ₀ : Γ, ∃ δ : ℝ, 0 < δ ∧
      {n : ℕ | δ ≤ Real.sqrt (hsNormSq (naturalFiniteModel (d n))
        (((U n s : Matrix (naturalFiniteModel (d n))
            (naturalFiniteModel (d n)) ℂ) * x n *
            (U n s : Matrix (naturalFiniteModel (d n))
              (naturalFiniteModel (d n)) ℂ)ᴴ) *
              (U n (iota γ₀) : Matrix (naturalFiniteModel (d n))
                (naturalFiniteModel (d n)) ℂ) -
            (U n (iota γ₀) : Matrix (naturalFiniteModel (d n))
              (naturalFiniteModel (d n)) ℂ) *
              ((U n s : Matrix (naturalFiniteModel (d n))
                (naturalFiniteModel (d n)) ℂ) * x n *
                (U n s : Matrix (naturalFiniteModel (d n))
                  (naturalFiniteModel (d n)) ℂ)ᴴ)))}.Infinite := by
  classical
  -- The conclusion is universally quantified, so its failure names `γ₀`.
  push Not at hfail
  obtain ⟨γ₀, hγ⟩ := hfail
  refine ⟨γ₀, ?_⟩
  -- What is left is the printed `δ` and the infinite set, which is the general
  -- extraction at the singleton `{γ₀}`.
  have hsing : ¬ ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ γ ∈ ({γ₀} : Finset Γ),
      Real.sqrt (hsNormSq (naturalFiniteModel (d n))
        (((U n s : Matrix (naturalFiniteModel (d n))
            (naturalFiniteModel (d n)) ℂ) * x n *
            (U n s : Matrix (naturalFiniteModel (d n))
              (naturalFiniteModel (d n)) ℂ)ᴴ) *
              (U n (iota γ) : Matrix (naturalFiniteModel (d n))
                (naturalFiniteModel (d n)) ℂ) -
            (U n (iota γ) : Matrix (naturalFiniteModel (d n))
              (naturalFiniteModel (d n)) ℂ) *
              ((U n s : Matrix (naturalFiniteModel (d n))
                (naturalFiniteModel (d n)) ℂ) * x n *
                (U n s : Matrix (naturalFiniteModel (d n))
                  (naturalFiniteModel (d n)) ℂ)ᴴ))) ≤ ε := by
    intro hall
    refine hγ fun ε hε ↦ ?_
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hall ε hε)
    exact ⟨N, fun n hn ↦ hN n hn γ₀ (Finset.mem_singleton_self γ₀)⟩
  obtain ⟨γ₁, hγ₁, δ, hδ, hinf⟩ :=
    UltrafilterSubsequence.exists_index_infinite_defect ({γ₀} : Finset Γ) _ hsing
  rw [Finset.mem_singleton] at hγ₁
  subst hγ₁
  exact ⟨δ, hδ, hinf⟩

end

end KazhdanTransportFailureExtraction
end GroupApproximation
