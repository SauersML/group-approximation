import GroupApproximation.Analysis.NaturalMatrixCoordinateEquiv
import GroupApproximation.Sofic.HyperlinearScalar
import GroupApproximation.Sofic.UltrafilterSubsequence

/-!
# The printed opening of `thm:kazhdan-transport`, where the proof can consume it

The printed proof of `\label{thm:kazhdan-transport}` begins by contradiction:

> Suppose the conclusion fails: there are `γ₀ ∈ Γ`, `δ > 0`, and an infinite set
> `I ⊆ ℕ` with `‖[Uₙ(s)xₙUₙ(s)*, Uₙ(ι(γ₀))]‖₂ ≥ δ` for `n ∈ I`.  Fix a free
> ultrafilter `ω` on `ℕ` with `I ∈ ω`.

`Sofic/KazhdanTransportFailureExtraction.lean` already states that sentence at
the printed objects, and ledger row `KT.01` records why stating it was not
enough: that file sits *above* the transport proof in the import graph, because
it spells the hypothesis with `NaturalHSCommutatorVanishing`, which
`Sofic/ManuscriptKazhdanTransport.lean` defines.  So the printed opening could
be read but not used, and the badged proof reached the same conclusion by a
different route.

This module is the same sentence spelled without that predicate — the
hypothesis is the negation written out, which is what the predicate unfolds to —
so it sits *below* `Sofic/UltraproductKazhdanTransport.lean` and the printed
proof can consume it.  `KazhdanTransportFailureExtraction` now derives its
statement from this one, so there is one proof and not two.

## What the pigeonhole is doing here

`UltrafilterSubsequence.exists_index_infinite_defect` proves the extraction for
an arbitrary finite index set, with a pigeonhole choosing the offending index.
The conclusion of `thm:kazhdan-transport` is universally quantified over `Γ`, so
its failure names a single `γ₀` and there is nothing to choose between: the
instantiation below is at the singleton `{γ₀}`, and the pigeonhole is trivial.
The finite Kazhdan set and its genuine pigeonhole belong to the spectral-gap
step, where finiteness of `S` is what bounds the constant.
-/

namespace GroupApproximation
namespace PrintedTransportOpening

open Filter Topology Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

variable {Γ : Type} [Group Γ] {H : Type u} [Group H]

/-- **The printed opening, at the printed objects and below the proof.**

The hypothesis is the negation of the theorem's own conclusion, written out; the
defect is the printed one, the normalized Hilbert--Schmidt norm of the commutator
of the conjugated sequence `Uₙ(s) xₙ Uₙ(s)*` with `Uₙ(ι γ₀)`. -/
theorem exists_gamma_infinite_commutator_defect
    (d : ℕ → ℕ)
    (U : ∀ n, H → Matrix.unitaryGroup (naturalFiniteModel (d n)) ℂ)
    (x : ∀ n, Matrix (naturalFiniteModel (d n)) (naturalFiniteModel (d n)) ℂ)
    (iota : Γ →* H) (s : H)
    (hfail : ¬ ∀ γ : Γ, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
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
                  (naturalFiniteModel (d n)) ℂ)ᴴ))) ≤ ε) :
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
  -- The conclusion is universally quantified, so its failure names `γ₀`.  The
  -- negation is taken one step only: pushed further it would dissolve the
  -- inner statement, which is the one the singleton extraction consumes.
  obtain ⟨γ₀, hγ⟩ := not_forall.mp hfail
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

end PrintedTransportOpening
end GroupApproximation
