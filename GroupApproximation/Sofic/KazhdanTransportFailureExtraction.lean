import GroupApproximation.Sofic.ManuscriptKazhdanTransport
import GroupApproximation.Sofic.PrintedTransportOpening
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

## The step is now consumed

It was not, when this file was written, and the reason was structural rather
than mathematical.  The hypothesis here is spelled with
`NaturalHSCommutatorVanishing`, which `Sofic/ManuscriptKazhdanTransport.lean`
defines, so this file sits *above* the transport proof in the import graph and
the printed opening could be read but not used.

`Sofic/PrintedTransportOpening.lean` is the same sentence with that hypothesis
written out instead — which is what the predicate unfolds to — so it sits below
`Sofic/UltraproductKazhdanTransport.lean`, and `ultraproductKazhdanTransport`
now opens with it.  The statement below is that one re-spelled with the
predicate, so there is one proof and not two.
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
                  (naturalFiniteModel (d n)) ℂ)ᴴ)))}.Infinite :=
  PrintedTransportOpening.exists_gamma_infinite_commutator_defect d U x iota s
    hfail

end

end KazhdanTransportFailureExtraction
end GroupApproximation
