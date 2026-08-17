import GroupApproximation.Algebra.AlternatingBoundedNormalGeneration
import Mathlib.Logic.Equiv.Fintype

/-!
# The production half of `hBNG`, with the density hypothesis in front

`Algebra/AlternatingBoundedNormalGeneration.lean` proves that a permutation
supported inside an `s`-independent set `A` is doubled by one commutator with
`s`, and that the resulting cycle type is therefore reachable in two
conjugates.  Both statements name `A`.

This file removes `A` from the statement.  What is left is the form the
premise `hBNG` of proof-ledger row `SO.17` would consume: a hypothesis
comparing the support of the target's half with the support of `s`, and no
mention of how the independent set was found.

> If `3|supp g| ≤ |supp s|`, then every permutation whose cycle type is
> `g.cycleType + g.cycleType` is a product of at most two conjugates of `s`
> and `s⁻¹`.

The constant `3` is the greedy bound of `exists_independent_subset` and is not
claimed to be optimal; only its independence of everything else matters, since
`|supp s| ≥ δ|Ω|` then makes the reachable supply a fixed fraction of the whole
model.  **This is still only the production half**: the consumption count —
how many such doubled elements an arbitrary even permutation needs — is not
proved anywhere, and `hBNG` therefore remains a premise.  See the module
docstring of `Algebra/AlternatingBoundedNormalGeneration.lean` for the precise
statement of what is missing.
-/

namespace GroupApproximation
namespace AlternatingBoundedNormalGeneration

open BoundedConjProductAlgebra SoficEnvelopeSimplicity

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- A permutation can be conjugated so that its support lands inside any
finset at least as large as that support.  The conjugator is the extension to
all of `Y` of a bijection from the support onto a subset of the target of the
same size. -/
theorem exists_conj_support_subset (g : Equiv.Perm Y) {B : Finset Y}
    (hcard : g.support.card ≤ B.card) :
    ∃ c : Equiv.Perm Y, (c * g * c⁻¹).support ⊆ B := by
  obtain ⟨B', hB'sub, hB'card⟩ := Finset.exists_subset_card_eq hcard
  let e : {x // x ∈ g.support} ≃ {x // x ∈ B'} :=
    g.support.equivFin.trans ((finCongr hB'card.symm).trans B'.equivFin.symm)
  refine ⟨e.extendSubtype, ?_⟩
  rw [Equiv.Perm.support_conj]
  intro z hz
  obtain ⟨y, hy, hyz⟩ := Finset.mem_map.mp hz
  have hmem : e.extendSubtype y ∈ B' := Equiv.extendSubtype_mem e y hy
  rw [show e.extendSubtype y = z from hyz] at hmem
  exact hB'sub hmem

/-- **The production half of bounded normal generation.**  If the target's
half-support is at most a third of `|supp s|`, then every permutation of that
doubled cycle type is a product of at most two conjugates of `s` and `s⁻¹`.

No hypothesis on `s` beyond the support comparison: `s` need not be even, need
not be a cycle, and the model's size never appears.  The length `2` is
absolute. -/
theorem isBoundedConjProduct_two_of_cycleType_doubled {s g : Equiv.Perm Y}
    (hcard : 3 * g.support.card ≤ s.support.card) {z : Equiv.Perm Y}
    (hz : z.cycleType = g.cycleType + g.cycleType) :
    IsBoundedConjProduct s 2 z := by
  obtain ⟨A, _hAsub, hAind, hAcard⟩ := exists_independent_subset s
  have hfit : g.support.card ≤ A.card := by omega
  obtain ⟨c, hc⟩ := exists_conj_support_subset g hfit
  refine isBoundedConjProduct_two_of_cycleType_eq hAind hc ?_
  rw [Equiv.Perm.cycleType_conj]
  exact hz

end AlternatingBoundedNormalGeneration
end GroupApproximation
