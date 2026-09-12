import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.IntegralDomain
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import GroupApproximation.Meta.AxiomGuard

/-!
# The printed answer group `k^×/(k^×)^{d-1}`, and its two printed evaluations

`non_mf_groups_exist.tex`, the two sentences that follow
`cor:leavitt-mf-quotient` (tex lines 1320--1322):

> For `d=2` the quotient is trivial for every countable field `k`, so every
> homomorphism from `L_k(1,2)^×` to an MF group is trivial.

> For `k=𝔽_q` the quotient is cyclic of order `gcd(q-1,d-1)`.

Both sentences evaluate the *same* group, the one `cor:leavitt-mf-quotient`
names as the answer:

    `Q(k,d) = k^× / (k^×)^{d-1}`.

This module computes `Q(k,d)` at the two printed specialisations, for every
field, with no Leavitt input at all: nothing here mentions `L_k(1,d)`, `K₁`, or
any citation.  It is pure abelian-group arithmetic about
`(powMonoidHom m : kˣ →* kˣ).range`, the subgroup the rest of the development
already uses (`Manuscript/OneSidedMFRadical/LeavittKOneFormula.unitPowSubgroup`
is that subgroup at `m = d - 1`).

## Why this is worth a module of its own

The census (`metadata/NON_MF_SENTENCE_MAP.tsv`, row `6d3ca647302e`) records the
first sentence as carried and the second as an admitted gap:

> Second clause (k=F_q, quotient cyclic of order gcd(q-1,d-1), general d) is
> still not covered ... Remains a real, separate gap, not a landing-status one.

The gap has two halves, and they are independent.  One is the *identification*
of `H/EL_d(R)` with `Q(k,d)`, i.e. the Khanh--Thanh half of
`cor:leavitt-mf-quotient`.  The other is the *evaluation* of `Q(k,d)` at a finite
field, which is what this module closes.  Nothing here asserts the
identification, and nothing here depends on it.

Both halves are now closed.  The identification is
`LeavittKOneFormulaSentences.manuscriptLeavittKOneFormula`, from
`KhanhThanhDiagonal.scalarSurjective_holds` and `LeavittKOneFormula.scalarKernel`,
and `LeavittKOneQuotientEvaluations` composes it with this module, so both printed
sentences hold at the printed quotient of `L_k(1,d)`.

## What is proved

* `subsingleton_quotient_powMonoidHom_one` --- `G/G¹` is trivial for every
  abelian group, so `Q(k,2)` is trivial for every field: the arithmetic clause
  of the `d = 2` sentence.
* `isCyclic_quotient_powMonoidHom_range` and
  `card_quotient_powMonoidHom_range` --- a quotient of a finite cyclic group by
  its `m`-th powers is cyclic of order `gcd(|G|, m)`.  Mathlib's
  `IsCyclic.index_powMonoidHom_range` supplies the index; the quotient's
  cardinality is that index.
* `card_units_quotient_pow` --- at `G = kˣ` for a finite field, `|G| = q - 1`,
  which is the printed `gcd(q-1, d-1)`.

## Calibration

At `d = 2` the second computation gives `gcd(q-1,1) = 1`, agreeing with the
first sentence; so `d = 2` is exactly the case that tests nothing here.  The
first informative case is `d = 3` over `𝔽₅`, where `gcd(4,2) = 2`.
-/

namespace GroupApproximation
namespace LeavittScalarQuotient

/-! ### First powers: the `d = 2` evaluation -/

section General

variable (G : Type*) [CommGroup G]

/-- `x ↦ x¹` is the identity, so the subgroup of first powers is everything. -/
theorem range_powMonoidHom_one : (powMonoidHom 1 : G →* G).range = ⊤ :=
  MonoidHom.range_eq_top.mpr fun x => ⟨x, pow_one x⟩

/-- **`G/G¹` is trivial.**  The arithmetic clause of the printed `d = 2`
sentence: at `d = 2` the printed answer group is `k^×/(k^×)^1`. -/
theorem subsingleton_quotient_powMonoidHom_one :
    Subsingleton (G ⧸ (powMonoidHom 1 : G →* G).range) := by
  constructor
  intro x y
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  have h : ∀ c : G,
      (QuotientGroup.mk c : G ⧸ (powMonoidHom 1 : G →* G).range) = 1 := by
    intro c
    refine (QuotientGroup.eq_one_iff c).mpr ?_
    exact ⟨c, by rw [powMonoidHom_apply, pow_one]⟩
  rw [h a, h b]

end General

/-! ### Powers in a finite cyclic group -/

section CyclicSource

variable (G : Type*) [CommGroup G] [IsCyclic G]

/-- A quotient of a cyclic group is cyclic. -/
theorem isCyclic_quotient_powMonoidHom_range (m : ℕ) :
    IsCyclic (G ⧸ (powMonoidHom m : G →* G).range) :=
  isCyclic_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)

end CyclicSource

section Cyclic

variable (G : Type*) [CommGroup G] [IsCyclic G] [Finite G]

/-- **`|G/Gᵐ| = gcd(|G|, m)` for a finite cyclic group.**  The quotient's
cardinality is the index of the subgroup of `m`-th powers, which Mathlib
evaluates. -/
theorem card_quotient_powMonoidHom_range (m : ℕ) :
    Nat.card (G ⧸ (powMonoidHom m : G →* G).range) = (Nat.card G).gcd m := by
  rw [← Subgroup.index_eq_card]
  exact IsCyclic.index_powMonoidHom_range G m

end Cyclic

/-! ### The answer group at a finite field -/

section FiniteField

variable (k : Type*) [Field k] [Finite k]

/-- **`|k^×/(k^×)^m| = gcd(q-1, m)`** for a finite field with `q` elements.
The unit group of a finite field is cyclic of order `q - 1`. -/
theorem card_units_quotient_pow (m : ℕ) :
    Nat.card (kˣ ⧸ (powMonoidHom m : kˣ →* kˣ).range)
      = (Nat.card k - 1).gcd m := by
  rw [card_quotient_powMonoidHom_range, Nat.card_units]

end FiniteField

/-! ### The printed sentences -/

/-- **Printed sentence, tex line 1322.**

> For `k=𝔽_q` the quotient is cyclic of order `gcd(q-1,d-1)`.

The evaluation clause, at every finite field and every `d ≥ 2`, with `q` read
as `Nat.card k`.  What this does *not* assert is the identification of the
printed quotient `H/EL_d(R)` with `k^×/(k^×)^{d-1}`; that is
`LeavittKOneFormulaSentences.manuscriptLeavittKOneFormula`, and the sentence at the
printed quotient is `LeavittKOneQuotientEvaluations.manuscriptSentence_quotientCyclicFiniteField`. -/
def PrintedLeavittScalarQuotientFiniteField : Prop :=
  ∀ (k : Type) [Field k] [Finite k] (d : ℕ), 2 ≤ d →
    IsCyclic (kˣ ⧸ (powMonoidHom (d - 1) : kˣ →* kˣ).range) ∧
      Nat.card (kˣ ⧸ (powMonoidHom (d - 1) : kˣ →* kˣ).range)
        = Nat.gcd (Nat.card k - 1) (d - 1)

theorem manuscriptSentence_leavittScalarQuotientFiniteField :
    PrintedLeavittScalarQuotientFiniteField := by
  intro k _ _ d _
  exact ⟨isCyclic_quotient_powMonoidHom_range kˣ (d - 1),
    card_units_quotient_pow k (d - 1)⟩

/-- **Printed sentence, tex line 1320, arithmetic clause.**

> For `d=2` the quotient is trivial for every countable field `k`.

At `d = 2` the printed answer group `k^×/(k^×)^{d-1}` is trivial, for every
field and with no countability hypothesis.  (The sentence's second clause,
that every homomorphism from `L_k(1,2)^×` to an MF group is then trivial, is
carried by
`FullDefectRingEJZUnconditional.manuscriptLeavittMFQuotientTwoAllCharacteristics`,
which does not go through this group, and, along the printed "so", by
`LeavittKOneQuotientEvaluations.manuscriptSentence_quotientTrivialRankTwo`.) -/
def PrintedLeavittScalarQuotientRankTwo : Prop :=
  ∀ (k : Type) [Field k] (d : ℕ), d = 2 →
    Subsingleton (kˣ ⧸ (powMonoidHom (d - 1) : kˣ →* kˣ).range)

theorem manuscriptSentence_leavittScalarQuotientRankTwo :
    PrintedLeavittScalarQuotientRankTwo := by
  intro k _ d hd
  subst hd
  have h21 : (2 : ℕ) - 1 = 1 := rfl
  rw [h21]
  exact subsingleton_quotient_powMonoidHom_one kˣ

end LeavittScalarQuotient
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms
  GroupApproximation.LeavittScalarQuotient.subsingleton_quotient_powMonoidHom_one
#audit_axioms
  GroupApproximation.LeavittScalarQuotient.card_quotient_powMonoidHom_range
#audit_axioms
  GroupApproximation.LeavittScalarQuotient.card_units_quotient_pow
#audit_closed_axioms
  GroupApproximation.LeavittScalarQuotient.manuscriptSentence_leavittScalarQuotientFiniteField
#audit_closed_axioms
  GroupApproximation.LeavittScalarQuotient.manuscriptSentence_leavittScalarQuotientRankTwo
