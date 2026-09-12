import GroupApproximation.GGT.RelHypOsin24CayleyLeaf
import GroupApproximation.GGT.RelHypOsin24Collapse

/-!
# The collapse witness is not a model of the fourth generation

`GGT/RelHypOsin24Collapse.lean` refutes the first three generations of the
weighted Greendlinger leaf with a length function on `ℤ * ℤ` whose unit ball
contains every commutator of the two factors.  `GGT/RelHypOsin24CayleyLeaf.lean`
states the fourth generation over `RelativeGeneratingSet.relLength`, the word
metric of `X ⊔ ℋ` with `X` **finite**.  This module closes the loop: the
collapse length function is the relative metric of **no** relative generating
set, so the refutation does not transfer.

The argument is the unit-ball theorem plus a counting step.  If
`relLengthOf X` agreed with the collapse length, then each `[t^m, s]` -- a
letter of the collapse metric, and never trivial -- would lie in `X ⊔ ℋ`.  It
lies in no peripheral coset, because the abelianisation of a source element has
trivial second coordinate and the commutator's abelianisation is zero while the
commutator is not; so it would lie in `X`.  But `m ↦ [t^m, s]` is injective --
the infinite dihedral action separates them, translating by `2m` -- and `X` is
finite.

This is the model test the standing rule asks for, in the direction that
matters: the new statement is not refuted by the witness that refutes the old
one, and the reason is the clause that was added.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open Monoid Monoid.CoprodI
open GroupApproximation.OsinWeightedMetric

namespace Osin24Collapse

/-- **The short element is not a source letter**, stated at `Multiplicative ℤ`
and routed through `emF`.

Both choices are forced by the family's carrier.  `Fam false` reduces to a
`match` on `Bool`, so a numeral or a class instance demanded *at* that type does
not elaborate -- which rules out writing `(1 : Fam false)`; and `CoprodI.of`
carries an implicit index that cannot be recovered from `Multiplicative ℤ`, so a
rewrite under it has no type-correct motive.  `emF`'s domain is fixed and
`Multiplicative ℤ` is defeq to it, so every step below is a rewrite at a type
the elaborator can see through. -/
theorem bad_ne_emF (m : ℕ) (hm : 1 ≤ m) (y : Multiplicative ℤ) :
    emF y ≠ bad m := by
  intro h
  have h0 : ab (emF y) = 0 := by
    rw [h]
    exact ab_bad m
  have h1 : (Multiplicative.toAdd y, (0 : ℤ)) = (0 : ℤ × ℤ) := (ab_emF y).symm.trans h0
  have h2 : Multiplicative.toAdd y = 0 := congrArg Prod.fst h1
  have h3 : y = 1 := by
    have h4 := congrArg Multiplicative.ofAdd h2
    rw [ofAdd_toAdd, ofAdd_zero] at h4
    exact h4
  have h5 : emF y = 1 := by
    rw [h3]
    exact map_one emF
  exact bad_ne_one m hm (h5.symm.trans h).symm

/-- **The short element lies in no peripheral coset.**  Its abelianisation is
zero, and the abelianisation is injective on each factor, so a source element
with the same abelianisation is trivial -- while `bad m` is not. -/
theorem bad_not_mem_sourceFactor (m : ℕ) (hm : 1 ≤ m) :
    bad m ∉ sourceFactor Fam := by
  rintro ⟨x, hx⟩
  exact bad_ne_emF m hm x hx

/-- **The short elements are pairwise distinct.**  `psi (bad m)` translates by
`2m`, so `m` is recoverable from `bad m`. -/
theorem bad_injective : Function.Injective (fun m : ℕ => bad (m + 1)) := by
  intro m m' h
  have h' : bad (m + 1) = bad (m' + 1) := h
  have h2 : psi (bad (m + 1)) 0 = psi (bad (m' + 1)) 0 := by rw [h']
  rw [psi_bad_apply, psi_bad_apply] at h2
  omega

end Osin24Collapse

/-- **The collapse length function is the relative metric of no finite relative
generating set.**

Stated pointwise on the length functions, so it does not depend on how the
`RelativeLength` structures are packaged: no `X` at all has
`relLengthOf X` agreeing with `Osin24Collapse.L` even as a function.  Since the
fourth-generation leaf quantifies only over length functions of the form
`relLengthOf X`, the collapse refutation cannot be run against it. -/
theorem not_isRelLength_collapse :
    ¬ ∃ X : RelativeGeneratingSet (CoprodI Osin24Collapse.Fam)
        (fun _ : Unit => sourceFactor Osin24Collapse.Fam),
      ∀ g, (relLengthOf X).len g = Osin24Collapse.L.len g := by
  rintro ⟨X, hX⟩
  have hmem : ∀ m : ℕ, Osin24Collapse.bad (m + 1) ∈ X.carrier := by
    intro m
    have h1 : (relLengthOf X).len (Osin24Collapse.bad (m + 1)) ≤ 1 := by
      rw [hX]
      exact Osin24Collapse.L_len_bad (m + 1)
    have h2 : Osin24Collapse.bad (m + 1) ∈ X.alphabet.carrier :=
      mem_alphabet_of_relLengthOf_le_one X h1
    rw [X.alphabet_carrier] at h2
    rcases h2 with h2 | h2
    · exact h2
    · rw [Set.mem_iUnion] at h2
      obtain ⟨l, hl⟩ := h2
      exact absurd hl (Osin24Collapse.bad_not_mem_sourceFactor (m + 1) (by omega))
  have hsub : Set.range (fun m : ℕ => Osin24Collapse.bad (m + 1)) ⊆ X.carrier := by
    rintro _ ⟨m, rfl⟩
    exact hmem m
  exact Set.infinite_range_of_injective Osin24Collapse.bad_injective
    (X.finite.subset hsub)

end RelHyp
end GGT
end GroupApproximation
