import GroupApproximation.Leavitt.BinaryLeavittSimple

/-!
# The simplified derivation of the coefficient-separation identity

`non_mf_groups_exist.tex` formerly proved a coefficient-separation lemma (retired from the article in favour of Preusser's theorem; the statement stays formalized here) — for
nonzero `r, s` there are `a, b` with `arb = 0` and `bsar ≠ 0` — from
the two-sided sandwich identity alone.  The printed proof chooses *two*
factorizations

  `u r v = 1`,   `c s d = 1`,

sets

  `a = d t₁ u`,   `b = v s₀ c`,

and runs three displays.  This module restates those three displays as closed
sentences and proves them.

## Why this module exists

The tree already carries a formalization of a *different*, earlier printed
proof of the same lemma: four sandwich factorizations `c_r r d_r = 1`,
`e_d d_r f_d = 1`, `e_s s f_s = 1`, `e_t (c_r r) f_t = 1`, an auxiliary
construction at `w = e_t f_d`, and the witnesses `a = f_s x e_t c_r`,
`b = d_r f_d y e_s`.  That recipe is `PartialClosureLeavitt`'s
`PrintedCoefficientSeparationFactorizations`,
`PrintedCoefficientSeparationRecipe` and `PrintedCoefficientSeparation`, and
`SentenceLeavittClosure`'s `manuscript_coefficient_separation_explicit`.  None
of those declarations mentions the witnesses `d t₁ u` and `v s₀ c` that the
manuscript now prints, so none of them carries the three displays below.

In particular `PartialClosureLeavitt`'s
`PrintedReversedProductVanishingImplication` is *not* the third display below.
That one vanishes the four-factor element `(d s₀)(t₁ c)` and multiplies it by
`c w` and `w d`, under the single hypothesis `c w d = 1`; the display below
vanishes the five-factor element `v s₀ t₁ u r` and multiplies it by `u r` and
`v`, under `u r v = 1`.  The two use the same trick on different elements.

## What is *not* restated here

The lemma's *statement* is already `exists_annihilate_preserve_reverse` and
`exists_split_annihilator`; this module formalizes the new proof of it, not the
statement.  The closing clause "contrary to `t₀(s₀t₁)s₁ = 1`" is unchanged from
the earlier print and is already carried by `SentenceLeavittClosure`'s
`manuscript_s0_t1_factorization` and `manuscript_s0_mul_t1_ne_zero`; below it
appears only as a proof step, never as a restated sentence.

## The Leavitt input

Exactly one relation is consumed by the three displays: `t₁ s₀ = 0`.  That is
the `LeavittFamily` field `t1_s0`, and over the manuscript's own coefficient
ring it is `PrintedLeavittEquations`' `printed_leavitt_delta` at `i = 1`,
`j = 0`.  The relations `t₀s₀ = 1` and `t₁s₁ = 1` are used only in the closing
nonvanishing step, and `s₀t₀ + s₁t₁ = 1` is not used at all.

No theorem from the literature is an input.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

/-! ## First display: the witnesses annihilate `r`

`non_mf_groups_exist.tex`: "and set `a = d t₁ u`, `b = v s₀ c`.  The Leavitt
relation `t₁s₀ = 0` gives `arb = d t₁ (urv) s₀ c = d t₁ s₀ c = 0`." -/

/-- **"and set `a = d t₁ u`, `b = v s₀ c`.  The Leavitt relation `t₁s₀ = 0`
gives `arb = d t₁ (urv) s₀ c = d t₁ s₀ c = 0`."**

The printed witnesses are substituted, so the statement records what `a` and
`b` *are* rather than quantifying over them; the three equalities are the three
steps of the printed display, in order, and the fourth conjunct is the
conclusion the display draws.  Only `u r v = 1` is needed: the factorization
`c s d = 1` of `s` plays no part in this display, and `c` and `d` enter as
unconstrained ring elements.  No nontriviality of the ring is needed either. -/
def PrintedSimplifiedSeparationWitnessesAnnihilate : Prop :=
  ∀ (S : Type) [Ring S] (L : LeavittFamily S) (r u v c d : S), u * r * v = 1 →
    (d * L.t1 * u) * r * (v * L.s0 * c)
        = d * L.t1 * (u * r * v) * L.s0 * c ∧
      d * L.t1 * (u * r * v) * L.s0 * c = d * L.t1 * L.s0 * c ∧
      d * L.t1 * L.s0 * c = 0 ∧
      (d * L.t1 * u) * r * (v * L.s0 * c) = 0

/-- Closed proof of the first printed display. -/
theorem manuscriptPrintedSimplifiedSeparationWitnessesAnnihilate :
    PrintedSimplifiedSeparationWitnessesAnnihilate := by
  intro S _ L r u v c d hurv
  have hassoc : (d * L.t1 * u) * r * (v * L.s0 * c)
      = d * L.t1 * (u * r * v) * L.s0 * c := by noncomm_ring
  have hcancel : d * L.t1 * (u * r * v) * L.s0 * c = d * L.t1 * L.s0 * c := by
    rw [hurv, mul_one]
  have hleavitt : d * L.t1 * L.s0 * c = 0 := by
    rw [mul_assoc d L.t1 L.s0, L.t1_s0, mul_zero, zero_mul]
  exact ⟨hassoc, hcancel, hleavitt, by rw [hassoc, hcancel, hleavitt]⟩

/-! ## Second display: the reversed product

`non_mf_groups_exist.tex`: "On the other hand,
`bsar = v s₀ (csd) t₁ u r = v s₀ t₁ u r`." -/

/-- **"On the other hand, `bsar = v s₀ (csd) t₁ u r = v s₀ t₁ u r`."**

The two printed steps and the composite they establish.  Only `c s d = 1` is
needed: the factorization of `r` plays no part in this display, and `u`, `v`
enter as unconstrained ring elements.  No Leavitt relation is consumed — `s₀`
and `t₁` are carried through untouched, which is exactly why the reversed
product survives. -/
def PrintedSimplifiedSeparationReversedProduct : Prop :=
  ∀ (S : Type) [Ring S] (L : LeavittFamily S) (r s u v c d : S), c * s * d = 1 →
    (v * L.s0 * c) * s * (d * L.t1 * u) * r
        = v * L.s0 * (c * s * d) * L.t1 * u * r ∧
      v * L.s0 * (c * s * d) * L.t1 * u * r = v * L.s0 * L.t1 * u * r ∧
      (v * L.s0 * c) * s * (d * L.t1 * u) * r = v * L.s0 * L.t1 * u * r

/-- Closed proof of the second printed display. -/
theorem manuscriptPrintedSimplifiedSeparationReversedProduct :
    PrintedSimplifiedSeparationReversedProduct := by
  intro S _ L r s u v c d hcsd
  have hassoc : (v * L.s0 * c) * s * (d * L.t1 * u) * r
      = v * L.s0 * (c * s * d) * L.t1 * u * r := by noncomm_ring
  have hcancel :
      v * L.s0 * (c * s * d) * L.t1 * u * r = v * L.s0 * L.t1 * u * r := by
    rw [hcsd, mul_one]
  exact ⟨hassoc, hcancel, hassoc.trans hcancel⟩

/-! ## Third display: the reversed product cannot vanish

`non_mf_groups_exist.tex`: "If this element were zero, then
`0 = (ur)(v s₀ t₁ u r) v = (urv) s₀ t₁ (urv) = s₀ t₁`." -/

/-- **"If this element were zero, then
`0 = (ur)(v s₀ t₁ u r) v = (urv) s₀ t₁ (urv) = s₀ t₁`."**

The two printed equalities of the display, followed by the implication the
sentence actually prints.  The manuscript reads the implication
contrapositively — `s₀t₁ ≠ 0`, hence `v s₀ t₁ u r ≠ 0` — but that reading needs
the *separate* clause "contrary to `t₀(s₀t₁)s₁ = 1`", which is already carried
by `SentenceLeavittClosure`'s `manuscript_s0_mul_t1_ne_zero`.  Stating the bare
implication here keeps this sentence free of any nontriviality hypothesis, and
lets the reader check the display line by line.

Neither `s` nor its factorization appears: by the second display the element
whose vanishing is assumed no longer mentions them. -/
def PrintedSimplifiedSeparationVanishingImplication : Prop :=
  ∀ (S : Type) [Ring S] (L : LeavittFamily S) (r u v : S), u * r * v = 1 →
    (u * r) * (v * L.s0 * L.t1 * u * r) * v
        = (u * r * v) * L.s0 * L.t1 * (u * r * v) ∧
      (u * r * v) * L.s0 * L.t1 * (u * r * v) = L.s0 * L.t1 ∧
      (v * L.s0 * L.t1 * u * r = 0 → L.s0 * L.t1 = 0)

/-- Closed proof of the third printed display. -/
theorem manuscriptPrintedSimplifiedSeparationVanishingImplication :
    PrintedSimplifiedSeparationVanishingImplication := by
  intro S _ L r u v hurv
  have hassoc : (u * r) * (v * L.s0 * L.t1 * u * r) * v
      = (u * r * v) * L.s0 * L.t1 * (u * r * v) := by noncomm_ring
  have hcancel :
      (u * r * v) * L.s0 * L.t1 * (u * r * v) = L.s0 * L.t1 := by
    rw [hurv, one_mul, mul_one]
  refine ⟨hassoc, hcancel, ?_⟩
  intro hzero
  calc L.s0 * L.t1
      = (u * r * v) * L.s0 * L.t1 * (u * r * v) := hcancel.symm
    _ = (u * r) * (v * L.s0 * L.t1 * u * r) * v := hassoc.symm
    _ = 0 := by rw [hzero, mul_zero, zero_mul]

/-! ## The three displays as one recipe -/

/-- **The printed recipe of `lem:coefficient-separation`, as now printed.**

Given the two factorizations the proof chooses, the printed witnesses
`a = d t₁ u` and `b = v s₀ c` annihilate `r`, the reversed product `b s a r`
collapses to `v s₀ t₁ u r`, and that element vanishes only if `s₀t₁` does.  This
is the whole printed derivation with the nonvanishing clause left to its own
sentence, so no hypothesis on the ring beyond the two factorizations is
needed. -/
def PrintedSimplifiedCoefficientSeparationRecipe : Prop :=
  ∀ (S : Type) [Ring S] (L : LeavittFamily S) (r s u v c d : S),
    u * r * v = 1 → c * s * d = 1 →
      (d * L.t1 * u) * r * (v * L.s0 * c) = 0 ∧
        (v * L.s0 * c) * s * (d * L.t1 * u) * r = v * L.s0 * L.t1 * u * r ∧
          (v * L.s0 * L.t1 * u * r = 0 → L.s0 * L.t1 = 0)

/-- Closed proof of the printed recipe, from the three displays. -/
theorem manuscriptPrintedSimplifiedCoefficientSeparationRecipe :
    PrintedSimplifiedCoefficientSeparationRecipe := by
  intro S _ L r s u v c d hurv hcsd
  obtain ⟨-, -, -, hab⟩ :=
    manuscriptPrintedSimplifiedSeparationWitnessesAnnihilate S L r u v c d hurv
  obtain ⟨-, -, hba⟩ :=
    manuscriptPrintedSimplifiedSeparationReversedProduct S L r s u v c d hcsd
  obtain ⟨-, -, himp⟩ :=
    manuscriptPrintedSimplifiedSeparationVanishingImplication S L r u v hurv
  exact ⟨hab, hba, himp⟩

/-- **The whole simplified derivation of the coefficient-separation identity.**

For nonzero `r, s` the two factorizations and the printed witnesses all exist
together and satisfy `arb = 0`, `bsar ≠ 0`.  Two-sided division is the only
input, and it is supplied as a hypothesis rather than quoted, so the sentence
applies verbatim to every ring carrying a Leavitt family in which nonzero
elements divide the identity from both sides. -/
def PrintedSimplifiedCoefficientSeparation : Prop :=
  ∀ (S : Type) [Ring S] (L : LeavittFamily S),
    (∀ z : S, z ≠ 0 → ∃ c d : S, c * z * d = 1) →
      ∀ r s : S, r ≠ 0 → s ≠ 0 →
        ∃ u v c d a b : S,
          u * r * v = 1 ∧ c * s * d = 1 ∧
            a = d * L.t1 * u ∧ b = v * L.s0 * c ∧
              a * r * b = 0 ∧ b * s * a * r ≠ 0

/-- Closed proof of the simplified derivation.  The final step is the printed
clause "contrary to `t₀(s₀t₁)s₁ = 1`", used here as a proof step; as a printed
sentence it belongs to `SentenceLeavittClosure`. -/
theorem manuscriptPrintedSimplifiedCoefficientSeparation :
    PrintedSimplifiedCoefficientSeparation := by
  intro S _ L hdiv r s hr hs
  letI : Nontrivial S := ⟨⟨r, 0, hr⟩⟩
  obtain ⟨u, v, hurv⟩ := hdiv r hr
  obtain ⟨c, d, hcsd⟩ := hdiv s hs
  obtain ⟨hab, hba, himp⟩ :=
    manuscriptPrintedSimplifiedCoefficientSeparationRecipe S L r s u v c d hurv
      hcsd
  refine ⟨u, v, c, d, d * L.t1 * u, v * L.s0 * c, hurv, hcsd, rfl, rfl, hab, ?_⟩
  rw [hba]
  intro hzero
  have hs0t1 : L.s0 * L.t1 = 0 := himp hzero
  have hone : (1 : S) = 0 := by
    calc (1 : S) = (L.t0 * L.s0) * (L.t1 * L.s1) := by
          rw [L.t0_s0, L.t1_s1, one_mul]
      _ = L.t0 * (L.s0 * L.t1) * L.s1 := by noncomm_ring
      _ = 0 := by rw [hs0t1, mul_zero, zero_mul]
  exact one_ne_zero hone

/-! ## The derivation at the manuscript's coefficient ring -/

/-- **The simplified derivation at `R = L_{𝔽₂}(1,2)`.**

`lem:coefficient-separation` is printed over the manuscript's own coefficient
ring, so the derivation is recorded there too, with the printed witnesses
displayed rather than existentially hidden.  Two-sided division is
`BinaryLeavitt.exists_mul_mul_eq_one`, so nothing is assumed. -/
def PrintedSimplifiedCoefficientSeparationAtBinaryLeavitt : Prop :=
  ∀ r s : BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2), r ≠ 0 → s ≠ 0 →
    ∃ u v c d : BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2),
      u * r * v = 1 ∧ c * s * d = 1 ∧
        (d * (BinaryLeavitt.family (ZMod 2)).t1 * u) * r *
            (v * (BinaryLeavitt.family (ZMod 2)).s0 * c) = 0 ∧
          (v * (BinaryLeavitt.family (ZMod 2)).s0 * c) * s *
              (d * (BinaryLeavitt.family (ZMod 2)).t1 * u) * r ≠ 0

/-- Closed proof of the simplified derivation over `L_{𝔽₂}(1,2)`. -/
theorem manuscriptPrintedSimplifiedCoefficientSeparationAtBinaryLeavitt :
    PrintedSimplifiedCoefficientSeparationAtBinaryLeavitt := by
  intro r s hr hs
  obtain ⟨u, v, c, d, a, b, hurv, hcsd, ha, hb, hab, hba⟩ :=
    manuscriptPrintedSimplifiedCoefficientSeparation
      (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))
      (BinaryLeavitt.family (ZMod 2))
      (fun _ hx => BinaryLeavitt.exists_mul_mul_eq_one (ZMod 2) hx) r s hr hs
  subst ha
  subst hb
  exact ⟨u, v, c, d, hurv, hcsd, hab, hba⟩

/-! ## The simplified derivation as one closed sentence -/

/-- The three printed displays of the simplified proof of
`lem:coefficient-separation`, the recipe they assemble into, and its two
instances. -/
def PrintedSimplifiedCoefficientSeparationCalculations : Prop :=
  PrintedSimplifiedSeparationWitnessesAnnihilate ∧
    PrintedSimplifiedSeparationReversedProduct ∧
      PrintedSimplifiedSeparationVanishingImplication ∧
        PrintedSimplifiedCoefficientSeparationRecipe ∧
          PrintedSimplifiedCoefficientSeparation ∧
            PrintedSimplifiedCoefficientSeparationAtBinaryLeavitt

/-- Closed proof of the whole simplified derivation. -/
theorem manuscriptPrintedSimplifiedCoefficientSeparationCalculations :
    PrintedSimplifiedCoefficientSeparationCalculations :=
  ⟨manuscriptPrintedSimplifiedSeparationWitnessesAnnihilate,
    manuscriptPrintedSimplifiedSeparationReversedProduct,
    manuscriptPrintedSimplifiedSeparationVanishingImplication,
    manuscriptPrintedSimplifiedCoefficientSeparationRecipe,
    manuscriptPrintedSimplifiedCoefficientSeparation,
    manuscriptPrintedSimplifiedCoefficientSeparationAtBinaryLeavitt⟩

end OneSidedMFRadical
end Manuscript
end GroupApproximation
