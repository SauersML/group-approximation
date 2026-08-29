import GroupApproximation.GGT.HullSCUnionGeometrySyllableSplit

/-!
# The crossing estimate for a conjugator with many syllables

This module closes the branch of the acylindricity clause in which `t` has many
syllables, and it closes it for *every* `k`: no cyclic reduction, no conjugacy
theorem, no axis.

## The statement

`exists_prefix_pair_of_syllable_displacement`: if `sylLength k ≤ ε` and
`sylLength (t⁻¹ * k * t) ≤ ε` and `2 * ε + 2 ≤ sylLength t`, then

    k = b * a⁻¹      with `a` and `b` syllable prefixes of `t`
                     of syllable length at most `ε + 1` .

So the displacement set injects into a pair of prefixes of a *fixed* word, and
`finite_syllablePrefix` bounds those by their syllable count.  The count that
comes out is `(ε + 2) * (ε + 2)`, and it never enumerates a ball --- Hull's alphabets
are infinite, and the letters of `a` and `b` are read off `t` rather than
chosen.

## Where the two prefixes come from

`a` is the common suffix splitting of `t` and `k * t`: their common suffix `w`
gives `t = a * w`, `k * t = b * w`, so `k = b * a⁻¹`, and

    sylLength a + sylLength b ≤ sylLength k + 1 ≤ ε + 1 .

That `a` is a prefix of `t` is immediate.  That `b` is a prefix of `t` is the
step that needs `t` to be long: the common *prefix* splitting of `t` and `k * t`
gives `t = c * u`, `k * t = c * v` with

    sylLength u + sylLength v ≤ sylLength (t⁻¹ * k * t) + 1 ≤ ε + 1 ,

so `sylLength c ≥ sylLength t - (ε + 1) ≥ ε + 1 ≥ sylLength b`.  Both `b` and
`c` are prefixes of `k * t`, and the shorter of two prefixes of one word is a
prefix of the longer, so `b` is a prefix of `c`, hence of `t`.

## What this replaces

The lineal case is real: for `k = e * h` cyclically reduced and `t = k ^ 10` one
has `sylLength k = 2`, `t⁻¹ * k * t = k` and `sylLength t = 20`, so no bound of
the form `sylLength k + sylLength (t⁻¹ k t) ≥ 2 * sylLength t` can hold.  The
statement above survives it: `a = 1` and `b = k`, and `k` is a prefix of `k ^ 10`.
What is bounded is the number of such `k`, not the length of `t`.

## What remains

`isAcylindrical_cayley_of_conjDisplacement` quantifies over `t` of large *word
length*, and a `t` of large word length may still have few syllables --- one
letter of a Hull alphabet can be arbitrarily long.  So
`finite_conjDisplacement_of_sylLength` covers the clause only where
`2 * ⌊ε⌋₊ + 2 ≤ sylLength t`, and the complementary branch, `sylLength t` small
and `wordNorm t` large, is the one where a single syllable of `t` is long and
the factor's own acylindricity has to be used.  `exists_suffix_split` is stated
without any hypothesis on `t` because it is the entry point there as well: it
already writes `k = b * a⁻¹` with `a` a syllable prefix of `t`, and what the
long syllable has to supply is the bound on `b`.
-/

namespace GroupApproximation
namespace HullSCUnionGeometry

open Monoid Monoid.CoprodI
open GroupApproximation.WordMetric
open GroupApproximation.HullGeometry
open GroupApproximation.FreeProductCyclic
open GroupApproximation.FreeProductUnionNorm
open GroupApproximation.Manuscript.NonMF.TorsionFree

section Count

variable {ι : Type*} [DecidableEq ι] {G : ι → Type*} [∀ i, Group (G i)]
  [∀ i, DecidableEq (G i)] {S : ∀ i, Set (G i)}

/-! ## 1.  The two prefixes -/

/-- **The back half, with no hypothesis on `t`.**  Every `k` is the quotient of
a syllable prefix of `k * t` by a syllable prefix of `t`, and the two together
cost at most one syllable more than `k` itself. -/
theorem exists_suffix_split (t k : CoprodI G) :
    ∃ a b : CoprodI G, IsSyllablePrefix a t ∧ IsSyllablePrefix b (k * t) ∧
      sylLength a + sylLength b ≤ sylLength k + 1 ∧ k = b * a⁻¹ := by
  obtain ⟨w, a, b, hta, hktb, htl, hktl, hsuf⟩ := exists_common_suffix t (k * t)
  have hkk : (k * t) * t⁻¹ = k := by group
  rw [hkk] at hsuf
  refine ⟨a, b, isSyllablePrefix_of_toList_append htl,
    isSyllablePrefix_of_toList_append hktl, hsuf, ?_⟩
  have h1 : k * (a * w) = b * w := by rw [← hta]; exact hktb
  have h2 : k = b * w * (a * w)⁻¹ := by rw [← h1]; group
  rw [h2]
  group

/-- **The crossing estimate.**  A `k` that displaces both `1` and a `t` of many
syllables by at most `ε` syllables is the quotient of two syllable prefixes of
`t`, each of at most `ε + 1` syllables. -/
theorem exists_prefix_pair_of_syllable_displacement {t k : CoprodI G} {ε : ℕ}
    (hk : sylLength k ≤ ε) (hkt : sylLength (t⁻¹ * k * t) ≤ ε)
    (ht : 2 * ε + 2 ≤ sylLength t) :
    ∃ a b : CoprodI G, IsSyllablePrefix a t ∧ IsSyllablePrefix b t ∧
      sylLength a ≤ ε + 1 ∧ sylLength b ≤ ε + 1 ∧ k = b * a⁻¹ := by
  obtain ⟨a, b, hapre, hbpre, hsuf, hkeq⟩ := exists_suffix_split t k
  obtain ⟨c, u, v, -, -, htl2, hktl2, hpre⟩ := exists_common_prefix t (k * t)
  have hka : t⁻¹ * (k * t) = t⁻¹ * k * t := by group
  rw [hka] at hpre
  have hlent : sylLength t = sylLength c + sylLength u := by
    simp only [sylLength, htl2, List.length_append]
  refine ⟨a, b, hapre, ?_, by omega, by omega, hkeq⟩
  have hcpre : IsSyllablePrefix c (k * t) := isSyllablePrefix_of_toList_append hktl2
  have hctpre : IsSyllablePrefix c t := isSyllablePrefix_of_toList_append htl2
  have hlen : (Word.equiv b).toList.length ≤ (Word.equiv c).toList.length := by
    show sylLength b ≤ sylLength c
    omega
  exact (List.prefix_of_prefix_length_le hbpre hcpre hlen).trans hctpre

/-! ## 2.  The count -/

section Counting

variable {H : Type*} [Group H]

/-- **A displacement set whose elements are quotients from two finite sets is
finite**, with cardinality at most the product.  This is
`finite_of_conj_decomposition` for the shape the crossing estimate produces. -/
theorem finite_of_quotient_decomposition {D : Set H} (P Q : Finset H)
    (hD : ∀ k ∈ D, ∃ b ∈ Q, ∃ a ∈ P, k = b * a⁻¹) :
    D.Finite ∧ D.ncard ≤ Q.card * P.card := by
  classical
  have hsub : D ⊆ ↑((Q ×ˢ P).image fun p : H × H => p.1 * p.2⁻¹) := by
    intro k hk
    obtain ⟨b, hb, a, ha, rfl⟩ := hD k hk
    exact Finset.mem_coe.mpr
      (Finset.mem_image.mpr ⟨(b, a), Finset.mem_product.mpr ⟨hb, ha⟩, rfl⟩)
  refine ⟨Set.Finite.subset (Finset.finite_toSet _) hsub, ?_⟩
  calc D.ncard
      ≤ (↑((Q ×ˢ P).image fun p : H × H => p.1 * p.2⁻¹) : Set H).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = ((Q ×ˢ P).image fun p : H × H => p.1 * p.2⁻¹).card :=
        Set.ncard_coe_finset _
    _ ≤ (Q ×ˢ P).card := Finset.card_image_le
    _ = Q.card * P.card := by rw [Finset.card_product]

end Counting

/-- **The syllable displacement set of a long word is finite**, with at most
`(ε + 2) * (ε + 2)` elements.  The prefixes of `t` of at most `ε + 1` syllables are
`ε + 2` many, and `exists_prefix_pair_of_syllable_displacement` writes every
element of the set as a quotient of two of them. -/
theorem finite_syllableDisplacement (t : CoprodI G) (ε : ℕ)
    (ht : 2 * ε + 2 ≤ sylLength t) :
    {k : CoprodI G | sylLength k ≤ ε ∧ sylLength (t⁻¹ * k * t) ≤ ε}.Finite ∧
      {k : CoprodI G | sylLength k ≤ ε ∧ sylLength (t⁻¹ * k * t) ≤ ε}.ncard
        ≤ (ε + 2) * (ε + 2) := by
  classical
  have hPfin :
      {c : CoprodI G | IsSyllablePrefix c t ∧ sylLength c ≤ ε + 1}.Finite :=
    (finite_syllablePrefix t (ε + 1)).1
  have hQcard : hPfin.toFinset.card ≤ ε + 2 := by
    have hmaps : ∀ c ∈ hPfin.toFinset, sylLength c ∈ Finset.range (ε + 2) := by
      intro c hc
      have hc' : c ∈ {c : CoprodI G | IsSyllablePrefix c t ∧ sylLength c ≤ ε + 1} :=
        hPfin.mem_toFinset.mp hc
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le hc'.2)
    have hinj : Set.InjOn sylLength
        (hPfin.toFinset : Set (CoprodI G)) := by
      intro p hp q hq hpq
      have hp' : p ∈ {c : CoprodI G | IsSyllablePrefix c t ∧ sylLength c ≤ ε + 1} :=
        hPfin.mem_toFinset.mp (Finset.mem_coe.mp hp)
      have hq' : q ∈ {c : CoprodI G | IsSyllablePrefix c t ∧ sylLength c ≤ ε + 1} :=
        hPfin.mem_toFinset.mp (Finset.mem_coe.mp hq)
      exact eq_of_isSyllablePrefix_of_sylLength_eq hp'.1 hq'.1 hpq
    have hcard := Finset.card_le_card_of_injOn sylLength hmaps hinj
    rwa [Finset.card_range] at hcard
  have hD : ∀ k ∈ {k : CoprodI G | sylLength k ≤ ε ∧ sylLength (t⁻¹ * k * t) ≤ ε},
      ∃ b ∈ hPfin.toFinset, ∃ a ∈ hPfin.toFinset, k = b * a⁻¹ := by
    rintro k ⟨hk1, hk2⟩
    obtain ⟨a, b, hap, hbp, hal, hbl, hkeq⟩ :=
      exists_prefix_pair_of_syllable_displacement hk1 hk2 ht
    exact ⟨b, hPfin.mem_toFinset.mpr ⟨hbp, hbl⟩, a,
      hPfin.mem_toFinset.mpr ⟨hap, hal⟩, hkeq⟩
  obtain ⟨hfin, hcard⟩ :=
    finite_of_quotient_decomposition hPfin.toFinset hPfin.toFinset hD
  exact ⟨hfin, le_trans hcard (Nat.mul_le_mul hQcard hQcard)⟩

/-! ## 3.  In the vocabulary of the acylindricity clause -/

/-- **The conjugation displacement set of the union alphabet is finite at every
`t` with many syllables**, with a bound depending only on `ε`.  A syllable costs
at least one letter, so the union word metric controls the syllable metric and
the previous count applies. -/
theorem finite_conjDisplacement_of_sylLength
    (hS : ∀ i, IsSymmetricGeneratingSet (S i)) {A : Alphabet (CoprodI G)}
    (hA : A.carrier = unionCarrier S) (ε : ℝ) (t : CoprodI G)
    (ht : 2 * ⌊ε⌋₊ + 2 ≤ sylLength t) :
    (conjDisplacement A ε t).Finite ∧
      (conjDisplacement A ε t).ncard ≤ (⌊ε⌋₊ + 2) * (⌊ε⌋₊ + 2) := by
  obtain ⟨hfin, hcard⟩ := finite_syllableDisplacement t ⌊ε⌋₊ ht
  have hsub : conjDisplacement A ε t
      ⊆ {k : CoprodI G | sylLength k ≤ ⌊ε⌋₊ ∧
          sylLength (t⁻¹ * k * t) ≤ ⌊ε⌋₊} := by
    rintro k ⟨h1, h2⟩
    rw [hA] at h1 h2
    exact ⟨le_trans (sylLength_le_wordNorm hS k) (Nat.le_floor h1),
      le_trans (sylLength_le_wordNorm hS _) (Nat.le_floor h2)⟩
  exact ⟨hfin.subset hsub, le_trans (Set.ncard_le_ncard hsub hfin) hcard⟩

end Count

end HullSCUnionGeometry
end GroupApproximation
