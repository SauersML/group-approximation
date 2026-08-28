import GroupApproximation.GGT.RelHypOsinTheorem24

/-!
# `OsinTheorem24` is false as stated, and the hypothesis it is missing

`GGT/RelHypOsinTheorem24.lean` states

    OsinTheorem24 : ∀ (G : Bool → Type) (_ : ∀ b, Group (G b)) (L : RelativeLength G)
      (R : Set (List (CoprodI G))) (lam : ℚ),
        WeightedGreendlingerLeaf L R lam ∧ WeightedTorsionLeaf L R lam

-- the universal closure of the two open leaves of `Sofic/OsinWeightedMetric.lean`.
`fournierFacioQuotientStatement_of_osin'` proves the Fournier-Facio quotient
sentence from it.  **This module proves `¬ OsinTheorem24`**, so that reduction
runs on a false hypothesis and establishes nothing until the leaf is repaired.

## The witness

Take the peripheral factor trivial and the partner factor `ℤ`, written
multiplicatively, and let the alphabet be

    X ∪ U  =  {1} ∪ {t^{±1}} ∪ {t^{±42}},

where `t` generates `ℤ`.  `L` is its word length, which has geodesic spellings
outright (`hasGeodesicSpellings_ofSymmetricGeneratingSet`).  The relator family
is the two words

    w = t · t ⋯ t   (42 letters),      w⁻¹ = t⁻¹ · t⁻¹ ⋯ t⁻¹   (42 letters),

and `R = {w, w⁻¹}`.  Every hypothesis of `WeightedGreendlingerLeaf` holds:

* `LetterSymmetrized` -- a constant list is fixed by every rotation
  (`List.rotate_replicate`), and formal inversion exchanges the two words;
* `LetterReduced` -- two adjacent letters multiply to `t^{±2}`, which is not a
  letter, so the pair does not merge;
* letters -- `t^{±1}` are letters;
* `LetterFragmentSlack` at `lam = 1/7` -- `42/7 + 1 = 7 = 42/6`, exactly;
* `LetterMetricSmallCancellation` at `lam = 1/7` -- the two members of `R` have
  **no letter in common**, so the only piece is the empty word, and
  `0 < 42/7`.

And the conclusion fails: `w.prod = t^42`, which is nontrivial and lies in
`⟪R⟫`, and it is a *single letter*, so `L.len (w.prod) = 1`, while every member
of `R` has `42` letters.  `RelativeLengthBound` would demand a relator shorter
than `2`.

## What the leaf is missing, and it is not the length floor

Scaling the witness does not help a repair that only raises the floor: the
witness already has relators of exactly `42` letters, the design's own floor,
and the same construction gives any length at all.  The defect is that
**nothing requires a relator to be a geodesic word**.  `HasGeodesicSpellings` is
a condition on `L`, and it is used to choose a spelling of the element `g` in
the conclusion; the relators themselves are arbitrary letter lists, so a relator
of `42` letters may spell an element of relative length `1`.  Osin's relators
are cycles in the relative Cayley graph whose subpaths are quasi-geodesic
(*Small cancellations over relatively hyperbolic groups*, §2), and that is the
clause that is absent here.

`not_geodesic_w` proves that the witness fails exactly that clause, so the
diagnosis is checked and not asserted.

A second defect is **not** formalized here, and is recorded as an analysis:
`LetterIsPiece` is a *syntactic* common prefix, while Osin's pieces are
subpaths that are equal *in the group*.  Two relators `u₁ · C₁` and `u₂ · C₂`
with `C₁` and `C₂` distinct geodesic letter lists spelling the same element of
the partner factor have no common letter, so they satisfy
`LetterMetricSmallCancellation` vacuously and geodesically, while
`r₁.prod · r₂.prod⁻¹ = u₁u₂⁻¹` is one letter long.  Writing that family down needs
a partner group with two disjoint geodesic spellings of one element, which is
why it is described rather than built.  `LetterIsGroupPiece` and
`LetterMetricGroupSmallCancellation` name the repaired condition, and
`letterMetricSmallCancellation_of_group` checks that it is the stronger of the
two -- so the design's `metric` field has to be restated over it, a `C'(1/8)`
proof for syntactic pieces not being one for group pieces.

## What is not claimed

Nothing here says Osin's theorem is false.  What is false is this repository's
*transcription* of it: the universal closure of the two leaves, with pieces read
syntactically and with no geodesicity demanded of the relators.  Until the two
clauses above are added, `fournierFacioQuotientStatement_of_osin'`,
`fournierFacioQuotientStatement_of_coned` and
`exists_smallCancellationQuotient` are conditional on a refuted hypothesis.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open Monoid Monoid.CoprodI
open GroupApproximation.OsinWeightedMetric
open GroupApproximation.WordMetric

namespace OsinRefutation

/-! ## 0.  A word of length one is a letter -/

/-- **An element that is neither trivial nor a letter needs two letters.**  The
word norm is attained, so a norm of `1` exhibits the element as a letter. -/
theorem two_le_wordNorm {G : Type*} [Group G] {S : Set G}
    (hS : IsSymmetricGeneratingSet S) {g : G} (h1 : g ≠ 1) (h2 : g ∉ S) :
    2 ≤ wordNorm S g := by
  obtain ⟨l, hl, hlen⟩ := exists_isWord_length_eq hS g
  rw [← hlen]
  rcases l with _ | ⟨x, _ | ⟨_, _⟩⟩
  · exact absurd (by simpa using hl.prod_eq.symm) h1
  · refine absurd ?_ h2
    have hx : x ∈ S := hl.letters x (by simp)
    have hxg : x = g := by simpa using hl.prod_eq
    rwa [hxg] at hx
  · simp only [List.length_cons]
    omega

/-! ## 1.  The witness family: trivial peripheral factor, `ℤ` partner -/

/-- The two-factor family of the counterexample. -/
def Fam : Bool → Type
  | false => PUnit
  | true => Multiplicative ℤ

instance instFamGroup : ∀ b, Group (Fam b)
  | false => inferInstanceAs (Group PUnit)
  | true => inferInstanceAs (Group (Multiplicative ℤ))

theorem fam_false_eq_one (x : Fam false) : x = 1 := by
  cases x
  rfl

/-- The inclusion of the partner factor. -/
def em : Fam true →* CoprodI Fam := CoprodI.of

theorem em_injective : Function.Injective em := CoprodI.of_injective true

/-- The letter `t ^ n`, indexed additively. -/
def E (n : ℤ) : CoprodI Fam := em (Multiplicative.ofAdd n)

theorem E_inj {m n : ℤ} (h : E m = E n) : m = n := by
  have h' : (Multiplicative.ofAdd m : Fam true) = Multiplicative.ofAdd n :=
    em_injective h
  exact Multiplicative.ofAdd.injective h'

theorem E_add (m n : ℤ) : E (m + n) = E m * E n := by
  show em (Multiplicative.ofAdd (m + n))
      = em (Multiplicative.ofAdd m) * em (Multiplicative.ofAdd n)
  rw [Multiplicative.ofAdd_add, map_mul]

theorem E_zero : E 0 = 1 := by
  show em (Multiplicative.ofAdd (0 : ℤ)) = 1
  rw [Multiplicative.ofAdd_zero, map_one]

theorem E_neg (n : ℤ) : E (-n) = (E n)⁻¹ := by
  show em (Multiplicative.ofAdd (-n)) = (em (Multiplicative.ofAdd n))⁻¹
  rw [Multiplicative.ofAdd_neg, map_inv]

theorem E_ne_one {n : ℤ} (h : n ≠ 0) : E n ≠ 1 := by
  intro hc
  exact h (E_inj (by rw [hc, E_zero]))

theorem E_pow (n : ℕ) : (E 1) ^ n = E (n : ℤ) := by
  induction n with
  | zero => simp [E_zero]
  | succ k ih =>
      rw [pow_succ, ih, ← E_add]
      congr 1
      push_cast
      ring

/-! ## 2.  Osin's alphabet, at five exponents -/

/-- The alphabet `X ∪ U`: the trivial peripheral factor, and `t^{±1}`,
`t^{±42}`. -/
def alph : Set (CoprodI Fam) :=
  {g | ∃ n : ℤ, (n = 0 ∨ n = 1 ∨ n = -1 ∨ n = 42 ∨ n = -42) ∧ g = E n}

theorem mem_alph_iff {n : ℤ} :
    E n ∈ alph ↔ (n = 0 ∨ n = 1 ∨ n = -1 ∨ n = 42 ∨ n = -42) := by
  constructor
  · rintro ⟨m, hm, hEq⟩
    rw [E_inj hEq]
    exact hm
  · intro h
    exact ⟨n, h, rfl⟩

theorem E_mem_closure (n : ℤ) : E n ∈ Subgroup.closure alph := by
  induction n using Int.induction_on with
  | hz =>
      rw [E_zero]
      exact one_mem _
  | hp k ih =>
      rw [E_add]
      exact mul_mem ih (Subgroup.subset_closure ⟨1, by norm_num, rfl⟩)
  | hn k ih =>
      have hsplit : (-(k : ℤ) - 1) = (-(k : ℤ)) + (-1) := by ring
      rw [hsplit, E_add]
      exact mul_mem ih (Subgroup.subset_closure ⟨-1, by norm_num, rfl⟩)

theorem alph_src : ∀ x : Fam false, (CoprodI.of x : CoprodI Fam) ∈ alph := by
  intro x
  refine ⟨0, by norm_num, ?_⟩
  rw [fam_false_eq_one x, map_one, E_zero]

theorem alph_symmGen : IsSymmetricGeneratingSet alph := by
  constructor
  · rintro g ⟨n, hn, rfl⟩
    refine ⟨-n, ?_, ?_⟩
    · rcases hn with h | h | h | h | h <;> rw [h] <;> norm_num
    · rw [E_neg]
  · refine Subgroup.eq_top_iff'.mpr ?_
    intro g
    induction g using Monoid.CoprodI.induction_on with
    | one => exact one_mem _
    | of i x =>
        cases i with
        | false =>
            rw [fam_false_eq_one x, map_one]
            exact one_mem _
        | true =>
            have hx : (CoprodI.of x : CoprodI Fam) = E (Multiplicative.toAdd x) := by
              show em x = em (Multiplicative.ofAdd (Multiplicative.toAdd x))
              rw [Multiplicative.ofAdd_toAdd]
            rw [hx]
            exact E_mem_closure _
    | mul _ _ ha hb => exact mul_mem ha hb

/-! ## 3.  The relative length function -/

/-- The witness's relative length: the word length of `X ∪ U`. -/
noncomputable def L : RelativeLength Fam :=
  ofSymmetricGeneratingSet alph_symmGen alph_src

theorem hasGeo : HasGeodesicSpellings L :=
  hasGeodesicSpellings_ofSymmetricGeneratingSet alph_symmGen alph_src

theorem len_le_one {n : ℤ} (h : n = 0 ∨ n = 1 ∨ n = -1 ∨ n = 42 ∨ n = -42) :
    L.len (E n) ≤ 1 :=
  wordNorm_le_one_of_mem (mem_alph_iff.mpr h)

theorem two_le_len {n : ℤ} (h0 : n ≠ 0)
    (h : ¬ (n = 0 ∨ n = 1 ∨ n = -1 ∨ n = 42 ∨ n = -42)) : 2 ≤ L.len (E n) :=
  two_le_wordNorm alph_symmGen (E_ne_one h0) (fun hc => h (mem_alph_iff.mp hc))

/-! ## 4.  The relator family: one word and its formal inverse -/

/-- `t` repeated `42` times. -/
def w : List (CoprodI Fam) := List.replicate 42 (E 1)

/-- `t⁻¹` repeated `42` times. -/
def wInv : List (CoprodI Fam) := List.replicate 42 (E (-1))

theorem w_def : w = List.replicate 42 (E 1) := rfl

theorem wInv_def : wInv = List.replicate 42 (E (-1)) := rfl

/-- The relator family. -/
def R : Set (List (CoprodI Fam)) := {w, wInv}

theorem w_mem : w ∈ R := Or.inl rfl

theorem wInv_mem : wInv ∈ R := Or.inr rfl

theorem length_of_mem {r : List (CoprodI Fam)} (hr : r ∈ R) : r.length = 42 := by
  rcases hr with rfl | rfl
  · rw [w_def, List.length_replicate]
  · rw [wInv_def, List.length_replicate]

theorem inv_E_one : (E 1)⁻¹ = E (-1) := (E_neg 1).symm

theorem inv_E_neg_one : (E (-1))⁻¹ = E 1 := by
  have h := E_neg (-1)
  rw [neg_neg] at h
  exact h.symm

theorem symmetrized : LetterSymmetrized R := by
  constructor
  · rintro r hr n
    rcases hr with rfl | rfl
    · rw [w_def, List.rotate_replicate, ← w_def]
      exact w_mem
    · rw [wInv_def, List.rotate_replicate, ← wInv_def]
      exact wInv_mem
  · rintro r hr
    rcases hr with rfl | rfl
    · have hmap : ((w.map fun a => a⁻¹).reverse) = wInv := by
        rw [w_def, wInv_def]
        simp [inv_E_one]
      rw [hmap]
      exact wInv_mem
    · have hmap : ((wInv.map fun a => a⁻¹).reverse) = w := by
        rw [wInv_def, w_def]
        simp [inv_E_neg_one]
      rw [hmap]
      exact w_mem

theorem letters : ∀ r ∈ R, ∀ a ∈ r, L.len a ≤ 1 := by
  rintro r hr a ha
  rcases hr with rfl | rfl
  · rw [w_def] at ha
    rw [List.eq_of_mem_replicate ha]
    exact len_le_one (by norm_num)
  · rw [wInv_def] at ha
    rw [List.eq_of_mem_replicate ha]
    exact len_le_one (by norm_num)

theorem cyclicallyReduced : ∀ r ∈ R, LetterReduced L r := by
  rintro r hr
  rcases hr with rfl | rfl
  · intro n s t' a b hEq
    rw [w_def, List.rotate_replicate] at hEq
    have ha : a = E 1 :=
      List.eq_of_mem_replicate (n := 42) (by rw [hEq]; simp)
    have hb : b = E 1 :=
      List.eq_of_mem_replicate (n := 42) (by rw [hEq]; simp)
    have h11 : E 1 * E 1 = E 2 := by
      rw [← E_add]
      norm_num
    rw [ha, hb, h11]
    exact two_le_len (by norm_num) (by norm_num)
  · intro n s t' a b hEq
    rw [wInv_def, List.rotate_replicate] at hEq
    have ha : a = E (-1) :=
      List.eq_of_mem_replicate (n := 42) (by rw [hEq]; simp)
    have hb : b = E (-1) :=
      List.eq_of_mem_replicate (n := 42) (by rw [hEq]; simp)
    have h11 : E (-1) * E (-1) = E (-2) := by
      rw [← E_add]
      norm_num
    rw [ha, hb, h11]
    exact two_le_len (by norm_num) (by norm_num)

theorem slack : LetterFragmentSlack R (1 / 7) := by
  intro r hr
  rw [length_of_mem hr]
  norm_num

theorem metric : LetterMetricSmallCancellation R (1 / 7) := by
  intro p hp r hr _
  have hp0 : p = [] := by
    obtain ⟨r₁, h₁, r₂, h₂, hne, hp₁, hp₂⟩ := hp
    by_contra hpne
    obtain ⟨x, q, rfl⟩ := List.exists_cons_of_ne_nil hpne
    have hx₁ : x ∈ r₁ := hp₁.subset (by simp)
    have hx₂ : x ∈ r₂ := hp₂.subset (by simp)
    have key : ∀ s : List (CoprodI Fam), s ∈ R → x ∈ s →
        (s = w ∧ x = E 1) ∨ (s = wInv ∧ x = E (-1)) := by
      rintro s hs hxs
      rcases hs with rfl | rfl
      · exact Or.inl ⟨rfl,
          List.eq_of_mem_replicate (n := 42) (by rw [← w_def]; exact hxs)⟩
      · exact Or.inr ⟨rfl,
          List.eq_of_mem_replicate (n := 42) (by rw [← wInv_def]; exact hxs)⟩
    rcases key r₁ h₁ hx₁ with ⟨hs₁, hxa⟩ | ⟨hs₁, hxa⟩ <;>
      rcases key r₂ h₂ hx₂ with ⟨hs₂, hxb⟩ | ⟨hs₂, hxb⟩
    · exact hne (hs₁.trans hs₂.symm)
    · have hcon : (1 : ℤ) = -1 := E_inj (hxa.symm.trans hxb)
      norm_num at hcon
    · have hcon : (-1 : ℤ) = 1 := E_inj (hxa.symm.trans hxb)
      norm_num at hcon
    · exact hne (hs₁.trans hs₂.symm)
  rw [hp0, length_of_mem hr]
  norm_num

/-! ## 5.  The conclusion fails -/

theorem w_prod : w.prod = E 42 := by
  have hcast : ((42 : ℕ) : ℤ) = (42 : ℤ) := by norm_num
  rw [w_def, List.prod_replicate, E_pow, hcast]

end OsinRefutation

/-- **`OsinTheorem24` is false.**

The witness is `OsinRefutation`'s: a `42`-letter relator over `ℤ` all of whose
letters are `t`, so that the relator spells `t^42`, which the alphabet makes a
single letter.  Every hypothesis of `WeightedGreendlingerLeaf` holds -- the
family is symmetrized, cyclically reduced, made of letters, meets the fragment
slack at `lam = 1/7` exactly, and satisfies the metric condition vacuously,
because its two members share no letter -- while its conclusion demands a
relator of fewer than two letters.

The missing hypothesis is that a relator be a geodesic word; see this module's
header for that and for a second defect, in the notion of piece, that survives
adding it. -/
theorem not_osinTheorem24 : ¬ OsinTheorem24 := by
  intro hOsin
  have hleaf :=
    (hOsin OsinRefutation.Fam OsinRefutation.instFamGroup OsinRefutation.L
      OsinRefutation.R (1 / 7)).1
  have hbound : RelativeLengthBound OsinRefutation.L OsinRefutation.R :=
    hleaf OsinRefutation.hasGeo OsinRefutation.symmetrized
      OsinRefutation.cyclicallyReduced OsinRefutation.letters
      OsinRefutation.slack OsinRefutation.metric
  have hne : OsinRefutation.w.prod ≠ 1 := by
    rw [OsinRefutation.w_prod]
    exact OsinRefutation.E_ne_one (by norm_num)
  have hmem : OsinRefutation.w.prod ∈ letterRelatorSubgroup OsinRefutation.R :=
    mem_letterRelatorSubgroup OsinRefutation.w_mem
  obtain ⟨r, hr, hlt⟩ := hbound OsinRefutation.w.prod hne hmem
  have h1 : OsinRefutation.L.len OsinRefutation.w.prod ≤ 1 := by
    rw [OsinRefutation.w_prod]
    exact OsinRefutation.len_le_one (by norm_num)
  have h2 : r.length = 42 := OsinRefutation.length_of_mem hr
  omega

/-! ## 6.  The clause the leaf is missing -/

section Repair

variable {G : Bool → Type} [∀ b, Group (G b)]

/-- **A relator is a geodesic word**: its letter count is the relative length of
the element it spells.  Osin's relators are cycles whose subpaths are
quasi-geodesic; this is the linear form of that clause, and
`WeightedGreendlingerLeaf` does not ask for it. -/
def LetterGeodesic (L : RelativeLength G) (r : List (CoprodI G)) : Prop :=
  r.length = L.len r.prod

/-- **Osin's piece**, as opposed to the syntactic one: a prefix of one relator
that equals, *in the group*, a prefix of another. -/
def LetterIsGroupPiece (R : Set (List (CoprodI G))) (p : List (CoprodI G)) :
    Prop :=
  ∃ r₁ ∈ R, ∃ r₂ ∈ R, r₁ ≠ r₂ ∧ p <+: r₁ ∧
    ∃ q, q <+: r₂ ∧ p.prod = q.prod

/-- The metric condition over Osin's pieces. -/
def LetterMetricGroupSmallCancellation (R : Set (List (CoprodI G))) (lam : ℚ) :
    Prop :=
  ∀ p, LetterIsGroupPiece R p → ∀ r ∈ R, p <+: r →
    (p.length : ℚ) < lam * (r.length : ℚ)

/-- **The repaired condition is the stronger one**: a syntactic piece is a group
piece, taken with `q = p`.  So a design certifying `C'(1/8)` over
`LetterIsPiece` has certified strictly less than the repaired leaf consumes, and
`WeightedRouterDesign.metric` has to be restated, not reused. -/
theorem letterMetricSmallCancellation_of_group {R : Set (List (CoprodI G))}
    {lam : ℚ} (h : LetterMetricGroupSmallCancellation R lam) :
    LetterMetricSmallCancellation R lam := by
  intro p hp r hr hpre
  obtain ⟨r₁, h₁, r₂, h₂, hne, hp₁, hp₂⟩ := hp
  exact h p ⟨r₁, h₁, r₂, h₂, hne, hp₁, p, hp₂, rfl⟩ r hr hpre

end Repair

/-- **The witness fails the missing clause, and only that one.**  `w` has `42`
letters and spells an element of relative length at most `1`, so it is not a
geodesic word.  Everything else `WeightedGreendlingerLeaf` asks of it holds, so
this is the whole of what has to be added. -/
theorem not_geodesic_w :
    ¬ LetterGeodesic OsinRefutation.L OsinRefutation.w := by
  intro hgeo
  have hg : OsinRefutation.w.length
      = OsinRefutation.L.len OsinRefutation.w.prod := hgeo
  have h1 : OsinRefutation.w.length = 42 :=
    OsinRefutation.length_of_mem OsinRefutation.w_mem
  have h2 : OsinRefutation.L.len OsinRefutation.w.prod ≤ 1 := by
    rw [OsinRefutation.w_prod]
    exact OsinRefutation.len_le_one (by norm_num)
  omega

end RelHyp
end GGT
end GroupApproximation
