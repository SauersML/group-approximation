import GroupApproximation.GGT.RelHypOsin24CayleyLeaf

/-!
# The Greendlinger content, step one: what the diagram argument has to deliver

`GGT/RelHypOsin24CayleyLeaf.lean` states Osin's Theorem 2.4 at the relative
Cayley graph.  Its Greendlinger half concludes `RelativeLengthBound`: a
nonidentity element of the relator subgroup is longer than half of some
relator's letter count.  Osin's own conclusion, like Greendlinger's, is
different in form -- a word representing such an element **contains a subword
that is more than `(1 - 3λ)` of a relator** -- and this module proves that the
two are the same statement, exactly, at `λ = 1/6`, and that the first implies
the second for every `λ ≤ 1/6`.

That is worth having before any diagram is drawn, for three reasons.

* It fixes the target.  What the van Kampen argument must produce is the arc
  bound; `relativeLengthBound_of_arcBound` then closes the leaf's Greendlinger
  half with no further geometry.  The remaining obligation is therefore a single
  quantitative statement, written out in the header of section 1 and in the
  hypothesis of that theorem, rather than a leaf.
* It explains the constants.  `1 - 3λ ≥ 1/2` is exactly `λ ≤ 1/6`, which is why
  the fragment slack of `Sofic/OsinWeightedMetric.lean` is stated at `1/6` and
  the designs are certified at `1/7` or `1/8`: the slack is what is left over
  after the arc bound is converted to a length bound.
* It is sharp.  `relativeLengthBound_iff_arcBound_sixth` shows that at `λ = 1/6`
  no information is lost in either direction, so the length-bound form of the
  conclusion is not a weakening of Greendlinger's -- it is Greendlinger's, at
  the boundary constant.

Section 2 collects the piece arithmetic the diagram argument runs on: pieces are
short, three of them cannot cover a relator, and the group-piece condition is
monotone in `λ`, so a design certifying `C'(1/8)` has certified `C'(1/7)`.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open Monoid Monoid.CoprodI
open GroupApproximation.OsinWeightedMetric

variable {G : Bool → Type} [∀ b, Group (G b)]

/-! ## 1.  The arc bound and the length bound

The arc bound, spelled out: for every `g ≠ 1` in the relator subgroup there is a
relator `r` with

    (1 - 3 * lam) * |r| < |g|

in the relative metric.  This is what Greendlinger's lemma delivers -- a
subword of a geodesic spelling of `g` that is more than `(1 - 3λ)` of `r`, whose
letter count is therefore a lower bound for `|g|` -- and it is all the leaf's
Greendlinger half needs. -/

/-- **The arc bound implies the leaf's conclusion**, for every `λ ≤ 1/6`.

The whole content is `1 - 3λ ≥ 1/2`.  No geometry, no diagram, and no
hypothesis on the relator family: whatever produces the arc bound produces
`RelativeLengthBound`. -/
theorem relativeLengthBound_of_arcBound {L : RelativeLength G}
    {R : Set (List (CoprodI G))} {lam : ℚ} (hlam : lam ≤ 1 / 6)
    (harc : ∀ g : CoprodI G, g ≠ 1 → g ∈ letterRelatorSubgroup R →
      ∃ r ∈ R, (1 - 3 * lam) * (r.length : ℚ) < (L.len g : ℚ)) :
    RelativeLengthBound L R := by
  intro g hg hmem
  obtain ⟨r, hr, hlt⟩ := harc g hg hmem
  refine ⟨r, hr, ?_⟩
  have h0 : (0 : ℚ) ≤ (r.length : ℚ) := Nat.cast_nonneg _
  have h1 : (1 / 2 : ℚ) * (r.length : ℚ) ≤ (1 - 3 * lam) * (r.length : ℚ) :=
    mul_le_mul_of_nonneg_right (by linarith) h0
  have h2 : (r.length : ℚ) < 2 * (L.len g : ℚ) := by linarith
  have h3 : ((r.length : ℕ) : ℚ) < ((2 * L.len g : ℕ) : ℚ) := by
    push_cast
    linarith
  exact_mod_cast h3

/-- **The length bound implies the arc bound**, for every `λ ≥ 1/6`.  Together
with the previous theorem this pins the two forms of Greendlinger's conclusion
to each other at the boundary constant. -/
theorem arcBound_of_relativeLengthBound {L : RelativeLength G}
    {R : Set (List (CoprodI G))} {lam : ℚ} (hlam : 1 / 6 ≤ lam)
    (hb : RelativeLengthBound L R) :
    ∀ g : CoprodI G, g ≠ 1 → g ∈ letterRelatorSubgroup R →
      ∃ r ∈ R, (1 - 3 * lam) * (r.length : ℚ) < (L.len g : ℚ) := by
  intro g hg hmem
  obtain ⟨r, hr, hlt⟩ := hb g hg hmem
  refine ⟨r, hr, ?_⟩
  have h0 : (0 : ℚ) ≤ (r.length : ℚ) := Nat.cast_nonneg _
  have h1 : ((r.length : ℕ) : ℚ) < ((2 * L.len g : ℕ) : ℚ) := by exact_mod_cast hlt
  have h2 : (r.length : ℚ) < 2 * (L.len g : ℚ) := by push_cast at h1; linarith
  have h3 : (1 - 3 * lam) * (r.length : ℚ) ≤ (1 / 2 : ℚ) * (r.length : ℚ) :=
    mul_le_mul_of_nonneg_right (by linarith) h0
  linarith

/-- **At `λ = 1/6` the two forms are the same statement.**  So the repository's
`RelativeLengthBound` is Greendlinger's conclusion at the boundary constant, not
a weakening of it. -/
theorem relativeLengthBound_iff_arcBound_sixth {L : RelativeLength G}
    {R : Set (List (CoprodI G))} :
    RelativeLengthBound L R ↔
      ∀ g : CoprodI G, g ≠ 1 → g ∈ letterRelatorSubgroup R →
        ∃ r ∈ R, (1 - 3 * (1 / 6 : ℚ)) * (r.length : ℚ) < (L.len g : ℚ) :=
  ⟨fun h => arcBound_of_relativeLengthBound le_rfl h,
    fun h => relativeLengthBound_of_arcBound le_rfl h⟩

/-- **The fourth-generation Greendlinger leaf, from the arc bound.**

The leaf's seven hypotheses are not used: whatever produces the arc bound for a
family produces the leaf for it.  So the Greendlinger half of
`OsinTheorem24Cayley` is exactly the demand that the arc bound hold for every
family satisfying those seven, and the diagram argument is the only thing
between them.  This is the relative-metric twin of
`Sofic.GreendlingerFreeGate.greendlingerConclusion_of_sharp`, which does the
same for the free case at the same constant. -/
theorem weightedGreendlingerLeafCayley_of_arcBound
    {X : RelativeGeneratingSet (CoprodI G) (fun _ : Unit => sourceFactor G)}
    {R : Set (List (CoprodI G))} {rho : ℕ} {lam : ℚ} (hlam : lam ≤ 1 / 6)
    (harc : ∀ g : CoprodI G, g ≠ 1 → g ∈ letterRelatorSubgroup R →
      ∃ r ∈ R, (1 - 3 * lam) * (r.length : ℚ) < ((relLengthOf X).len g : ℚ)) :
    WeightedGreendlingerLeafCayley X R rho lam :=
  fun _ _ _ _ _ _ _ => relativeLengthBound_of_arcBound hlam harc

/-! ## 2.  The piece arithmetic the diagram argument runs on -/

/-- **A group piece is short**: the metric condition, named at the shape the
counting arguments use. -/
theorem length_lt_of_isGroupPiece {R : Set (List (CoprodI G))} {lam : ℚ}
    (h : LetterMetricGroupSmallCancellation R lam) {p r : List (CoprodI G)}
    (hp : LetterIsGroupPiece R p) (hr : r ∈ R) (hpre : p <+: r) :
    (p.length : ℚ) < lam * (r.length : ℚ) :=
  h p hp r hr hpre

/-- **The group-piece condition is monotone in `λ`**, exactly as its syntactic
twin `letterMetricSmallCancellation_mono`.  A design certifying `C'(1/8)` has
certified `C'(1/7)`, which is what the leaves are stated at. -/
theorem letterMetricGroupSmallCancellation_mono {R : Set (List (CoprodI G))}
    {lam lam' : ℚ} (h : lam ≤ lam')
    (hm : LetterMetricGroupSmallCancellation R lam) :
    LetterMetricGroupSmallCancellation R lam' := by
  intro p hp r hr hpre
  have h1 := hm p hp r hr hpre
  have h2 : lam * (r.length : ℚ) ≤ lam' * (r.length : ℚ) :=
    mul_le_mul_of_nonneg_right h (Nat.cast_nonneg _)
  linarith

/-- **A relator is never a piece of itself.**  At `lam ≤ 1` the metric condition
applied to `r` as a prefix of itself is already a contradiction, so the
symmetrized family is never degenerate in the way that would let one relator be
read off another. -/
theorem not_isGroupPiece_self {R : Set (List (CoprodI G))} {lam : ℚ}
    (hlam : lam ≤ 1) (h : LetterMetricGroupSmallCancellation R lam)
    {r : List (CoprodI G)} (hr : r ∈ R) : ¬ LetterIsGroupPiece R r := by
  intro hp
  have h1 := h r hp r hr (List.prefix_refl r)
  have h0 : (0 : ℚ) ≤ (r.length : ℚ) := Nat.cast_nonneg _
  have h2 : lam * (r.length : ℚ) ≤ 1 * (r.length : ℚ) :=
    mul_le_mul_of_nonneg_right hlam h0
  linarith

/-- **A relator with a piece is nonempty**, at every constant: the empty relator
admits no piece, since a piece would have to be shorter than `lam * 0`. -/
theorem length_pos_of_isGroupPiece {R : Set (List (CoprodI G))} {lam : ℚ}
    (h : LetterMetricGroupSmallCancellation R lam)
    {p r : List (CoprodI G)} (hp : LetterIsGroupPiece R p) (hr : r ∈ R)
    (hpre : p <+: r) : 0 < r.length := by
  rcases Nat.eq_zero_or_pos r.length with hz | hpos
  · exfalso
    have h1 := h p hp r hr hpre
    have h0 : (0 : ℚ) ≤ (p.length : ℚ) := Nat.cast_nonneg _
    have hz' : ((r.length : ℕ) : ℚ) = 0 := by rw [hz]; norm_num
    rw [hz', mul_zero] at h1
    linarith
  · exact hpos

/-- **Three pieces cannot cover half a relator.**

The counting fact behind Greendlinger's lemma: at `λ ≤ 1/6` the total length of
three pieces of `r` is less than `|r|/2`, so a boundary face of a van Kampen
diagram whose exterior arc is covered by three interior arcs still has more than
half of its boundary outside.  It is the same inequality `3λ ≤ 1/2` that section
1 turns into the length bound. -/
theorem sum_three_groupPieces_lt {R : Set (List (CoprodI G))} {lam : ℚ}
    (hlam : lam ≤ 1 / 6) (h : LetterMetricGroupSmallCancellation R lam)
    {p₁ p₂ p₃ r : List (CoprodI G)} (hr : r ∈ R)
    (h₁ : LetterIsGroupPiece R p₁) (hp₁ : p₁ <+: r)
    (h₂ : LetterIsGroupPiece R p₂) (hp₂ : p₂ <+: r)
    (h₃ : LetterIsGroupPiece R p₃) (hp₃ : p₃ <+: r) :
    (p₁.length : ℚ) + (p₂.length : ℚ) + (p₃.length : ℚ)
      < (1 / 2 : ℚ) * (r.length : ℚ) := by
  have e₁ := h p₁ h₁ r hr hp₁
  have e₂ := h p₂ h₂ r hr hp₂
  have e₃ := h p₃ h₃ r hr hp₃
  have h0 : (0 : ℚ) ≤ (r.length : ℚ) := Nat.cast_nonneg _
  have hle : lam * (r.length : ℚ) ≤ (1 / 6 : ℚ) * (r.length : ℚ) :=
    mul_le_mul_of_nonneg_right hlam h0
  linarith

end RelHyp
end GGT
end GroupApproximation
