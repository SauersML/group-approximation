import GroupApproximation.Sofic.OsinWeightedMetric

/-!
# What the weighted leaf statements still have to exclude

The hypotheses of `WeightedGreendlingerLeaf` inspect the *lists* used as
relators.  The conclusion, however, concerns the products of those lists in
the ambient free product.  In particular, letter-level small cancellation by
itself does not say that a long relator list has a long ambient product: a long
cyclically reduced word in the chosen generators of the partner can already be
a short element because of relations inside that partner.

The first theorem below isolates this missing gate.  It is a no-go theorem, not
an additional input: if all six advertised leaf hypotheses hold and one
nonidentity element of the relator subgroup is short compared with every
relator, then the proposed weighted Greendlinger leaf is false.  Taking the
short element to be the product of one of the relator lists gives the directly
usable form `not_weightedGreendlingerLeaf_of_short_relatorProduct`.

For example, the intended elementary counterexample schema takes the partner
to be a finite-rank free abelian group, chooses distinct generators
`x₁, ..., x₄₂`, also declares their product to be a generator of the weighted
alphabet, and symmetrizes the list `[x₁, ..., x₄₂]`.  The list has no long
letter-piece, while its ambient product has length one.  The theorem below is
the exact final implication needed after spelling that finite schema out.

The torsion companion records the analogous semantic test: over a torsion-free
ambient group, any finite-order element surviving in the quotient refutes the
weighted torsion leaf.  Thus neither open leaf may be installed universally
without first relating the partner's internal presentation to the relator
diagrams.
-/

namespace GroupApproximation
namespace OsinWeightedMetric

open Monoid Monoid.CoprodI OsinSmallCancellation

section Greendlinger

variable {G : Bool → Type} [∀ b, Group (G b)]

/-- A short nonidentity element of the relator subgroup contradicts the
conclusion promised by the weighted Greendlinger leaf.  All six premises of the
leaf are displayed explicitly, so this theorem cannot hide a diagram lemma. -/
theorem not_weightedGreendlingerLeaf_of_short
    {L : RelativeLength G} {R : Set (List (CoprodI G))} {lam : ℚ}
    (hgeo : HasGeodesicSpellings L)
    (hsym : LetterSymmetrized R)
    (hred : ∀ r ∈ R, LetterReduced L r)
    (hletters : ∀ r ∈ R, ∀ a ∈ r, L.len a ≤ 1)
    (hslack : LetterFragmentSlack R lam)
    (hmetric : LetterMetricSmallCancellation R lam)
    {t : CoprodI G} (ht : t ≠ 1)
    (hmem : t ∈ letterRelatorSubgroup R)
    (hshort : ∀ r ∈ R, 2 * L.len t ≤ r.length) :
    ¬ WeightedGreendlingerLeaf L R lam := by
  intro hleaf
  exact
    (not_relativeLengthBound_of_short ht hmem hshort)
      (hleaf hgeo hsym hred hletters hslack hmetric)

/-- The concrete form in which the short element is the ambient product of a
relator list.  Membership in the normal closure is then a theorem, rather than
an extra hypothesis. -/
theorem not_weightedGreendlingerLeaf_of_short_relatorProduct
    {L : RelativeLength G} {R : Set (List (CoprodI G))} {lam : ℚ}
    (hgeo : HasGeodesicSpellings L)
    (hsym : LetterSymmetrized R)
    (hred : ∀ r ∈ R, LetterReduced L r)
    (hletters : ∀ r ∈ R, ∀ a ∈ r, L.len a ≤ 1)
    (hslack : LetterFragmentSlack R lam)
    (hmetric : LetterMetricSmallCancellation R lam)
    {r₀ : List (CoprodI G)} (hr₀ : r₀ ∈ R) (hr₀_ne : r₀.prod ≠ 1)
    (hshort : ∀ r ∈ R, 2 * L.len r₀.prod ≤ r.length) :
    ¬ WeightedGreendlingerLeaf L R lam :=
  not_weightedGreendlingerLeaf_of_short hgeo hsym hred hletters hslack hmetric
    hr₀_ne (mem_letterRelatorSubgroup hr₀) hshort

end Greendlinger

section Torsion

variable {G : Bool → Type} [∀ b, Group (G b)]

/-- Over a torsion-free ambient free product, a nonidentity finite-order
quotient element is a direct counterexample to the conclusion of the weighted
torsion leaf. -/
theorem not_weightedTorsionLeaf_of_quotient_torsion
    {L : RelativeLength G} {R : Set (List (CoprodI G))} {lam : ℚ}
    (hgeo : HasGeodesicSpellings L)
    (hsym : LetterSymmetrized R)
    (hred : ∀ r ∈ R, LetterReduced L r)
    (hletters : ∀ r ∈ R, ∀ a ∈ r, L.len a ≤ 1)
    (hslack : LetterFragmentSlack R lam)
    (hmetric : LetterMetricSmallCancellation R lam)
    (hnpp : LetterNoProperPower R)
    (hamb : IsPowerTorsionFree (CoprodI G))
    {q : CoprodI G ⧸ letterRelatorSubgroup R} {n : ℕ}
    (hn : 0 < n) (hqpow : q ^ n = 1) (hq : q ≠ 1) :
    ¬ WeightedTorsionLeaf L R lam := by
  intro hleaf
  have hlifts : TorsionLifts (letterRelatorSubgroup R) :=
    hleaf hgeo hsym hred hletters hslack hmetric hnpp
  exact hq (isPowerTorsionFree_of_torsionLifts hamb hlifts q n hn hqpow)

end Torsion

end OsinWeightedMetric
end GroupApproximation
