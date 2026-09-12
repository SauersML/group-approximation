import GroupApproximation.GGT.DGOProposition414OrientedSegment

/-!
# Extremal polygons for the least DGO sum bound

The child tuple produced by the balanced component surgery depends on the
input polygon.  Therefore it cannot first be fixed and then used to construct
a `SumBound`, whose definition quantifies over *all* polygons.  The least
constant `sumCost`, however, has an extremal-input principle: if it is positive,
the preceding constant fails, and pushing the negation through `SumBound`
produces one polygon on which every radius witness has sum at least `sumCost`.

Applying the component surgery only to that polygon is enough.  Its family
certificate gives one radius witness bounded by the sum of the child costs;
extremality supplies the reverse lower bound.  Thus the polygon-dependent
child tuple proves the numerical subdivision inequality required by Lemma
4.19, without the invalid uniformisation step.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents
open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- One fully admissible input to `SumBound`, with all polygon data retained. -/
structure SumBoundInput (D : RelGenSet G Λ) (b : ℝ) (n : ℕ) where
  basepoint : G
  word : List (RelLetter G Λ)
  cut : ℕ → ℕ
  target : Finset ℕ
  label : ℕ → Λ
  letters : ∀ a ∈ word, D.IsLetter a
  closed : RelLetter.listVal word = 1
  polygonCut : IsPolygonCut n word cut
  target_lt : ∀ s ∈ target, s < n
  target_edge : ∀ s ∈ target, cut (s + 1) = cut s + 1
  target_component : ∀ s ∈ target,
    IsComp (label s) word (cut s) (cut (s + 1))
  target_isolated : ∀ s ∈ target,
    IsIsolated D.fam (label s) basepoint word (cut s)
  quasi : ∀ s : ℕ, s < n → s ∉ target → ∀ p q : ℕ,
    cut s ≤ p → p ≤ q → q ≤ cut (s + 1) →
    ((q - p : ℕ) : ℝ) - b ≤
      ((wordDist D.alphabet.carrier
        (vertex basepoint word p) (vertex basepoint word q) : ℕ) : ℝ)

namespace SumBoundInput

/-- The original distinguished span at side `s`. -/
def span {D : RelGenSet G Λ} {b : ℝ} {n : ℕ}
    (P : SumBoundInput D b n) (s : ℕ) : G :=
  (vertex P.basepoint P.word (P.cut s))⁻¹ *
    vertex P.basepoint P.word (P.cut (s + 1))

/-- A radius witness for this particular input. -/
def HasRadiusWitnessAtMost {D : RelGenSet G Λ} {b : ℝ} {n : ℕ}
    (P : SumBoundInput D b n) (K : ℕ) : Prop :=
  ∃ r : ℕ → ℕ,
    (∀ s ∈ P.target,
      P.span s ∈ D.relBall (P.label s) (r s)) ∧
    ∑ s ∈ P.target, r s ≤ K

/-- A global sum bound specializes to every packaged input. -/
theorem hasRadiusWitnessAtMost_of_sumBound
    {D : RelGenSet G Λ} {b : ℝ} {n K : ℕ}
    (hK : SumBound D b n K) (P : SumBoundInput D b n) :
    P.HasRadiusWitnessAtMost K :=
  hK P.basepoint P.word P.cut P.target P.label P.letters P.closed
    P.polygonCut P.target_lt P.target_edge P.target_component
    P.target_isolated P.quasi

end SumBoundInput

/-- If the least sum constant is positive, one input realizes its lower-bound
property: every radius witness on that input has total at least `sumCost`. -/
theorem exists_extremal_sumBoundInput_of_pos
    (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    (n : ℕ) (hpos : 0 < sumCost D hsymm b hδ n) :
    ∃ P : SumBoundInput D (b : ℝ) n,
      ∀ r : ℕ → ℕ,
        (∀ s ∈ P.target,
          P.span s ∈ D.relBall (P.label s) (r s)) →
        sumCost D hsymm b hδ n ≤ ∑ s ∈ P.target, r s := by
  classical
  let K := sumCost D hsymm b hδ n
  have hnot : ¬ SumBound D (b : ℝ) n (K - 1) := by
    intro hsmall
    have hle : K ≤ K - 1 := sumCost_le D hsymm b hδ hsmall
    dsimp [K] at hle
    omega
  unfold SumBound at hnot
  push Not at hnot
  obtain ⟨v, word, cut, I, lam, hlet, hclosed, hcut, hI, hedge,
    hcomp, hiso, hquasi, hfail⟩ := hnot
  let P : SumBoundInput D (b : ℝ) n :=
    { basepoint := v
      word := word
      cut := cut
      target := I
      label := lam
      letters := hlet
      closed := hclosed
      polygonCut := hcut
      target_lt := hI
      target_edge := hedge
      target_component := hcomp
      target_isolated := hiso
      quasi := hquasi }
  refine ⟨P, ?_⟩
  intro r hr
  have hgt : K - 1 < ∑ s ∈ I, r s := hfail r hr
  dsimp [P, K] at hgt ⊢
  omega

/-- A family certificate on an extremal input gives the numerical child-cost
subdivision inequality. -/
theorem sumCost_le_childCosts_of_extremalCertificate
    (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    {n : ℕ} (P : SumBoundInput D (b : ℝ) n)
    (hextremal : ∀ r : ℕ → ℕ,
      (∀ s ∈ P.target,
        P.span s ∈ D.relBall (P.label s) (r s)) →
      sumCost D hsymm b hδ n ≤ ∑ s ∈ P.target, r s)
    (A : AuxiliaryCycleFamilyCertificate D hsymm b hδ n
      P.basepoint P.word P.cut P.target P.label) :
    sumCost D hsymm b hδ n ≤
      ∑ j, sumCost D hsymm b hδ (A.childSides j) := by
  obtain ⟨_hlower, _hupper, _hsmall, r, hrmem, hrsum⟩ :=
    consequences_of_auxiliaryCycleFamilyCertificate D hsymm b hδ A
  exact (hextremal r hrmem).trans hrsum

/-- For positive `sumCost`, any construction of a family certificate on the
extremal polygon supplies a polygon-dependent child tuple with all numerical
facts exported together. -/
theorem exists_extremal_family_consequences
    (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    (n : ℕ) (hpos : 0 < sumCost D hsymm b hδ n)
    (produce : ∀ P : SumBoundInput D (b : ℝ) n,
      Nonempty (AuxiliaryCycleFamilyCertificate D hsymm b hδ n
        P.basepoint P.word P.cut P.target P.label)) :
    ∃ (P : SumBoundInput D (b : ℝ) n)
        (A : AuxiliaryCycleFamilyCertificate D hsymm b hδ n
          P.basepoint P.word P.cut P.target P.label),
      n ≤ ∑ j, A.childSides j ∧
      (∑ j, A.childSides j ≤
        n + 6 * (A.chordLength * A.chordLength)) ∧
      (∀ j, 5 * A.childSides j ≤ 4 * n) ∧
      sumCost D hsymm b hδ n ≤
        ∑ j, sumCost D hsymm b hδ (A.childSides j) := by
  obtain ⟨P, hP⟩ :=
    exists_extremal_sumBoundInput_of_pos D hsymm b hδ n hpos
  let A := Classical.choice (produce P)
  have hcon := consequences_of_auxiliaryCycleFamilyCertificate D hsymm b hδ A
  refine ⟨P, A, hcon.1, hcon.2.1, hcon.2.2.1, ?_⟩
  exact sumCost_le_childCosts_of_extremalCertificate D hsymm b hδ P hP A

/-! ## The corrected quadratic assembly interface -/

/-- Proposition 4.14 from a direct numerical subdivision inequality for
`sumCost`.

Unlike `sumBound_linear_of_quadraticChordTraversal`, the last premise does not
ask for a uniform `SumBound` with polygon-dependent child sizes.  It asks for
the numerical inequality which the extremal-polygon argument above proves.
This is the interface into which the raw interval surgery feeds. -/
theorem sumBound_linear_of_quadraticCostSubdivision
    (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    (pieceOverhead sizeOverhead : ℕ → ℝ) (N : ℕ) (α ε : ℝ) (M₁ : ℕ)
    (hα0 : 0 < α) (hα1 : α < 1) (hε0 : 0 < ε)
    (hgain : Real.sqrt α * (1 + ε) ≤ 1)
    (hthresh : ∀ n : ℕ, M₁ < n →
      sizeOverhead n + pieceOverhead n ≤ ε * Real.sqrt n)
    (H : ∀ n : ℕ, N < n →
      ∃ (k : ℕ) (m : Fin k → ℕ) (chordLength : ℕ)
          (partners : List ℕ),
        (k : ℝ) ≤ pieceOverhead n ∧
        (sumCost D hsymm b hδ n : ℝ) ≤
          ∑ i, (sumCost D hsymm b hδ (m i) : ℝ) ∧
        (n : ℝ) ≤ ∑ i, (m i : ℝ) ∧
        (ChordPartnerQuadraticTraversalBound chordLength partners →
          (∑ i, (m i : ℝ)) ≤
            (n : ℝ) + 6 * (chordLength * chordLength)) ∧
        (6 * (chordLength * chordLength) : ℝ) ≤ sizeOverhead n ∧
        (∀ i, (m i : ℝ) ≤ α * n) ∧
        ChordPartnerQuadraticTraversalBound chordLength partners) :
    ∃ L : ℕ, ∀ n : ℕ, 1 ≤ n → SumBound D (b : ℝ) n (L * n) := by
  obtain ⟨L, hlinear⟩ :=
    DGO.nat_linear_of_subdivision_of_sqrt_overhead
      (sumCost D hsymm b hδ) pieceOverhead sizeOverhead N α ε M₁
      hα0 hα1 hε0 hgain hthresh (by
        intro n hn
        obtain ⟨k, m, chordLength, partners, hk, hcost, hnle, hsize,
          hquadratic, hm, htraversal⟩ := H n hn
        have hsumle : (∑ i, (m i : ℝ)) ≤ (n : ℝ) + sizeOverhead n :=
          (hsize htraversal).trans (by
            simpa using (add_le_add_left hquadratic (n : ℝ)))
        exact ⟨k, m, hk, hcost, hnle, hsumle, hm⟩)
  refine ⟨L, ?_⟩
  intro n hn
  exact SumBound.mono (sumBound_sumCost D hsymm b hδ n) (hlinear n hn)

/-- A certified extremal family exports the direct quadratic subdivision tuple
consumed by `sumBound_linear_of_quadraticCostSubdivision`. -/
theorem exists_quadraticCostSubdivisionData_of_extremalFamily
    (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    {n : ℕ} (P : SumBoundInput D (b : ℝ) n)
    (hextremal : ∀ r : ℕ → ℕ,
      (∀ s ∈ P.target,
        P.span s ∈ D.relBall (P.label s) (r s)) →
      sumCost D hsymm b hδ n ≤ ∑ s ∈ P.target, r s)
    (A : AuxiliaryCycleFamilyCertificate D hsymm b hδ n
      P.basepoint P.word P.cut P.target P.label) :
    ∃ (k : ℕ) (m : Fin k → ℕ) (chordLength : ℕ)
        (partners : List ℕ),
      sumCost D hsymm b hδ n ≤
        ∑ i, sumCost D hsymm b hδ (m i) ∧
      n ≤ ∑ i, m i ∧
      (ChordPartnerQuadraticTraversalBound chordLength partners →
        ∑ i, m i ≤ n + 6 * (chordLength * chordLength)) ∧
      (∀ i, 5 * m i ≤ 4 * n) ∧
      ChordPartnerQuadraticTraversalBound chordLength partners := by
  refine ⟨A.k, A.childSides, A.chordLength, A.partners, ?_, A.count_lower,
    A.count_upper, A.child_small, A.traversal⟩
  exact sumCost_le_childCosts_of_extremalCertificate D hsymm b hδ P
    hextremal A

end DGOProposition414
end GGT
end GroupApproximation
