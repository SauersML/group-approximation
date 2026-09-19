import GroupApproximation.GGT.DGOProposition414BalancedSplit
import GroupApproximation.GGT.DGOAssemblySubdivisionGeneral
import GroupApproximation.GGT.DGOShortIsolatingCycleGeneral

/-!
# General-parameter inputs for DGO Proposition 4.14

The genuine quasi-geodesic estimate retains both parameters. `bookkeeping`
only exposes the same finite polygon to the existing component-surgery API;
its word-length error is never used to choose a geometric constant.
-/

namespace GroupApproximation.GGT.DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents
open GroupApproximation.WordMetric

universe u w
variable {G : Type u} [Group G] {Λ : Type w}

/-- An input polygon with the original general quasi-geodesic estimates. -/
structure QuasiSumBoundInput (D : RelGenSet G Λ) (mu b : ℝ) (n : ℕ) where
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
    ((q - p : ℕ) : ℝ) / mu - b ≤
      ((wordDist D.alphabet.carrier
        (vertex basepoint word p) (vertex basepoint word q) : ℕ) : ℝ)

namespace QuasiSumBoundInput

/-- The original distinguished span at side `s`. -/
def span {D : RelGenSet G Λ} {mu b : ℝ} {n : ℕ}
    (P : QuasiSumBoundInput D mu b n) (s : ℕ) : G :=
  (vertex P.basepoint P.word (P.cut s))⁻¹ *
    vertex P.basepoint P.word (P.cut (s + 1))

/-- A radius witness for this particular input. -/
def HasRadiusWitnessAtMost {D : RelGenSet G Λ} {mu b : ℝ} {n : ℕ}
    (P : QuasiSumBoundInput D mu b n) (K : ℕ) : Prop :=
  ∃ r : ℕ → ℕ,
    (∀ s ∈ P.target,
      P.span s ∈ D.relBall (P.label s) (r s)) ∧
    ∑ s ∈ P.target, r s ≤ K

/-- The same finite polygon, exposed to the combinatorial surgery API.
The error here is deliberately not a uniform geometric estimate. -/
def bookkeeping {D : RelGenSet G Λ} {mu b : ℝ} {n : ℕ}
    (P : QuasiSumBoundInput D mu b n) :
    SumBoundInput D (P.word.length : ℝ) n where
  basepoint := P.basepoint
  word := P.word
  cut := P.cut
  target := P.target
  label := P.label
  letters := P.letters
  closed := P.closed
  polygonCut := P.polygonCut
  target_lt := P.target_lt
  target_edge := P.target_edge
  target_component := P.target_component
  target_isolated := P.target_isolated
  quasi := by
    intro s hs _ p q _ _ hq
    have hlength := P.polygonCut.le_length (by omega : s + 1 ≤ n)
    have hdiff : q - p ≤ P.word.length := by omega
    have hdiffR : ((q - p : ℕ) : ℝ) ≤ (P.word.length : ℝ) := by exact_mod_cast hdiff
    have hnonneg := Nat.cast_nonneg (α := ℝ)
      (wordDist D.alphabet.carrier (vertex P.basepoint P.word p)
        (vertex P.basepoint P.word q))
    linarith

/-- Single-edge distinguished sides satisfy the genuine estimate after one
unit of additive slack. All other sides retain the supplied estimate. -/
theorem quasi_all {D : RelGenSet G Λ} {mu b : ℝ} {n : ℕ}
    (P : QuasiSumBoundInput D mu b n) (hmu : 1 ≤ mu) (hb : 0 ≤ b) :
    ∀ s : ℕ, s < n → ∀ p q : ℕ,
      P.cut s ≤ p → p ≤ q → q ≤ P.cut (s + 1) →
      ((q - p : ℕ) : ℝ) / mu - (b + 1) ≤
        ((wordDist D.alphabet.carrier
          (vertex P.basepoint P.word p) (vertex P.basepoint P.word q) : ℕ) : ℝ) := by
  intro s hs p q hp hpq hq
  by_cases hsI : s ∈ P.target
  · have hedge := P.target_edge s hsI
    have hdiff : q - p ≤ 1 := by omega
    have hdiffR : ((q - p : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hdiff
    have hmu0 : 0 < mu := lt_of_lt_of_le zero_lt_one hmu
    have hdiv : ((q - p : ℕ) : ℝ) / mu ≤ 1 :=
      (div_le_iff₀ hmu0).mpr (by linarith)
    have hnonneg := Nat.cast_nonneg (α := ℝ)
      (wordDist D.alphabet.carrier (vertex P.basepoint P.word p)
        (vertex P.basepoint P.word q))
    linarith
  · have h := P.quasi s hs hsI p q hp hpq hq
    linarith

/-- The original polygon is quasi-geodesic on all sides after the same slack. -/
theorem toPolygon {D : RelGenSet G Λ} {mu b : ℝ} {n : ℕ}
    (P : QuasiSumBoundInput D mu b n) (hmu : 1 ≤ mu) (hb : 0 ≤ b) :
    IsQuasiGeodesicPolygon D mu (b + 1) n P.basepoint P.word :=
  ⟨P.letters, P.closed, P.cut, P.polygonCut.start, P.polygonCut.finish,
    P.polygonCut.mono, P.quasi_all hmu hb⟩

/-- The uniform chord bound comes from the genuine parameters, while the
existing split record retains the exact word, components and cut indices. -/
theorem exists_balancedSplitData_quasi (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ}
    (mu b : ℝ) (hmu : 1 ≤ mu) (hb : 0 ≤ b)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ) :
    ∃ R : ℕ, ∀ {n k : ℕ}, 8 ≤ n → n ≤ 2 ^ k →
      ∀ P : QuasiSumBoundInput D mu b n,
        Nonempty (BalancedSplitData D hsymm P.word.length hδ P.bookkeeping k R) := by
  obtain ⟨R, hR⟩ := exists_balanced_interior_cut_word_quasi D mu (b + 1)
    (lt_of_lt_of_le zero_lt_one hmu) (by linarith) hδ
  refine ⟨R, ?_⟩
  intro n k hn hk P
  obtain ⟨a, c, i, j, hac, hcn, hlower, hupper, hai, hia, hcj, hjc, hdist⟩ :=
    hR hn hk P.basepoint P.word P.cut P.letters P.closed P.polygonCut
      (P.quasi_all hmu hb)
  let polygon : IsCutPolygon D ((P.word.length + 1 : ℕ) : ℝ) n
      P.basepoint P.word P.cut :=
    isCutPolygon_of_sumBound_shape D P.word.length n P.basepoint P.word P.cut
      P.target P.letters P.closed P.polygonCut P.target_edge P.bookkeeping.quasi
  obtain ⟨chord, cut₁, cut₂, hchord, hcut₁, hcut₂, hclosed₁,
    hclosed₂, hletters₁, hletters₂, hlength, hcounts⟩ :=
    exists_interior_half_polygon_data D P.basepoint P.word P.cut
      polygon hac hcn hlower hupper hai hia hcj hjc hdist
  exact ⟨{
    firstSide := a
    secondSide := c
    firstVertex := i
    secondVertex := j
    side_order := hac
    secondSide_lt := hcn
    quarter_lower := hlower
    quarter_upper := hupper
    firstVertex_mem := ⟨hai, hia⟩
    secondVertex_mem := ⟨hcj, hjc⟩
    chord := chord
    firstCut := cut₁
    secondCut := cut₂
    chord_geodesic := hchord
    first_polygonCut := hcut₁
    second_polygonCut := hcut₂
    first_closed := hclosed₁
    second_closed := hclosed₂
    first_letters := hletters₁
    second_letters := hletters₂
    chord_length_le := hlength
    side_counts := hcounts
  }⟩

end QuasiSumBoundInput
end GroupApproximation.GGT.DGOProposition414

#audit_axioms GroupApproximation.GGT.DGOProposition414.QuasiSumBoundInput.bookkeeping
#audit_axioms GroupApproximation.GGT.DGOProposition414.QuasiSumBoundInput.toPolygon
#audit_axioms GroupApproximation.GGT.DGOProposition414.QuasiSumBoundInput.exists_balancedSplitData_quasi
