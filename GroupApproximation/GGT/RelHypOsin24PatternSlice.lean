import GroupApproximation.GGT.RelHypOsin24PatternPigeonhole
import GroupApproximation.GGT.RelHypOsin24ClassificationBridge

/-!
# Osin's repeated-pattern to peripheral-slice frontier

After the finite metric-to-pattern pigeonhole, Osin's Lemmas `cyc1`, `qc1`,
and `qc-hyp` use relative components and the cyclic centralizer argument to
place an infinite repeated-pattern subfamily in one fixed set
`K h H_λ`, with the right factor in a bounded relative ball.  This file names
that exact geometric step and proves all consequences that only need an
infinite subfamily.

The subfamily form is strictly weaker than the earlier
`RelativeBoundedPowerExtractionStatement`, whose conclusion required every
index of the original bounded set to lie in one slice.  It is the form used by
the power-pigeonhole contradiction, and it is the source-faithful frontier for
the remaining centralizer/quasi-convexity estimate in Memoirs Theorem 1.10.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v

/-- **Osin's repeated-pattern slice estimate.**  A bounded family of powers
whose labelled relative spellings share one skeleton has an infinite
subfamily in one fixed peripheral double-coset slice.  The right factor has a
bounded relative metric, exactly as in the source's `cyc1`/`qc1` argument. -/
def RepeatedPatternPeripheralSliceStatement : Prop :=
  ∀ (G : Type u) (_ : Group G) (I : Type v) [Finite I] [Nonempty I]
    (D : RelGenSet G I),
    D.base.Finite → D.IsHyperbolicallyEmbedded → ∀ g : G,
      IsHyperbolicElement D.fam g →
        (∀ n : ℕ, 0 < n → g ^ n ≠ 1) →
          ∀ N : ℕ, ∀ p : RelativeWordPattern G I, ∀ T : Set ℕ,
            T.Infinite →
              (∀ q : ℕ, q ∈ T → ∃ w : List (RelLetter G I),
                (∀ a ∈ w, D.IsLetter a) ∧ w.length ≤ N ∧
                  relativeWordPattern w = p ∧ RelLetter.listVal w = g ^ q) →
              ∃ T' : Set ℕ, T' ⊆ T ∧ T'.Infinite ∧
                ∃ (lam : I) (n : ℕ) (k h : G),
                  ∀ q : ℕ, q ∈ T' →
                    ∃ z : G, z ∈ D.relBall lam n ∧ g ^ q = k * h * z

/-- The weaker extraction target used by the power-unbounded argument. -/
def RelativeBoundedPowerSubsequenceExtractionStatement : Prop :=
  ∀ (G : Type u) (_ : Group G) (I : Type v) [Finite I] [Nonempty I]
    (D : RelGenSet G I),
    D.base.Finite → D.IsHyperbolicallyEmbedded → ∀ g : G,
      IsHyperbolicElement D.fam g →
        (∀ n : ℕ, 0 < n → g ^ n ≠ 1) →
      ∀ R : ℝ, ∀ S : Set ℕ, S.Infinite →
        (∀ q : ℕ, q ∈ S →
          dist (Cayley.base D.alphabet) ((g ^ q) • Cayley.base D.alphabet) ≤ R) →
        ∃ T : Set ℕ, T ⊆ S ∧ T.Infinite ∧
          ∃ (lam : I) (n : ℕ) (k h : G),
            ∀ q : ℕ, q ∈ T →
              ∃ z : G, z ∈ D.relBall lam n ∧ g ^ q = k * h * z

/-- The repeated-pattern slice estimate implies the weaker extraction target
by the proved metric-to-pattern pigeonhole. -/
theorem relativeBoundedPowerSubsequenceExtraction_of_patternSlice
    (hSlice : RepeatedPatternPeripheralSliceStatement.{u, v}) :
    RelativeBoundedPowerSubsequenceExtractionStatement.{u, v} := by
  intro G instG I _ _ D hbase hemb g hhyper hord R S hS hbounded
  letI : Group G := instG
  obtain ⟨N, p, T, hTS, hT, hpattern⟩ :=
    metricBoundedRepeatedRelativePattern_proved G instG I D hbase g R S hS
      hbounded
  obtain ⟨T', hT'T, hT'inf, lam, n, k, h, hdecomp⟩ :=
    hSlice G instG I D hbase hemb g hhyper hord N p T hT hpattern
  exact ⟨T', hT'T.trans hTS, hT'inf, lam, n, k, h, hdecomp⟩

/-- An infinite-subfamily extraction contradicts a non-parabolic infinite-order
element whenever the original power orbit were bounded. -/
theorem isEscaping_of_relativeBoundedPowerSubsequenceExtraction
    (hExtract : RelativeBoundedPowerSubsequenceExtractionStatement.{u, v})
    {G : Type u} [Group G] {I : Type v} [Finite I] [Nonempty I]
    (D : RelGenSet G I) (hbase : D.base.Finite)
    (hemb : D.IsHyperbolicallyEmbedded) {g : G}
    (hhyper : IsHyperbolicElement D.fam g)
    (hord : ∀ n : ℕ, 0 < n → g ^ n ≠ 1) :
    IsEscaping g (Cayley.base D.alphabet) := by
  classical
  by_contra hnot
  obtain ⟨R, hSraw⟩ := boundedPowerSubsequence_proved
    G inferInstance (Cayley D.alphabet) inferInstance inferInstance g
      (Cayley.base D.alphabet) hnot
  let S : Set ℕ :=
    {q : ℕ | dist (Cayley.base D.alphabet)
      ((g ^ q) • Cayley.base D.alphabet) ≤ R}
  have hS : S.Infinite := by
    simpa [S] using hSraw
  obtain ⟨T, hTS, hT, lam, n, k, h, hdecomp⟩ :=
    hExtract G inferInstance I D hbase hemb g hhyper hord R S hS (by
      intro q hq
      exact hq)
  exact not_fixed_boundedPenetration_power_slice D hemb hhyper hord lam n k h T hT
    hdecomp

/-- Source assembly: once the repeated-pattern component estimate is supplied,
the finite-family relative power escape statement follows. -/
theorem finiteFamilyRelativePowerEscape_of_patternSlice
    (hSlice : RepeatedPatternPeripheralSliceStatement.{u, v}) :
    FiniteFamilyRelativePowerEscapeStatement.{u, v} := by
  classical
  intro G instG I _ D hbase hemb g hhyper hord
  letI : Group G := instG
  by_cases hI : IsEmpty I
  · letI : IsEmpty I := hI
    exact finiteAlphabetRelativePowerEscape_emptyModel D hbase g hord
  · letI : Nonempty I := not_isEmpty_iff.mp hI
    exact isEscaping_of_relativeBoundedPowerSubsequenceExtraction
      (relativeBoundedPowerSubsequenceExtraction_of_patternSlice hSlice)
      D hbase hemb hhyper hord

/-- The one-point model is vacuous under the infinite-order premise, so the
repeated-pattern slice statement's conclusion follows by contradiction. -/
theorem repeatedPatternPeripheralSlice_trivialModel
    {I : Type v} [Finite I] [Nonempty I] (D : RelGenSet PUnit I)
    (_hbase : D.base.Finite) (_hemb : D.IsHyperbolicallyEmbedded) (g : PUnit)
    (_hhyper : IsHyperbolicElement D.fam g)
    (hord : ∀ n : ℕ, 0 < n → g ^ n ≠ 1) (N : ℕ)
    (p : RelativeWordPattern PUnit I) (T : Set ℕ) (_hT : T.Infinite)
    (_hpattern : ∀ q : ℕ, q ∈ T → ∃ w : List (RelLetter PUnit I),
      (∀ a ∈ w, D.IsLetter a) ∧ w.length ≤ N ∧
        relativeWordPattern w = p ∧ RelLetter.listVal w = g ^ q) :
    ∃ T' : Set ℕ, T' ⊆ T ∧ T'.Infinite ∧
      ∃ (lam : I) (n : ℕ) (k h : PUnit),
        ∀ q : ℕ, q ∈ T' →
          ∃ z : PUnit, z ∈ D.relBall lam n ∧ g ^ q = k * h * z := by
  exfalso
  exact hord 1 (by omega) (Subsingleton.elim _ _)

end RelHyp
end GGT
end GroupApproximation
