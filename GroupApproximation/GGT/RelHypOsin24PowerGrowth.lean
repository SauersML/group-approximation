import GroupApproximation.GGT.RelHypOsin24ClassificationBridge

/-!
# The source-facing cyclic power-growth interface

Osin's Memoirs Theorem 1.10 (`label{10}` in the fetched `math0404040.tex`)
states that a hyperbolic element of infinite order has constants
`lambda > 0` and `c >= 0` with

    `d_hat(1,g^n) > lambda * n - c`.

The proof in Chapter 4.3 runs through `cyc1` (strong relative
quasi-convexity of the centralizer), `qc1` and `qc-hyp` (finite generation and
hyperbolicity), and `trd00`/`trd` (positive relative translation number).  This
module records exactly the output of that source chain and proves the purely
formal consequences already supported by the repository.  The geometric
production of the constants is intentionally a named Prop: no local
finiteness argument alone supplies it, as the infinite-peripheral case is the
content of Osin's theorem.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v

/-! ## The exact source output -/

/-- **Osin's cyclic power-growth output.**  This is the strict inequality in
Memoirs Theorem 1.10, specialized to a finite labelled relative family. -/
def FiniteFamilyRelativePowerLinearGrowthStatement : Prop :=
  ∀ (G : Type u) (_ : Group G) (I : Type v) [Finite I]
    (D : RelGenSet G I),
    D.base.Finite → D.IsHyperbolicallyEmbedded → ∀ g : G,
      IsHyperbolicElement D.fam g →
        (∀ n : ℕ, 0 < n → g ^ n ≠ 1) →
          ∃ l B : ℝ, 0 < l ∧ 0 ≤ B ∧
            ∀ n : ℕ,
              l * (n : ℝ) - B <
                dist (Cayley.base D.alphabet)
                  ((g ^ n) • Cayley.base D.alphabet)

/-- The source-growth output immediately gives the finite-family escape target.
The proof is only the Archimedean/filter step; all relative geometry is
contained in `hGrowth`. -/
theorem finiteFamilyRelativePowerEscape_of_linearGrowth
    (hGrowth : FiniteFamilyRelativePowerLinearGrowthStatement.{u, v}) :
    FiniteFamilyRelativePowerEscapeStatement.{u, v} := by
  intro G instG I _ D hbase hemb g hhyper hord
  letI : Group G := instG
  obtain ⟨l, B, hl, hB, hlin⟩ :=
    hGrowth G instG I D hbase hemb g hhyper hord
  exact isEscaping_of_strict_linear_lower_bound hl hB hlin

/-- The exact source inequality is also enough for the acylindrical action
classification, once the relative alphabet is known to be acylindrical. -/
theorem hyperbolicElementLoxodromicAcylindrical_of_linearGrowth
    (hGrowth : FiniteFamilyRelativePowerLinearGrowthStatement.{u, v})
    {G : Type u} [Group G] {I : Type v} [Finite I]
    (D : RelGenSet G I) (hbase : D.base.Finite)
    (hemb : D.IsHyperbolicallyEmbedded)
    (hacy : IsAcylindrical G (Cayley D.alphabet)) {g : G}
    (hhyper : IsHyperbolicElement D.fam g)
    (hord : ∀ n : ℕ, 0 < n → g ^ n ≠ 1) :
    IsLoxodromic g (Cayley.base D.alphabet) := by
  have hesc : IsEscaping g (Cayley.base D.alphabet) := by
    apply finiteFamilyRelativePowerEscape_of_linearGrowth hGrowth
      G inferInstance I D hbase hemb g hhyper hord
  exact isLoxodromic_of_relativePowerEscape_of_acylindrical D hemb hacy hesc

/-! ## The ordinary hyperbolic model -/

/-- In the empty-family model, finite-base properness gives loxodromy and the
existing loxodromic axis estimate supplies Osin's strict linear inequality. -/
theorem finiteFamilyRelativePowerLinearGrowth_emptyModel
    {G : Type u} [Group G] {I : Type v} [IsEmpty I]
    (D : RelGenSet G I) (hbase : D.base.Finite)
    (hemb : D.IsHyperbolicallyEmbedded) (g : G)
    (hord : ∀ n : ℕ, 0 < n → g ^ n ≠ 1) :
    ∃ l B : ℝ, 0 < l ∧ 0 ≤ B ∧
      ∀ n : ℕ,
        l * (n : ℝ) - B <
          dist (Cayley.base D.alphabet)
            ((g ^ n) • Cayley.base D.alphabet) := by
  have hlox : IsLoxodromic g (Cayley.base D.alphabet) :=
    relHypHyperbolicElementLoxodromic_empty D hbase hemb g hord
  exact strictLinearLowerBound_of_isLoxodromic hlox

/-- Model test for the named source Prop: on an ordinary finite Cayley graph,
every infinite-order element has the required strict linear power bound. -/
theorem finiteFamilyRelativePowerLinearGrowth_standardModel
    {G : Type u} [Group G] {I : Type v} [IsEmpty I]
    (D : RelGenSet G I) (hbase : D.base.Finite)
    (hemb : D.IsHyperbolicallyEmbedded) (g : G)
    (_hhyper : IsHyperbolicElement D.fam g)
    (hord : ∀ n : ℕ, 0 < n → g ^ n ≠ 1) :
    ∃ l B : ℝ, 0 < l ∧ 0 ≤ B ∧
      ∀ n : ℕ,
        l * (n : ℝ) - B <
          dist (Cayley.base D.alphabet)
            ((g ^ n) • Cayley.base D.alphabet) :=
  finiteFamilyRelativePowerLinearGrowth_emptyModel D hbase hemb g hord

end RelHyp
end GGT
end GroupApproximation
