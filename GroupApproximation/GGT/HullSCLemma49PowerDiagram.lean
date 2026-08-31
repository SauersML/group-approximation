import GroupApproximation.GGT.HullSCCanonicalQuotientPublished
import GroupApproximation.GroupTheory.NormalClosureReducedProduct

/-!
# The exact reduced power diagram behind Hull's Lemma 4.9

The kernel-power conclusion of Hull's Lemma 4.9 has one elementary branch:
if the chosen power is already trivial, the correction is the identity.  In
the remaining branch, membership in the one-relator normal closure supplies a
least-area product of signed conjugates of that relator.  Flattening this
product produces the reduced power diagram formalized here.

The final geometric content of Lemma 4.9 is isolated as
`HullLemma49ReducedDiagramStatement`: under the published `C₁` hypotheses,
every such reduced power diagram admits the required kernel correction.  The
last theorem proves that this exact diagram statement implies the manuscript's
quotient-free `HullLemma49KernelPowerStatement`.
-/

namespace GroupApproximation
namespace HullSC

open RelatorDefectBudget

universe u w

/-- A least-area algebraic van Kampen diagram whose boundary is the positive
power `g ^ n`.  Reducedness says that no nonempty consecutive block of cells
has trivial product. -/
structure Lemma49ReducedPowerDiagram {G : Type u} [Group G]
    (R : Set G) (g : G) (n : ℕ) where
  exponent_pos : 0 < n
  power_ne_one : g ^ n ≠ 1
  area : ℕ
  area_pos : 0 < area
  factors : List G
  factors_length : factors.length = area
  factors_prod : factors.prod = g ^ n
  factors_cells : ∀ x ∈ factors, IsSignedConjugate R x
  reduced : ∀ (pre mid suf : List G),
    factors = pre ++ mid ++ suf → mid ≠ [] → mid.prod ≠ 1

/-- A nontrivial power in a normal closure has a least-area reduced power
diagram, with no geometric or literature input. -/
theorem exists_lemma49ReducedPowerDiagram
    {G : Type u} [Group G] {R : Set G} {g : G} {n : ℕ}
    (hn : 0 < n) (hpow : g ^ n ∈ Subgroup.normalClosure R)
    (hne : g ^ n ≠ 1) :
    Nonempty (Lemma49ReducedPowerDiagram R g n) := by
  classical
  have hex : ∃ area : ℕ, IsRelatorProduct R area (g ^ n) :=
    exists_isRelatorProduct hpow
  let area : ℕ := Nat.find hex
  have hcertificate : IsRelatorProduct R area (g ^ n) := Nat.find_spec hex
  obtain ⟨factors, hlength, hprod, hcells⟩ := hcertificate.exists_flatten
  have harea_pos : 0 < area := by
    by_contra hnot
    have hzero : area = 0 := Nat.eq_zero_of_not_pos hnot
    have hcertificate0 : IsRelatorProduct R 0 (g ^ n) := by
      simpa only [hzero] using hcertificate
    exact hne hcertificate0.eq_one_of_index_zero
  have hminimal : ∀ {m : ℕ}, IsRelatorProduct R m (g ^ n) → area ≤ m := by
    intro m hm
    exact Nat.find_min' hex hm
  refine ⟨{
    exponent_pos := hn
    power_ne_one := hne
    area := area
    area_pos := harea_pos
    factors := factors
    factors_length := hlength
    factors_prod := hprod
    factors_cells := hcells
    reduced := ?_ }⟩
  exact no_trivial_subproduct_of_minimal hlength hprod hcells hminimal

/-- The remaining geometric statement of Hull's Lemma 4.9, after the quotient,
order, normal-closure, least-area, and reducedness bookkeeping has been
removed. -/
def HullLemma49ReducedDiagramStatement : Prop :=
  ∀ {G : Type u} [Group G] {Λ : Type w} (D : GGT.RelGenSet G Λ),
    D.IsHyperbolicallyEmbedded →
      ∃ (eps rho : ℕ) (mu : ℝ), 0 < mu ∧
        ∀ (W : Set (List (GGT.RelLetter G Λ)))
          (v : List (GGT.RelLetter G Λ)), v ∈ W →
          RelWord.IsLemma49Input D W eps mu rho →
            ∀ (g : G) (n : ℕ),
              Lemma49ReducedPowerDiagram
                ({GGT.RelLetter.listVal v} : Set G) g n →
                ∃ k ∈ Subgroup.normalClosure
                    ({GGT.RelLetter.listVal v} : Set G),
                  (g * k) ^ n = 1

/-- The reduced-diagram statement implies the exact quotient-free
kernel-power statement consumed by the canonical Hull filling. -/
theorem hullLemma49KernelPowerStatement_of_reducedDiagram
    (hdiagram : HullLemma49ReducedDiagramStatement.{u, w}) :
    HullLemma49KernelPowerStatement.{u, w} := by
  intro G _ Λ D hemb
  obtain ⟨eps, rho, mu, hmu, hgood⟩ := hdiagram D hemb
  refine ⟨eps, rho, mu, hmu, ?_⟩
  intro W v hv hinput g n hn hpow
  by_cases htrivial : g ^ n = 1
  · refine ⟨1, Subgroup.one_mem _, ?_⟩
    simpa using htrivial
  · obtain ⟨P⟩ := exists_lemma49ReducedPowerDiagram hn hpow htrivial
    exact hgood W v hv hinput g n P

end HullSC
end GroupApproximation
