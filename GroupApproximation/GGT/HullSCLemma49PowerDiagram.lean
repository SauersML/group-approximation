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
open GroupApproximation.WordMetric

universe u w

/-! ## Shortest representatives of quotient conjugacy classes -/

/-- `h` represents a conjugate of `g` modulo the normal subgroup `N`.

The explicit formula is the lift-level version of conjugacy in `G ⧸ N` and
is the form used in Hull's proof when a shortest word representing a conjugate
of the quotient element is selected. -/
def ConjugateModulo {G : Type u} [Group G]
    (N : Subgroup G) (g h : G) : Prop :=
  ∃ a k : G, k ∈ N ∧ h = a * g * a⁻¹ * k

namespace ConjugateModulo

theorem refl {G : Type u} [Group G] (N : Subgroup G) (g : G) :
    ConjugateModulo N g g := by
  exact ⟨1, 1, N.one_mem, by simp⟩

theorem trans {G : Type u} [Group G] {N : Subgroup G} [N.Normal]
    {g h z : G} (hgh : ConjugateModulo N g h)
    (hhz : ConjugateModulo N h z) : ConjugateModulo N g z := by
  obtain ⟨a, k, hk, rfl⟩ := hgh
  obtain ⟨b, l, hl, rfl⟩ := hhz
  refine ⟨b * a, b * k * b⁻¹ * l, ?_, ?_⟩
  · exact N.mul_mem ((inferInstance : N.Normal).conj_mem k hk b) hl
  · group

/-- Membership of a positive power in a normal subgroup is invariant under
changing the lift inside a quotient conjugacy class. -/
theorem pow_mem {G : Type u} [Group G] {N : Subgroup G} [N.Normal]
    {g h : G} {n : ℕ} (hgh : ConjugateModulo N g h)
    (hg : g ^ n ∈ N) : h ^ n ∈ N := by
  obtain ⟨a, k, hk, rfl⟩ := hgh
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  have hkker : k ∈ q.ker := by
    rwa [QuotientGroup.ker_mk']
  have hkq : q k = 1 := MonoidHom.mem_ker.mp hkker
  have hgker : g ^ n ∈ q.ker := by
    rwa [QuotientGroup.ker_mk']
  have hgq : q (g ^ n) = 1 := MonoidHom.mem_ker.mp hgker
  rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker]
  simp only [map_pow, map_mul, map_inv]
  rw [hkq, mul_one]
  rw [conj_pow, ← map_pow, hgq, mul_one, mul_inv_cancel]

/-- A power correction for one lift transports back across quotient
conjugacy.  This is the exact algebraic step used after Hull chooses a shortest
representative of the quotient conjugacy class. -/
theorem correction {G : Type u} [Group G] {N : Subgroup G} [N.Normal]
    {g h : G} {n : ℕ} (hgh : ConjugateModulo N g h)
    (hcorr : ∃ k ∈ N, (h * k) ^ n = 1) :
    ∃ k ∈ N, (g * k) ^ n = 1 := by
  obtain ⟨a, k₀, hk₀, rfl⟩ := hgh
  obtain ⟨k₁, hk₁, hpow⟩ := hcorr
  let k : G := a⁻¹ * (k₀ * k₁) * a
  have hk : k ∈ N := by
    dsimp [k]
    simpa only [inv_inv] using
      (inferInstance : N.Normal).conj_mem (k₀ * k₁) (N.mul_mem hk₀ hk₁) a⁻¹
  refine ⟨k, hk, ?_⟩
  have heq : g * k = a⁻¹ * ((a * g * a⁻¹ * k₀) * k₁) * a := by
    dsimp [k]
    group
  rw [heq]
  have hconjpow :
      (a⁻¹ * ((a * g * a⁻¹ * k₀) * k₁) * a) ^ n =
        a⁻¹ * ((a * g * a⁻¹ * k₀) * k₁) ^ n * a := by
    clear hpow
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, pow_succ, ih]
        group
  rw [hconjpow, hpow, mul_one, inv_mul_cancel]

end ConjugateModulo

/-- `g` has least word length among all lifts of its quotient conjugacy
class. -/
def IsShortestModuloConjugacy {G : Type u} [Group G]
    (A : Set G) (N : Subgroup G) (g : G) : Prop :=
  ∀ h : G, ConjugateModulo N g h → wordNorm A g ≤ wordNorm A h

/-- Every quotient conjugacy class has a shortest lift, by well-ordering of
the natural-valued word length. -/
theorem exists_shortest_conjugateModulo {G : Type u} [Group G]
    (A : Set G) (N : Subgroup G) [N.Normal] (g : G) :
    ∃ h : G, ConjugateModulo N g h ∧ IsShortestModuloConjugacy A N h := by
  classical
  let P : ℕ → Prop := fun m ↦
    ∃ h : G, ConjugateModulo N g h ∧ wordNorm A h = m
  have hex : ∃ m, P m :=
    ⟨wordNorm A g, g, ConjugateModulo.refl N g, rfl⟩
  obtain ⟨h, hgh, hlength⟩ := Nat.find_spec hex
  refine ⟨h, hgh, ?_⟩
  intro y hhy
  have hgy : ConjugateModulo N g y := hgh.trans hhy
  have hy : P (wordNorm A y) := ⟨y, hgy, rfl⟩
  rw [hlength]
  exact Nat.find_min' hex hy

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

/-- The remaining geometric statement of Hull's Lemma 4.9, after quotient
conjugacy minimization, order, normal-closure, least-area, and reducedness
bookkeeping have been removed.  The diagram argument is required only for a
shortest lift of its quotient conjugacy class, exactly as in Hull's proof. -/
def HullLemma49ShortestReducedDiagramStatement : Prop :=
  ∀ {G : Type u} [Group G] {Λ : Type w} (D : GGT.RelGenSet G Λ),
    D.IsHyperbolicallyEmbedded →
      ∃ (eps rho : ℕ) (mu : ℝ), 0 < mu ∧
        ∀ (W : Set (List (GGT.RelLetter G Λ)))
          (v : List (GGT.RelLetter G Λ)), v ∈ W →
          RelWord.IsLemma49Input D W eps mu rho →
            ∀ (g : G) (n : ℕ),
              IsShortestModuloConjugacy D.alphabet.carrier
                (Subgroup.normalClosure
                  ({GGT.RelLetter.listVal v} : Set G)) g →
              Lemma49ReducedPowerDiagram
                ({GGT.RelLetter.listVal v} : Set G) g n →
                ∃ k ∈ Subgroup.normalClosure
                    ({GGT.RelLetter.listVal v} : Set G),
                  (g * k) ^ n = 1

/-- The reduced-diagram statement implies the exact quotient-free
kernel-power statement consumed by the canonical Hull filling. -/
theorem hullLemma49KernelPowerStatement_of_reducedDiagram
    (hdiagram : HullLemma49ShortestReducedDiagramStatement.{u, w}) :
    HullLemma49KernelPowerStatement.{u, w} := by
  intro G _ Λ D hemb
  obtain ⟨eps, rho, mu, hmu, hgood⟩ := hdiagram D hemb
  refine ⟨eps, rho, mu, hmu, ?_⟩
  intro W v hv hinput g n hn hpow
  let N : Subgroup G :=
    Subgroup.normalClosure ({GGT.RelLetter.listVal v} : Set G)
  obtain ⟨h, hgh, hshort⟩ :=
    exists_shortest_conjugateModulo D.alphabet.carrier N g
  have hhpow : h ^ n ∈ N := hgh.pow_mem hpow
  have hcorr : ∃ k ∈ N, (h * k) ^ n = 1 := by
    by_cases htrivial : h ^ n = 1
    · exact ⟨1, N.one_mem, by simpa using htrivial⟩
    · obtain ⟨P⟩ := exists_lemma49ReducedPowerDiagram hn hhpow htrivial
      exact hgood W v hv hinput h n hshort P
  exact hgh.correction hcorr

end HullSC
end GroupApproximation
