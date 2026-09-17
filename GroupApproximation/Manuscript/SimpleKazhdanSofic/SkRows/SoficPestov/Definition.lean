import GroupApproximation.Sofic.Sofic
import GroupApproximation.Sofic.RegularActionSofic
import GroupApproximation.Meta.AxiomGuard

/-!
# Pestov's printed normalization of soficity

tex l.105–109: "Sofic and hyperlinear groups are defined by approximately multiplicative maps into
finite symmetric groups with the normalized Hamming distance, [...] that keep nontrivial elements
uniformly far from~$1$~\cite{Pestov}."

tex l.345–346: "It is LEF, so it is sofic~\cite[Example~4.5]{Pestov} [...]"

This module fixes the printed normalization: maps `φ : G → Sym(Fin n)`, the normalized Hamming
distance `d(σ, τ) = #{i | σ i ≠ τ i} / n` (the fraction of points where the permutations
disagree), `φ 1 = 1`, defect `< ε`, and nontrivial elements at distance `> 1 - ε` from `1`.

* `pestovHammingDist`: the normalized Hamming distance on `Equiv.Perm (Fin n)`.
* `pestovHammingDist_eq_hammingDistance`: it is the corpus `hammingDistance` on `finModel n`
  (`Sofic/Sofic.lean`, `Sofic/RegularActionSofic.lean`), i.e. the corpus normalization is also
  the fraction of disagreement points.
* The metric lemmas (symmetry, triangle, bi-invariance) restated on `Fin n`, so later proofs can
  argue with a single syntactic form of the distance.
* `IsSoficPestov` (multiplicativity on all pairs of the test set) and `IsSoficPestovRestricted`
  (only when `g, h, gh` lie in the test set, Pestov's printed convention).
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace SkRows
namespace SoficPestov

/-- The normalized Hamming distance on `Sym(n)`: the fraction of points on which two
permutations disagree. -/
noncomputable def pestovHammingDist {n : ℕ} (σ τ : Equiv.Perm (Fin n)) : ℝ :=
  ((Finset.univ.filter fun i => σ i ≠ τ i).card : ℝ) / n

/-- The printed normalization agrees with the corpus distance on the finite model `Fin n`. -/
theorem pestovHammingDist_eq_hammingDistance {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    pestovHammingDist σ τ = hammingDistance (finModel n) σ τ := by
  rw [hammingDistance_eq, card_finModel]
  rfl

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SoficPestov.pestovHammingDist_eq_hammingDistance

theorem pestovHammingDist_self {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    pestovHammingDist σ σ = 0 := by
  simp only [pestovHammingDist_eq_hammingDistance]
  exact hammingDistance_self (finModel n) σ

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SoficPestov.pestovHammingDist_self

theorem pestovHammingDist_comm {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    pestovHammingDist σ τ = pestovHammingDist τ σ := by
  simp only [pestovHammingDist_eq_hammingDistance]
  exact hammingDistance_comm (finModel n) σ τ

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SoficPestov.pestovHammingDist_comm

theorem pestovHammingDist_triangle {n : ℕ} (σ τ ρ : Equiv.Perm (Fin n)) :
    pestovHammingDist σ ρ ≤ pestovHammingDist σ τ + pestovHammingDist τ ρ := by
  simp only [pestovHammingDist_eq_hammingDistance]
  exact hammingDistance_triangle (finModel n) σ τ ρ

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SoficPestov.pestovHammingDist_triangle

theorem pestovHammingDist_left_invariant {n : ℕ} (s σ τ : Equiv.Perm (Fin n)) :
    pestovHammingDist (s * σ) (s * τ) = pestovHammingDist σ τ := by
  simp only [pestovHammingDist_eq_hammingDistance]
  exact hammingDistance_left_invariant (finModel n) s σ τ

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SoficPestov.pestovHammingDist_left_invariant

theorem pestovHammingDist_right_invariant {n : ℕ} (σ τ s : Equiv.Perm (Fin n)) :
    pestovHammingDist (σ * s) (τ * s) = pestovHammingDist σ τ := by
  simp only [pestovHammingDist_eq_hammingDistance]
  exact hammingDistance_right_invariant (finModel n) σ τ s

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SoficPestov.pestovHammingDist_right_invariant

/-- **Soficity in Pestov's printed normalization.**  For every finite `F ⊆ G` and `ε > 0` there is
a map `φ : G → Sym(n)` with `φ 1 = 1`, Hamming defect `< ε` on all pairs of `F`, and every
nontrivial element of `F` sent to distance `> 1 - ε` from the identity. -/
def IsSoficPestov (G : Type*) [Group G] : Prop :=
  ∀ (F : Finset G) (ε : ℝ), 0 < ε →
    ∃ (n : ℕ) (φ : G → Equiv.Perm (Fin n)),
      (∀ g ∈ F, ∀ h ∈ F, pestovHammingDist (φ (g * h)) (φ g * φ h) < ε) ∧
      φ 1 = 1 ∧
      ∀ g ∈ F, g ≠ 1 → 1 - ε < pestovHammingDist (φ g) 1

/-- The same notion with multiplicativity only tested when `g, h, gh ∈ F` (Pestov's
`(F, ε)`-almost homomorphisms). -/
def IsSoficPestovRestricted (G : Type*) [Group G] : Prop :=
  ∀ (F : Finset G) (ε : ℝ), 0 < ε →
    ∃ (n : ℕ) (φ : G → Equiv.Perm (Fin n)),
      (∀ g ∈ F, ∀ h ∈ F, g * h ∈ F → pestovHammingDist (φ (g * h)) (φ g * φ h) < ε) ∧
      φ 1 = 1 ∧
      ∀ g ∈ F, g ≠ 1 → 1 - ε < pestovHammingDist (φ g) 1

/-- Testing all pairs is at least as strong as testing the product-closed pairs. -/
theorem isSoficPestovRestricted_of_isSoficPestov {G : Type*} [Group G]
    (h : IsSoficPestov G) : IsSoficPestovRestricted G := by
  intro F ε hε
  obtain ⟨n, φ, hmul, hφ1, hsep⟩ := h F ε hε
  exact ⟨n, φ, fun g hg k hk _ => hmul g hg k hk, hφ1, hsep⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SoficPestov.isSoficPestovRestricted_of_isSoficPestov

end SoficPestov
end SkRows
end SimpleKazhdanSofic
end GroupApproximation
