import GroupApproximation.Algebra.HyperbolicGroup
import GroupApproximation.Algebra.WordMetricComparison

/-!
# Quasi-isometry, and what generating-set independence reduces to

The one open statement named here is a `Prop`-valued definition, not a theorem,
and nothing in this repository is conditional on it.

`Algebra/HyperbolicGroup.lean` defines hyperbolicity against *some* finite
symmetric generating set.  The theorem that makes that definition respectable is
that the choice does not matter, and the standard proof factors through two
steps:

1. changing the generating set is a quasi-isometry;
2. hyperbolicity is a quasi-isometry invariant of geodesic spaces --- the Morse
   lemma, i.e. stability of quasi-geodesics.

**Step 1 is proved here** (`isQuasiIsometry_id_of_generating_sets`, off the
bi-Lipschitz comparison of `Algebra/WordMetricComparison.lean`), and step 2 is
`QuasiIsometryInvariant`, stated and not proved.
`independentOfGeneratingSet_of_quasiIsometryInvariant` is the reduction: the
open statement about generating sets follows from the open statement about
quasi-isometries, so there is exactly one missing input rather than two.

`Algebra/MorseLemma.lean` says how much of step 2 is elementary: hyperbolicity
*is* transported, unconditionally, by a quasi-isometry with multiplicative
constant `1` (`isFourPointHyperbolic_of_roughIsometry`), and the general case
fails arithmetically with a defect of exactly `K²`
(`fourPoint_transport_of_biLipschitz`).  It also states the Morse lemma itself.
`Algebra/FiniteIndexQuasiIsometry.lean` supplies the other quasi-isometry this
development needs: a finite-index subgroup, with its Schreier metric, is
quasi-isometric to the ambient group.
-/

namespace GroupApproximation
namespace Hyperbolic

open WordMetric

universe u v

/-- A **quasi-isometric embedding** of one word metric in another: distances are
preserved up to the multiplicative constant `K` and the additive constant `C`,
in both directions. -/
def IsQuasiIsometricEmbedding {G : Type u} {H : Type v} [Group G] [Group H]
    (S : Set G) (T : Set H) (f : G → H) (K C : ℕ) : Prop :=
  ∀ x y : G,
    wordDist T (f x) (f y) ≤ K * wordDist S x y + C ∧
      wordDist S x y ≤ K * wordDist T (f x) (f y) + C

/-- A **quasi-isometry**: a quasi-isometric embedding whose image is
`C`-coarsely everything. -/
def IsQuasiIsometry {G : Type u} {H : Type v} [Group G] [Group H]
    (S : Set G) (T : Set H) (f : G → H) (K C : ℕ) : Prop :=
  IsQuasiIsometricEmbedding S T f K C ∧ ∀ y : H, ∃ x : G, wordDist T (f x) y ≤ C

/-- **Changing the finite generating set is a quasi-isometry**, on the nose:
the identity map, with the bi-Lipschitz constant and no additive error. -/
theorem isQuasiIsometry_id_of_generating_sets {G : Type u} [Group G] (S T : Finset G)
    (hS : IsSymmetricGeneratingSet (S : Set G))
    (hT : IsSymmetricGeneratingSet (T : Set G)) :
    ∃ K : ℕ, IsQuasiIsometry (S : Set G) (T : Set G) id K 0 := by
  obtain ⟨C, _, hC⟩ := exists_bilipschitz S T hS hT
  refine ⟨C, ?_, fun y => ⟨y, ?_⟩⟩
  · intro x y
    obtain ⟨h₁, h₂⟩ := hC x y
    simp only [id_eq, add_zero]
    exact ⟨h₁, h₂⟩
  · simp [wordDist_self]

/-- **Open.**  Hyperbolicity is a quasi-isometry invariant.  For geodesic spaces
this is the classical consequence of the Morse lemma --- stability of
quasi-geodesics --- and it is the single input the theorem below is missing.
Not proved here, and nothing in this repository assumes it. -/
def QuasiIsometryInvariant : Prop :=
  ∀ (G H : Type) (_ : Group G) (_ : Group H) (S : Set G) (T : Set H) (f : G → H) (K C : ℕ),
    IsSymmetricGeneratingSet S → IsSymmetricGeneratingSet T →
    IsQuasiIsometry S T f K C → (∃ δ : ℕ, IsFourPointHyperbolic S δ) →
      ∃ δ : ℕ, IsFourPointHyperbolic T δ

/-- **Open.**  Hyperbolicity does not depend on the finite generating set. -/
def IndependentOfGeneratingSet : Prop :=
  ∀ (G : Type) (_ : Group G) (S T : Finset G),
    IsSymmetricGeneratingSet (S : Set G) → IsSymmetricGeneratingSet (T : Set G) →
    (∃ δ : ℕ, IsFourPointHyperbolic (S : Set G) δ) →
      ∃ δ : ℕ, IsFourPointHyperbolic (T : Set G) δ

/-- **The reduction.**  Independence of the generating set follows from
quasi-isometry invariance, because changing the generating set is a
quasi-isometry.  So the two open statements above are one open statement: the
Morse lemma. -/
theorem independentOfGeneratingSet_of_quasiIsometryInvariant
    (h : QuasiIsometryInvariant) : IndependentOfGeneratingSet := by
  intro G hG S T hS hT hhyp
  obtain ⟨K, hqi⟩ := isQuasiIsometry_id_of_generating_sets S T hS hT
  exact h G G hG hG (S : Set G) (T : Set G) id K 0 hS hT hqi hhyp

end Hyperbolic
end GroupApproximation
