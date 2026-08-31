import GroupApproximation.GGT.HullSCPublishedSmallCancellation
import GroupApproximation.GGT.HullSCRelatorSeparation2Quotient

/-!
# Hull's pair construction with the published `C₁` hypotheses

The older pair interface asked Hull's quotient and no-new-torsion conclusions
from `RelWord.IsSmallCancellation`.  That predicate omits three hypotheses used
in the published proof: quasi-geodesicity, strong boundedness, and the
prime-piece estimate.  The last is exactly the extra `C₁` hypothesis of Hull's
Lemma 4.9.

This file retains the historical Bool-pair one-step interface.  Its quotient
half consumes `RelWord.IsLemma49Input`, which extends the Lemma 4.4 input and
hence the ordinary small-cancellation predicate.  The source-faithful natural
quotient over the complete selected auxiliary family is instead assembled in
`HullSCCanonicalQuotientPublished`; no cone-off or rotating-family conclusion
is attributed to Lemmas 4.4 and 4.9 there.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

/-- Hull's §6 relator, at the one-letter base part, carrying every hypothesis
used by Lemmas 4.4 and 4.9 rather than only their small-cancellation subset. -/
def HullRelatorStatement₂OfBaseLetterPublished : Prop :=
  ∀ {G : Type u} [Group G] (A : HullGeneratingSet G) (N : Subgroup G)
    (E : HypEmbeddedCore₂ A N), Suitable A.alphabet N → ∀ (t : G),
      t⁻¹ ∈ E.rel.base → ∀ (eps rho : ℕ) (mu : ℝ), 0 < mu →
        ∃ u ∈ N, ∃ W : Set (List (GGT.RelLetter G Bool)),
          (∃ v ∈ W, GGT.RelLetter.listVal v = t⁻¹ * u) ∧
            RelWord.IsLemma49Input E.rel W eps mu rho

/-- The quotient half of Hull's Theorem 5.1 with the published `C₁` input.

The output is unchanged.  Only the premise is repaired: finite-order lifting
is a Lemma 4.9 conclusion and therefore requires the prime-piece clause. -/
def HullQuotientStatement₂Published : Prop :=
  ∀ {G : Type u} [Group G] (A : HullGeneratingSet G) (N : Subgroup G)
    (E : HypEmbeddedCore₂ A N), Suitable A.alphabet N →
      ∀ {k : ℕ} (S : Fin k → Subgroup G),
        (∀ j : Fin k, Suitable A.alphabet (S j)) → ∀ R : ℕ,
          ∃ (eps rho : ℕ) (mu : ℝ), 0 < mu ∧
            ∀ (W : Set (List (GGT.RelLetter G Bool)))
              (v : List (GGT.RelLetter G Bool)), v ∈ W →
              RelWord.IsLemma49Input E.rel W eps mu rho →
                Nonempty (HullFillingQuotient A N S
                  (GGT.RelLetter.listVal v) R)

/-- Hull's one-step theorem from the two source-faithful halves.

The relator and quotient halves are instantiated at the same `t`-enlarged
core and exchange `IsLemma49Input` without projection to the weaker predicate. -/
theorem hullOneStep_of_published₂
    (hEmb : ExistsHypEmbeddedConeOff₂.{u})
    (hrelator : HullRelatorStatement₂OfBaseLetterPublished.{u})
    (hquot : HullQuotientStatement₂Published.{u}) :
    HullOneStepStatement.{u} := by
  intro G _ A N hN k S hS t R
  obtain ⟨E⟩ := nonempty_hypEmbeddedCore₂_of_coneOff hEmb A hN
  let E' : HypEmbeddedCore₂ A N := E.adjoinPair t
  have ht : t⁻¹ ∈ E'.rel.base := mem_base_adjoinPair E t
  obtain ⟨eps, rho, mu, hmu, hgood⟩ := hquot A N E' hN S hS R
  obtain ⟨u, huN, W, ⟨v, hvW, hvval⟩, hsc⟩ :=
    hrelator A N E' hN t ht eps rho mu hmu
  have hq := hgood W v hvW hsc
  rw [hvval] at hq
  obtain ⟨D⟩ := hq
  have hrel : D.q (t⁻¹ * u) = 1 := by
    rw [← MonoidHom.mem_ker, D.ker_eq]
    exact Subgroup.subset_normalClosure rfl
  have hqt : D.q t = D.q u := by
    rw [map_mul, map_inv] at hrel
    exact inv_mul_eq_one.mp hrel
  refine ⟨{ step := D.toHullStep
            mem_map := ?_
            kerNormallyGenerated := ⟨{t⁻¹ * u}, by simp, ?_⟩ }⟩
  · intro _
    show D.q t ∈ N.map D.q
    rw [hqt]
    exact Subgroup.mem_map_of_mem _ huN
  · show D.q.ker = Subgroup.normalClosure ((({t⁻¹ * u} : Finset G)) : Set G)
    rw [D.ker_eq, Finset.coe_singleton]

end HullSC
end GroupApproximation
