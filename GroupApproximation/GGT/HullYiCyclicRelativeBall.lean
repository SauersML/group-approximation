import GroupApproximation.GGT.ElementaryCoarseTranslationProperAction
import GroupApproximation.GGT.HullTheorem316RelativePolygon

/-!
# Relative-ball finiteness for Hull's cyclic `yi` family

For the cyclic peripherals selected by Hull's `yi`, properness of the
peripheral action is not a literature input: it follows immediately from
loxodromy.  The only remaining content of local finiteness is therefore the
prescribed-base relative-distance lower bound, inequality (41) in
Dahmani--Guirardel--Osin's Theorem 4.42.

This module proves that reduction for an arbitrary indexed family and composes
it with `HullYiCyclicPairGeometry`.  No projection-complex statement is assumed
or renamed: the last theorem accepts the lower bound itself, exactly in the
form in which it is used.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.GGT
open GroupApproximation.GGT.Elementary
open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v w

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X]
  [MulAction G X]

/-- A loxodromic cyclic subgroup acts properly at the loxodromy basepoint. -/
theorem actsProperlyAt_zpowers_of_isLoxodromic
    (hiso : IsIsometricAction G X) {g : G} {x : X}
    (hlox : IsLoxodromic g x) : ActsProperlyAt (Subgroup.zpowers g) x := by
  intro eps
  refine Set.Finite.subset
    ((finite_zpow_displacement hiso hlox eps).image (fun k : ℤ => g ^ k)) ?_
  rintro h ⟨hhpow, hhdisp⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hhpow
  exact ⟨k, hhdisp, rfl⟩

/-- A per-radius orbit-displacement bound and properness are exactly enough for
relative-ball finiteness.  No linear dependence on the radius is needed. -/
theorem locallyFinite_family_of_orbitBound_of_actsProperly
    {Λ : Type w} {D : RelGenSet G Λ} {s : X}
    (hproper : ∀ lam : Λ, ActsProperlyAt (D.fam lam) s)
    (hbound : ∀ (lam : Λ) (n : ℕ), ∃ R : ℝ,
      ∀ h : G, h ∈ D.relBall lam n → dist s (h • s) ≤ R) :
    ∀ (lam : Λ) (n : ℕ), (D.relBall lam n).Finite := by
  intro lam n
  obtain ⟨R, hR⟩ := hbound lam n
  refine Set.Finite.subset (hproper lam R) ?_
  intro h hh
  exact ⟨(RelGenSet.mem_relBall.mp hh).1, hR h hh⟩

/-- Inequality (41) supplies the weaker per-radius displacement bound. -/
theorem orbitBound_family_of_orbitLowerBound
    {Λ : Type w} {D : RelGenSet G Λ} {s : X}
    (hlow : ∀ lam : Λ, ∃ alpha : ℝ, 0 < alpha ∧
      ∀ (n : ℕ) (h : G), h ∈ D.relBall lam n →
        alpha * dist s (h • s) ≤ (n : ℝ)) :
    ∀ (lam : Λ) (n : ℕ), ∃ R : ℝ,
      ∀ h : G, h ∈ D.relBall lam n → dist s (h • s) ≤ R := by
  intro lam n
  obtain ⟨alpha, halpha, hlower⟩ := hlow lam
  refine ⟨(n : ℝ) / alpha, ?_⟩
  intro h hh
  rw [le_div_iff₀ halpha]
  calc
    dist s (h • s) * alpha = alpha * dist s (h • s) := mul_comm _ _
    _ ≤ (n : ℝ) := hlower n h hh

/-- Inequality (41) and properness give relative-ball finiteness, independently
for every member of an indexed family. -/
theorem locallyFinite_family_of_orbitLowerBound_of_actsProperly
    {Λ : Type w} {D : RelGenSet G Λ} {s : X}
    (hproper : ∀ lam : Λ, ActsProperlyAt (D.fam lam) s)
    (hlow : ∀ lam : Λ, ∃ alpha : ℝ, 0 < alpha ∧
      ∀ (n : ℕ) (h : G), h ∈ D.relBall lam n →
        alpha * dist s (h • s) ≤ (n : ℝ)) :
    ∀ (lam : Λ) (n : ℕ), (D.relBall lam n).Finite := by
  exact locallyFinite_family_of_orbitBound_of_actsProperly hproper
    (orbitBound_family_of_orbitLowerBound hlow)

/-- For a loxodromic cyclic family, bounded displacement of each relative ball
already implies local finiteness. -/
theorem locallyFinite_zpowersFamily_of_orbitBound
    {Λ : Type w} (A : Alphabet G) (g : Λ → G)
    (hlox : ∀ lam : Λ, IsLoxodromic (g lam) (Cayley.base A))
    (hbound : ∀ (lam : Λ) (n : ℕ), ∃ R : ℝ,
      ∀ h : G,
        h ∈ (coneOffFamily A (fun nu => Subgroup.zpowers (g nu))).relBall lam n →
          dist (Cayley.base A) (h • Cayley.base A) ≤ R) :
    ∀ (lam : Λ) (n : ℕ),
      ((coneOffFamily A
        (fun nu => Subgroup.zpowers (g nu))).relBall lam n).Finite := by
  apply locallyFinite_family_of_orbitBound_of_actsProperly
    (D := coneOffFamily A (fun nu => Subgroup.zpowers (g nu)))
    (s := Cayley.base A)
  · intro lam
    rw [coneOffFamily_fam]
    exact actsProperlyAt_zpowers_of_isLoxodromic
      (isIsometricAction_cayley A) (hlox lam)
  · exact hbound

/-- For a loxodromic cyclic family, the prescribed cone-off has locally finite
relative metric as soon as its relative distance controls orbit displacement.

This is the exact cyclic-family form of the "in particular" clause of DGO
Theorem 4.42.  Properness is proved above, rather than carried as an input. -/
theorem locallyFinite_zpowersFamily_of_orbitLowerBound
    {Λ : Type w} (A : Alphabet G) (g : Λ → G)
    (hlox : ∀ lam : Λ, IsLoxodromic (g lam) (Cayley.base A))
    (hlow : ∀ lam : Λ, ∃ alpha : ℝ, 0 < alpha ∧
      ∀ (n : ℕ) (h : G),
        h ∈ (coneOffFamily A (fun nu => Subgroup.zpowers (g nu))).relBall lam n →
          alpha * dist (Cayley.base A) (h • Cayley.base A) ≤ (n : ℝ)) :
    ∀ (lam : Λ) (n : ℕ),
      ((coneOffFamily A
        (fun nu => Subgroup.zpowers (g nu))).relBall lam n).Finite := by
  exact locallyFinite_zpowersFamily_of_orbitBound A g hlox
    (orbitBound_family_of_orbitLowerBound hlow)

/-- Full hyperbolic embeddedness follows from the exact per-radius orbit bound;
this is the weakest residual interface needed by local finiteness. -/
theorem isHyperbolicallyEmbedded_zpowers_of_elementaryClosure_eq_of_orbitBound
    {Λ : Type w} [Fintype Λ] [Nonempty Λ]
    (A : HullGeneratingSet G) (g : Λ → G)
    (hncom : PairwiseNonCommensurable g)
    (hlox : ∀ lam : Λ, IsLoxodromic (g lam) (Cayley.base A.alphabet))
    (hcyc : ∀ lam : Λ,
      Elementary.elementaryClosure (g lam) = Subgroup.zpowers (g lam))
    (hbound : ∀ (lam : Λ) (n : ℕ), ∃ R : ℝ,
      ∀ h : G, h ∈
        (coneOffFamily A.alphabet
          (fun nu => Subgroup.zpowers (g nu))).relBall lam n →
        dist (Cayley.base A.alphabet) (h • Cayley.base A.alphabet) ≤ R) :
    (coneOffFamily A.alphabet
      (fun lam => Subgroup.zpowers (g lam))).IsHyperbolicallyEmbedded := by
  apply isHyperbolicallyEmbedded_zpowers_of_elementaryClosure_eq
    A g hncom hlox hcyc
  exact locallyFinite_zpowersFamily_of_orbitBound A.alphabet g hlox hbound

/-- The cyclic `yi` cone-off is hyperbolically embedded once the sole remaining
prescribed-base lower bound is supplied.  Hyperbolicity, geometric separation,
and peripheral properness are all theorems in the chain. -/
theorem isHyperbolicallyEmbedded_zpowers_of_elementaryClosure_eq_of_orbitLowerBound
    {Λ : Type w} [Fintype Λ] [Nonempty Λ]
    (A : HullGeneratingSet G) (g : Λ → G)
    (hncom : PairwiseNonCommensurable g)
    (hlox : ∀ lam : Λ, IsLoxodromic (g lam) (Cayley.base A.alphabet))
    (hcyc : ∀ lam : Λ,
      Elementary.elementaryClosure (g lam) = Subgroup.zpowers (g lam))
    (hlow : ∀ lam : Λ, ∃ alpha : ℝ, 0 < alpha ∧
      ∀ (n : ℕ) (h : G), h ∈
        (coneOffFamily A.alphabet
          (fun nu => Subgroup.zpowers (g nu))).relBall lam n →
        alpha * dist (Cayley.base A.alphabet) (h • Cayley.base A.alphabet)
          ≤ (n : ℝ)) :
    (coneOffFamily A.alphabet
      (fun lam => Subgroup.zpowers (g lam))).IsHyperbolicallyEmbedded := by
  exact isHyperbolicallyEmbedded_zpowers_of_elementaryClosure_eq_of_orbitBound
    A g hncom hlox hcyc (orbitBound_family_of_orbitLowerBound hlow)

end HullSC
end GroupApproximation
