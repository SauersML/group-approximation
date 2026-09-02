import GroupApproximation.GGT.DGOLemma421Statement
import GroupApproximation.GGT.DGOPolygonCutFamily

/-!
# DGO Lemma 4.21 from the uniform isolated-component sum bound

Dahmani--Guirardel--Osin Proposition 4.14 states that, in a weakly relatively
hyperbolic group, the total relative length of distinguished isolated
components in an `n`-gon is bounded by `C(μ,c) n` when all other sides are
`(μ,c)`-quasi-geodesic.  `DGOUniformSumBound` is that conclusion in the
radius-witness form used by `DGOPolygonCut.SumBound`, and
`DGOProposition414Uniform` keeps the source's quantifier order.

The rest of this module proves DGO Lemma 4.21(b) from that uniform bound.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.WordMetric
open GroupApproximation.GGT.DGOPolygonCut

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **The conclusion of DGO Proposition 4.14 at fixed parameters.**

This is Definition 4.13 and Proposition 4.14 written with a radius witness.
The distinguished sides are isolated components and every other side is
`(μ,c)`-quasi-geodesic.  One radius function bounds all distinguished spans,
and its total is at most `C n`. -/
def DGOUniformSumBound (D : RelGenSet G Λ) (mu c : ℝ) (C : ℕ) : Prop :=
  ∀ (n : ℕ) (v : G) (word : List (RelLetter G Λ))
      (cut : ℕ → ℕ) (I : Finset ℕ) (lam : ℕ → Λ),
    (∀ a ∈ word, D.IsLetter a) →
    RelLetter.listVal word = 1 →
    IsPolygonCut n word cut →
    (∀ s ∈ I, s < n) →
    (∀ s ∈ I, cut (s + 1) = cut s + 1) →
    (∀ s ∈ I, IsComp (lam s) word (cut s) (cut (s + 1))) →
    (∀ s ∈ I, IsIsolated D.fam (lam s) v word (cut s)) →
    (∀ s : ℕ, s < n → s ∉ I → ∀ p q : ℕ,
      cut s ≤ p → p ≤ q → q ≤ cut (s + 1) →
      ((q - p : ℕ) : ℝ) / mu - c ≤
        ((wordDist D.alphabet.carrier
          (vertex v word p) (vertex v word q) : ℕ) : ℝ)) →
    ∃ r : ℕ → ℕ,
      (∀ s ∈ I,
        (vertex v word (cut s))⁻¹ * vertex v word (cut (s + 1))
          ∈ D.relBall (lam s) (r s)) ∧
      ∑ s ∈ I, r s ≤ C * n

/-- **Dahmani--Guirardel--Osin Proposition 4.14, with uniformity in `n`.**

The quantifier order is the one printed in Proposition 4.14: after the group,
relative structure, and weak-hyperbolicity hypothesis are fixed, arbitrary
`μ ≥ 1` and `c ≥ 0` determine one positive constant `C(μ,c)` which works for
every `n`-gon. -/
def DGOProposition414Uniform : Prop :=
  ∀ (G : Type u) [Group G] (Λ : Type w) (D : RelGenSet G Λ),
    (∃ delta : ℝ, IsHyperbolicSpace delta (Cayley D.alphabet)) →
    ∀ mu c : ℝ, 1 ≤ mu → 0 ≤ c →
      ∃ C : ℕ, 0 < C ∧ DGOUniformSumBound D mu c C

/-- The uniform Proposition 4.14 statement specializes to the landed
`(1,0)` sum-bound interface. -/
theorem exists_sumBound_zero_of_uniform414
    (h : DGOProposition414Uniform.{u, w}) (D : RelGenSet G Λ)
    (hhyp : ∃ delta : ℝ, IsHyperbolicSpace delta (Cayley D.alphabet)) :
    ∃ C : ℕ, 0 < C ∧ ∀ n : ℕ, SumBound D 0 n (C * n) := by
  obtain ⟨C, hC, hbound⟩ := h G Λ D hhyp 1 0 le_rfl le_rfl
  refine ⟨C, hC, ?_⟩
  intro n v word cut I lam hlet hclosed hcut hI hedge hcomp hiso hquasi
  apply hbound n v word cut I lam hlet hclosed hcut hI hedge hcomp hiso
  intro s hs hsI p q hp hpq hq
  simpa using hquasi s hs hsI p q hp hpq hq

/-! ## Model test for the uniform-bound payload -/

/-- The relative structure on the trivial group with one trivial peripheral
member.  Keeping a genuine peripheral index makes the model test non-vacuous. -/
private def trivialUniformRelGenSet : RelGenSet PUnit Unit where
  base := Set.univ
  fam := fun _ => ⊤
  symmetricGenerating := by
    have h := Hyperbolic.isSymmetricGeneratingSet_univ (G := PUnit)
    rw [Finset.coe_univ] at h
    simpa only [Set.univ_union] using h

/-- In the one-point model every distinguished span is the identity, so the
uniform sum bound holds with radius zero for every parameter and constant. -/
theorem dgoUniformSumBound_trivialModel (mu c : ℝ) (C : ℕ) :
    DGOUniformSumBound trivialUniformRelGenSet mu c C := by
  intro n v word cut I lam hlet hclosed hcut hI hedge hcomp hiso hquasi
  refine ⟨fun _ => 0, ?_, by simp⟩
  intro s hs
  have hspan :
      (vertex v word (cut s))⁻¹ * vertex v word (cut (s + 1)) = 1 :=
    Subsingleton.elim _ _
  rw [hspan]
  exact one_mem_relBall trivialUniformRelGenSet (lam s) 0

/-- The positive uniform constant required by Proposition 4.14 exists in the
nonempty-peripheral trivial model. -/
theorem dgoProposition414Uniform_trivialModel (mu c : ℝ)
    (_hmu : 1 ≤ mu) (_hc : 0 ≤ c) :
    ∃ C : ℕ, 0 < C ∧ DGOUniformSumBound trivialUniformRelGenSet mu c C := by
  exact ⟨1, Nat.zero_lt_one, dgoUniformSumBound_trivialModel mu c 1⟩

end OsinComponents
end GGT
end GroupApproximation
