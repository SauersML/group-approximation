import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyCompose
import GroupApproximation.GGT.HullSCRelatorSeparation2WindowDiffExact
import GroupApproximation.GGT.CayleyFourPointConverse

/-!
# Hull's relator separation from the jointly chosen exact design

The old endpoint asked for side exclusion uniformly over every exponent list.
This module keeps only the precise chosen-list seam left by the construction.

`ExactRelatorDesign₂` packages the list produced by
`exists_relator_exponents_window_diff_through_exact`.  It records depth,
translate separation, deep positive differences, bounded pure-run windows,
and bounded windows crossing the unique base letter.  The closure predicate
below is asked only for such a design, at the radius and minimum length fixed
by the block-count argument.  Thus it has no degenerate all-list branch.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

section ExactDesign

variable {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}

/-- All five finite-avoidance clauses carried by Hull's jointly chosen
exponent list. -/
def ExactRelatorDesign₂ (E : HypEmbeddedCore₂ A N) (baseLetter : G)
    (rho eps diffRadius W target : ℕ) (ms : List ℕ) : Prop :=
  ms.length = target ∧ ms.Nodup ∧
    (∀ m ∈ ms, ∀ s t : Bool,
      E.lox s ^ m ∉ E.rel.relBall t rho ∧
        (E.lox s ^ m)⁻¹ ∉ E.rel.relBall t rho) ∧
    (∀ i ∈ ms, ∀ j ∈ ms, i ≠ j → ∀ s : Bool,
      ∀ x ∈ E.rel.relBall s eps, ∀ x' ∈ E.rel.relBall s eps,
        x * E.lox s ^ i * x' ≠ E.lox s ^ j ∧
          x * E.lox s ^ i * x' ≠ (E.lox s ^ j)⁻¹) ∧
    (∀ i ∈ ms, ∀ j ∈ ms, j < i → ∀ s t : Bool,
      E.lox s ^ (i - j) ∉ E.rel.relBall t diffRadius) ∧
    (∀ pre post : List ℕ, ∀ n : ℕ, ms = pre ++ n :: post →
      ∀ s t : Bool, ∀ r : ℕ, r ≤ W →
        E.lox s ^ n * GGT.RelLetter.listVal
            (blockWord (E.lox false) (E.lox true) t (post.take r))
          ∉ E.rel.fam (!s)) ∧
    ∀ pre post : List ℕ, ∀ n : ℕ, ms = pre ++ n :: post →
      ∀ s b₀ b₁ : Bool, ∀ r₀ r₁ : ℕ, r₀ ≤ W → r₁ ≤ W →
        E.lox s ^ n * GGT.RelLetter.listVal
            (blockWord (E.lox false) (E.lox true) b₀ (post.take r₀)) *
            baseLetter * GGT.RelLetter.listVal
            (blockWord (E.lox false) (E.lox true) b₁ (post.take r₁))
          ∉ E.rel.fam (!s)

/-- The exact finite-avoidance construction, packaged without weakening any
of its clauses. -/
theorem exists_exactRelatorDesign₂ (E : HypEmbeddedCore₂ A N)
    (rho eps diffRadius : ℕ) (baseLetter : G) (W target : ℕ) :
    ∃ ms : List ℕ,
      ExactRelatorDesign₂ E baseLetter rho eps diffRadius W target ms := by
  exact exists_relator_exponents_window_diff_through_exact E rho eps
    diffRadius baseLetter W target

/-- The one remaining same-side implication, scoped only to the exact lists
the construction can produce.  Its window and difference radius is
`1 + blockConst`; its list is required to clear the same (C3) threshold used
by the four-way composition. -/
def SideExclusionOfExactDesign₂ (E : HypEmbeddedCore₂ A N)
    (cnt : ℕ) : Prop :=
  ∀ (baseLetter : G), baseLetter ∈ E.rel.base → ∀ (eps rho epsD Cm : ℕ),
    ∀ (target : ℕ) (ms : List ℕ),
      ExactRelatorDesign₂ E baseLetter (max rho (Cm * 4)) epsD
          (1 + blockConst [baseLetter] (max cnt (eps + 2)))
          (1 + blockConst [baseLetter] (max cnt (eps + 2))) target ms →
      [baseLetter].length +
          5 * blockSeparation [baseLetter] (max cnt (eps + 2)) eps + 3 ≤
        ms.length →
      RelatorSideExclusionAt₂ E [baseLetter] ms

/-- The separation theorem with the false all-list premise removed.  The
exact producer is invoked at a target enlarged to the composition's (C3)
threshold, and the side closure is consumed only for that returned list. -/
theorem separationNe₂_clause_of_exactDesign (E : HypEmbeddedCore₂ A N)
    (hN : Suitable A.alphabet N) (cnt : ℕ) {δ : ℕ}
    (hδ : Hyperbolic.IsFourPointHyperbolic E.rel.alphabet.carrier δ)
    (hcount : RelatorBlockCountInputOne₂ E cnt)
    (hside : SideExclusionOfExactDesign₂ E cnt)
    (t : G) (ht : t⁻¹ ∈ E.rel.base) (eps rho : ℕ) :
    ∃ B : ℕ, ∀ L : ℕ, ∃ (p : List G) (ms : List ℕ),
      (∀ g ∈ p, g ∈ E.rel.base) ∧ p.prod = t⁻¹ ∧ L ≤ ms.length ∧
        (∀ m ∈ ms, ∀ b : Bool, E.lox b ^ m ∉ E.rel.relBall b rho ∧
          (E.lox b ^ m)⁻¹ ∉ E.rel.relBall b rho) ∧
        ∀ w w' u₀ u₀' : List (GGT.RelLetter G Bool),
          RelWord.Sym (relatorWord₂ p (E.lox false) (E.lox true) ms) w →
            RelWord.Sym (relatorWord₂ p (E.lox false) (E.lox true) ms) w' →
              w' ≠ w → (∃ s, w = u₀ ++ s) → (∃ s', w' = u₀' ++ s') →
                B < u₀.length →
                  ∀ y z : G, wordNorm E.rel.base y ≤ eps →
                    wordNorm E.rel.base z ≤ eps →
                      GGT.RelLetter.listVal u₀'
                          = y * GGT.RelLetter.listVal u₀ * z →
                        GGT.RelLetter.listVal w'
                          = y * GGT.RelLetter.listVal w * y⁻¹ := by
  let p : List G := [t⁻¹]
  have hplen : p.length = 1 := by simp [p]
  have hp0 : 0 < p.length := by simp [p]
  have hpbase : ∀ g ∈ p, g ∈ E.rel.base := by
    intro g hg
    have hgt : g = t⁻¹ := by simpa [p] using hg
    simpa [hgt] using ht
  have hpprod : p.prod = t⁻¹ := by simp [p]
  apply separationNe₂_clause_of_spelling_of_producer E hN cnt hδ t p hp0
    hpbase hpprod (hcount p hplen) eps rho
  intro epsD Cm L
  let cw := max cnt (eps + 2)
  let W := 1 + blockConst p cw
  let target := max L (p.length + 5 * blockSeparation p cw eps + 3)
  obtain ⟨ms, hdesign⟩ :=
    exists_exactRelatorDesign₂ E (max rho (Cm * 4)) epsD W (t⁻¹) W target
  rcases hdesign with ⟨hlen, hnodup, hdeep, hsep, hdiff, hwin, hthrough⟩
  have hlong : p.length + 5 * blockSeparation p cw eps + 3 ≤ ms.length := by
    rw [hlen]
    exact Nat.le_max_right _ _
  have hexcl : RelatorSideExclusionAt₂ E p ms := by
    have hs := hside (t⁻¹) ht eps rho epsD Cm target ms
    simpa only [p, cw, W] using
      hs ⟨hlen, hnodup, hdeep, hsep, hdiff, hwin, hthrough⟩ hlong
  exact ⟨ms, by rw [hlen]; exact Nat.le_max_left _ _, hnodup, hdeep, hsep,
    hexcl⟩

end ExactDesign

section QuantifiedExactDesign

variable
  (hclosure : ∀ {G : Type u} [Group G] (A : HullGeneratingSet G)
    (N : Subgroup G) (E : HypEmbeddedCore₂ A N), ∃ cnt : ℕ,
      RelatorBlockCountInputOne₂ E cnt ∧ SideExclusionOfExactDesign₂ E cnt)

include hclosure in
/-- Corrected separation over every core, now resting on the exact-design
closure rather than the refuted universal-list exclusion. -/
theorem separationNe₂OfBaseLetter_of_exactDesign :
    ∀ {G : Type u} [Group G] (A : HullGeneratingSet G) (N : Subgroup G)
      (E : HypEmbeddedCore₂ A N), Suitable A.alphabet N →
        ∀ (t : G), t⁻¹ ∈ E.rel.base → ∀ (eps rho : ℕ),
          ∃ B : ℕ, ∀ L : ℕ,
            ∃ (p : List G) (ms : List ℕ),
              (∀ g ∈ p, g ∈ E.rel.base) ∧ p.prod = t⁻¹ ∧ L ≤ ms.length ∧
                (∀ m ∈ ms, ∀ b : Bool, E.lox b ^ m ∉ E.rel.relBall b rho ∧
                  (E.lox b ^ m)⁻¹ ∉ E.rel.relBall b rho) ∧
                ∀ w w' u₀ u₀' : List (GGT.RelLetter G Bool),
                  RelWord.Sym (relatorWord₂ p (E.lox false) (E.lox true) ms) w →
                    RelWord.Sym (relatorWord₂ p (E.lox false) (E.lox true) ms) w' →
                      w' ≠ w → (∃ s, w = u₀ ++ s) →
                        (∃ s', w' = u₀' ++ s') → B < u₀.length →
                          ∀ y z : G, wordNorm E.rel.base y ≤ eps →
                            wordNorm E.rel.base z ≤ eps →
                              GGT.RelLetter.listVal u₀'
                                  = y * GGT.RelLetter.listVal u₀ * z →
                                GGT.RelLetter.listVal w'
                                  = y * GGT.RelLetter.listVal w * y⁻¹ := by
  intro G _ A N E hN t ht eps rho
  obtain ⟨cnt, hcount, hside⟩ := hclosure A N E
  obtain ⟨δ, hδ⟩ :=
    GGT.exists_isFourPointHyperbolic_of_isHyperbolicallyEmbedded E.rel E.embedded
  exact separationNe₂_clause_of_exactDesign E hN cnt hδ hcount hside
    t ht eps rho

include hclosure in
/-- Hull's one-letter §6 endpoint with every finite-avoidance choice made
internally.  The sole residual is the exact-design side-closure implication. -/
theorem hullRelatorStatement₂OfBaseLetter_of_exactDesign :
    HullRelatorStatement₂OfBaseLetter.{u} :=
  hullRelatorStatement₂OfBaseLetter_of_separationNe₂
    (separationNe₂OfBaseLetter_of_exactDesign hclosure)

end QuantifiedExactDesign

end HullSC
end GroupApproximation
