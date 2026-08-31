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
    CyclicThroughBaseAvoidance E.rel E.lox baseLetter W ms ∧
    BaseFirstAvoidance E.rel E.lox baseLetter W ms

/-- The exact finite-avoidance construction, packaged without weakening any
of its clauses. -/
theorem exists_exactRelatorDesign₂ (E : HypEmbeddedCore₂ A N)
    (rho eps diffRadius : ℕ) (baseLetter : G) (W target : ℕ) :
    ∃ ms : List ℕ,
      ExactRelatorDesign₂ E baseLetter rho eps diffRadius W target ms := by
  exact exists_relator_exponents_window_diff_through_exact E rho eps
    diffRadius baseLetter W target

/-- After peeling an anchor of index `s`, a bounded pure-run window begins
with an `!s`-letter and cannot return to the anchor family. -/
theorem ExactRelatorDesign₂.pureWindow_not_mem_anchorFamily
    {E : HypEmbeddedCore₂ A N} {baseLetter : G}
    {rho eps diffRadius W target : ℕ} {ms : List ℕ}
    (h : ExactRelatorDesign₂ E baseLetter rho eps diffRadius W target ms)
    {pre post : List ℕ} {n : ℕ} (hsplit : ms = pre ++ n :: post)
    (s t : Bool) {r : ℕ} (hr : r ≤ W) :
    E.lox (!s) ^ n * GGT.RelLetter.listVal
        (blockWord (E.lox false) (E.lox true) t (post.take r))
      ∉ E.rel.fam s := by
  have hwin := h.2.2.2.2.2.1 pre post n hsplit (!s) t r hr
  simpa using hwin

/-- The analogous peeled window when the cyclic interval crosses the unique
base letter.  The suffix comes from `post` and the complementary prefix from
`pre`; this is the corrected cyclic orientation. -/
theorem ExactRelatorDesign₂.throughBase_not_mem_anchorFamily
    {E : HypEmbeddedCore₂ A N} {baseLetter : G}
    {rho eps diffRadius W target : ℕ} {ms : List ℕ}
    (h : ExactRelatorDesign₂ E baseLetter rho eps diffRadius W target ms)
    {pre post : List ℕ} {n : ℕ} (hsplit : ms = pre ++ n :: post)
    (s b₀ b₁ : Bool) {r₀ r₁ : ℕ} (hr₀ : r₀ ≤ W) (hr₁ : r₁ ≤ W) :
    E.lox (!s) ^ n * GGT.RelLetter.listVal
        (blockWord (E.lox false) (E.lox true) b₀ (post.take r₀)) *
        baseLetter * GGT.RelLetter.listVal
        (blockWord (E.lox false) (E.lox true) b₁ (pre.take r₁))
      ∉ E.rel.fam s := by
  have hthrough := h.2.2.2.2.2.2.1 pre post n hsplit (!s) b₀ b₁ r₀ r₁
    hr₀ hr₁
  simpa using hthrough

/-- The exceptional seam after the final `true` block starts at the base
letter and continues through the first `false` block. -/
theorem ExactRelatorDesign₂.baseFirst_not_mem_trueFamily
    {E : HypEmbeddedCore₂ A N} {baseLetter : G}
    {rho eps diffRadius W target : ℕ} {ms : List ℕ}
    (h : ExactRelatorDesign₂ E baseLetter rho eps diffRadius W target ms)
    {n : ℕ} {post : List ℕ} (hms : ms = n :: post)
    {r : ℕ} (hr : r ≤ W) :
    baseLetter * E.lox false ^ n * GGT.RelLetter.listVal
        (blockWord (E.lox false) (E.lox true) true (post.take r))
      ∉ E.rel.fam true := by
  subst ms
  exact h.2.2.2.2.2.2.2 r hr

/-- The one remaining same-side implication, scoped only to the exact lists
the construction can produce.  Its window and difference radius is
`1 + blockConst`; its list is required to clear the same (C3) threshold used
by the four-way composition. -/
def SideExclusionOfExactDesign₂ (E : HypEmbeddedCore₂ A N)
    (cnt : ℕ) : Prop :=
  RelatorBlockCountInputOne₂ E cnt →
  ∀ (baseLetter : G), baseLetter ∈ E.rel.base → ∀ (eps rho epsD Cm : ℕ),
    ∀ (target : ℕ) (ms : List ℕ),
      Even target →
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
theorem separationNe₂_clause_of_exactDesign_of_sideExclusion
    (E : HypEmbeddedCore₂ A N)
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
  let threshold := p.length + 5 * blockSeparation p cw eps + 3
  let target := 2 * max L threshold
  obtain ⟨ms, hdesign⟩ :=
    exists_exactRelatorDesign₂ E (max rho (Cm * 4)) epsD W (t⁻¹) W target
  rcases hdesign with
    ⟨hlen, hnodup, hdeep, hsep, hdiff, hwin, hthrough, hbaseFirst⟩
  have htargetEven : Even target := by
    refine ⟨max L threshold, ?_⟩
    simp only [target, two_mul]
  have hlong : p.length + 5 * blockSeparation p cw eps + 3 ≤ ms.length := by
    rw [hlen]
    simp only [target, threshold]
    omega
  have hexcl : RelatorSideExclusionAt₂ E p ms := by
    have hs := hside hcount (t⁻¹) ht eps rho epsD Cm target ms
    simpa only [p, cw, W] using
      hs htargetEven
        ⟨hlen, hnodup, hdeep, hsep, hdiff, hwin, hthrough, hbaseFirst⟩ hlong
  refine ⟨ms, ?_, hnodup, hdeep, hsep, hexcl⟩
  rw [hlen]
  simp only [target]
  omega

end ExactDesign

end HullSC
end GroupApproximation
