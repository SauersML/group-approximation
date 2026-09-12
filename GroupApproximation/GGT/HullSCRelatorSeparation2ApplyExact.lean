import GroupApproximation.GGT.HullSCRelatorSeparation2WindowDiffExact

/-!
# Hull's relator separation from the jointly chosen exact design

The old endpoint asked for side exclusion uniformly over every exponent list.
This module packages the precise chosen-list design produced by the
construction.

`ExactRelatorDesign₂` packages the list produced by
`exists_relator_exponents_window_diff_through_exact`.  It records depth,
translate separation, deep positive differences, bounded pure-run windows,
and bounded windows crossing the unique base letter.  The fixed-list block
count and its cyclic parser live downstream, after this design has been chosen.
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

end ExactDesign

end HullSC
end GroupApproximation
