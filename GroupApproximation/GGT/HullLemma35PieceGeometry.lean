import GroupApproximation.GGT.OsinLemma55GuessingGeodesics
import GroupApproximation.Algebra.HyperbolicSlimFourPoint
import GroupApproximation.Meta.AxiomGuard

/-!
# Hull's Lemma 3.5: slim polygons with short sides

The manuscript's paragraph on Fournier-Facio's group (section `sec:torsion-free`, tex 1680-1684)
says:

> The group $G_0$ is obtained there as a common quotient of two finitely generated acylindrically
> hyperbolic groups by Hull's theorem~\cite[Corollary~7.4]{Hull}, which allows the quotient to be
> chosen acylindrically hyperbolic; we take $G_0$ to be such a quotient.

Hull's proof of Corollary 7.4 uses his Lemma 3.5 (`PrintedHullLemma35`).  When a component letter
of one side of a triangle shares its coset with components of the other sides, its expansion lies
on one side of a quadrilateral or a hexagon in the Cayley graph of the peripheral subgroup, whose
other sides are short connectors and the expansions of those components.  In a group with a
`δ`-hyperbolic word metric this module bounds the distance from the points between two corners of
such a polygon to a set `P` holding the far ends of the short sides and the vertices of the long
ones (`nearBetween_quad`, `nearBetween_hexagon`).
-/

namespace GroupApproximation
namespace GGT
namespace HullLemma35

open GroupApproximation.WordMetric

universe u

section Polygons

variable {H : Type u} [Group H]

/-- **Every point between `X` and `Y` is within `K` of `P`** in `Γ(H, A)`. -/
def NearBetween (A P : Set H) (K : ℕ) (X Y : H) : Prop :=
  ∀ q : H, Hyperbolic.IsBetween A X q Y → ∃ p ∈ P, wordDist A q p ≤ K

theorem NearBetween.mono {A P : Set H} {K K' : ℕ} {X Y : H} (h : NearBetween A P K X Y)
    (hK : K ≤ K') : NearBetween A P K' X Y := by
  intro q hq
  obtain ⟨p, hp, hd⟩ := h q hq
  exact ⟨p, hp, le_trans hd hK⟩

/-- Points between `X` and `Y` are within `d(X, Y)` of `Y`. -/
theorem nearBetween_of_right {A P : Set H} {K : ℕ} {X Y : H} (hY : Y ∈ P)
    (hXY : wordDist A X Y ≤ K) : NearBetween A P K X Y := by
  intro q hq
  refine ⟨Y, hY, ?_⟩
  have h : wordDist A X q + wordDist A q Y = wordDist A X Y := hq
  omega

/-- Points between `X` and `Y` are within `d(X, Y)` of `X`. -/
theorem nearBetween_of_left {A P : Set H} (hA : IsSymmetricGeneratingSet A) {K : ℕ} {X Y : H}
    (hX : X ∈ P) (hXY : wordDist A X Y ≤ K) : NearBetween A P K X Y := by
  intro q hq
  refine ⟨X, hX, ?_⟩
  have h : wordDist A X q + wordDist A q Y = wordDist A X Y := hq
  rw [wordDist_comm hA]
  omega

/-- **A side with its vertices in `P`**: points between its ends are `2δ`-close to `P`. -/
theorem nearBetween_of_side {A P : Set H} (hA : IsSymmetricGeneratingSet A) {δ : ℕ}
    (hδ : Hyperbolic.IsFourPointHyperbolic A δ) {X Y : H}
    (hside : ∀ m ≤ wordDist A X Y, ∃ c ∈ P, Hyperbolic.IsBetween A X c Y ∧ wordDist A X c = m) :
    NearBetween A P (2 * δ) X Y := by
  intro q hq
  have hm : wordDist A X q ≤ wordDist A X Y := by
    have h : wordDist A X q + wordDist A q Y = wordDist A X Y := hq
    omega
  obtain ⟨c, hc, hbet, hdc⟩ := hside _ hm
  exact ⟨c, hc, OsinEnlargement.wordDist_le_of_isBetween_of_wordDist_eq hA hδ hq hbet hdc.symm⟩

/-- **Slim triangles**: nearness on two sides gives nearness on the third, `4δ` further. -/
theorem nearBetween_of_slim {A P : Set H} (hA : IsSymmetricGeneratingSet A) {δ : ℕ}
    (hδ : Hyperbolic.IsFourPointHyperbolic A δ) {X Y Z : H} {K : ℕ}
    (h₁ : NearBetween A P K X Z) (h₂ : NearBetween A P K Z Y) :
    NearBetween A P (4 * δ + K) X Y := by
  intro q hq
  rcases Hyperbolic.isSlimTriangles_of_isFourPointHyperbolic hA hδ X Y Z q hq with
      ⟨r, hr, hdr⟩ | ⟨r, hr, hdr⟩
  · obtain ⟨p, hp, hd⟩ := h₁ r hr
    have htri := wordDist_triangle hA q r p
    exact ⟨p, hp, by omega⟩
  · obtain ⟨p, hp, hd⟩ := h₂ r hr
    have htri := wordDist_triangle hA q r p
    exact ⟨p, hp, by omega⟩

/-- **A quadrilateral with two short sides.**  The corners are `X₀ X₁ X₂ X₃`; the sides from `X₁`
to `X₂` and from `X₃` to `X₀` are at most `Tb` long with `X₂, X₃ ∈ P`, and the side from `X₃` to
`X₂` has its vertices in `P`. -/
theorem nearBetween_quad {A P : Set H} (hA : IsSymmetricGeneratingSet A) {δ : ℕ}
    (hδ : Hyperbolic.IsFourPointHyperbolic A δ) {X₀ X₁ X₂ X₃ : H} {Tb : ℕ}
    (h₁₂ : wordDist A X₁ X₂ ≤ Tb) (hX₂ : X₂ ∈ P)
    (hside : ∀ m ≤ wordDist A X₃ X₂,
      ∃ c ∈ P, Hyperbolic.IsBetween A X₃ c X₂ ∧ wordDist A X₃ c = m)
    (h₀₃ : wordDist A X₀ X₃ ≤ Tb) (hX₃ : X₃ ∈ P) :
    NearBetween A P (8 * δ + (2 * δ + Tb)) X₀ X₁ := by
  have h₂₁ : wordDist A X₂ X₁ ≤ Tb := by
    rw [wordDist_comm hA]
    exact h₁₂
  have hs32 : NearBetween A P (2 * δ + Tb) X₃ X₂ :=
    (nearBetween_of_side hA hδ hside).mono (Nat.le_add_right _ _)
  have hs21 : NearBetween A P (2 * δ + Tb) X₂ X₁ :=
    (nearBetween_of_left hA hX₂ h₂₁).mono (Nat.le_add_left _ _)
  have hs31 : NearBetween A P (4 * δ + (2 * δ + Tb)) X₃ X₁ :=
    nearBetween_of_slim hA hδ hs32 hs21
  have hs03 : NearBetween A P (4 * δ + (2 * δ + Tb)) X₀ X₃ :=
    (nearBetween_of_right hX₃ h₀₃).mono (by omega)
  exact (nearBetween_of_slim hA hδ hs03 hs31).mono (by omega)

/-- **A hexagon with three short sides.**  The corners are `X₀ X₁ X₂ X₃ X₄ X₅`; the sides from `X₁`
to `X₂`, from `X₃` to `X₄` and from `X₅` to `X₀` are at most `Tb` long with `X₂, X₄, X₅ ∈ P`, and
the sides from `X₃` to `X₂` and from `X₅` to `X₄` have their vertices in `P`. -/
theorem nearBetween_hexagon {A P : Set H} (hA : IsSymmetricGeneratingSet A) {δ : ℕ}
    (hδ : Hyperbolic.IsFourPointHyperbolic A δ) {X₀ X₁ X₂ X₃ X₄ X₅ : H} {Tb : ℕ}
    (h₁₂ : wordDist A X₁ X₂ ≤ Tb) (hX₂ : X₂ ∈ P)
    (hside₃₂ : ∀ m ≤ wordDist A X₃ X₂,
      ∃ c ∈ P, Hyperbolic.IsBetween A X₃ c X₂ ∧ wordDist A X₃ c = m)
    (h₃₄ : wordDist A X₃ X₄ ≤ Tb) (hX₄ : X₄ ∈ P)
    (hside₅₄ : ∀ m ≤ wordDist A X₅ X₄,
      ∃ c ∈ P, Hyperbolic.IsBetween A X₅ c X₄ ∧ wordDist A X₅ c = m)
    (h₀₅ : wordDist A X₀ X₅ ≤ Tb) (hX₅ : X₅ ∈ P) :
    NearBetween A P (12 * δ + (2 * δ + Tb)) X₀ X₁ := by
  have h₂₁ : wordDist A X₂ X₁ ≤ Tb := by
    rw [wordDist_comm hA]
    exact h₁₂
  have h₄₃ : wordDist A X₄ X₃ ≤ Tb := by
    rw [wordDist_comm hA]
    exact h₃₄
  -- the far side, through `X₅` and `X₄`
  have hs54 : NearBetween A P (2 * δ + Tb) X₅ X₄ :=
    (nearBetween_of_side hA hδ hside₅₄).mono (Nat.le_add_right _ _)
  have hs43 : NearBetween A P (2 * δ + Tb) X₄ X₃ :=
    (nearBetween_of_left hA hX₄ h₄₃).mono (Nat.le_add_left _ _)
  have hs53 : NearBetween A P (4 * δ + (2 * δ + Tb)) X₅ X₃ :=
    nearBetween_of_slim hA hδ hs54 hs43
  have hs05 : NearBetween A P (4 * δ + (2 * δ + Tb)) X₀ X₅ :=
    (nearBetween_of_right hX₅ h₀₅).mono (by omega)
  have hs03 : NearBetween A P (4 * δ + (4 * δ + (2 * δ + Tb))) X₀ X₃ :=
    nearBetween_of_slim hA hδ hs05 hs53
  -- the near side, through `X₂`
  have hs32 : NearBetween A P (2 * δ + Tb) X₃ X₂ :=
    (nearBetween_of_side hA hδ hside₃₂).mono (Nat.le_add_right _ _)
  have hs21 : NearBetween A P (2 * δ + Tb) X₂ X₁ :=
    (nearBetween_of_left hA hX₂ h₂₁).mono (Nat.le_add_left _ _)
  have hs31 : NearBetween A P (4 * δ + (4 * δ + (2 * δ + Tb))) X₃ X₁ :=
    (nearBetween_of_slim hA hδ hs32 hs21).mono (by omega)
  exact (nearBetween_of_slim hA hδ hs03 hs31).mono (by omega)

end Polygons

end HullLemma35
end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.HullLemma35.nearBetween_of_side
#audit_axioms GroupApproximation.GGT.HullLemma35.nearBetween_of_slim
#audit_axioms GroupApproximation.GGT.HullLemma35.nearBetween_quad
#audit_axioms GroupApproximation.GGT.HullLemma35.nearBetween_hexagon
