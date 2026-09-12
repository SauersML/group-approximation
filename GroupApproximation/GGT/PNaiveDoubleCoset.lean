import GroupApproximation.GGT.PNaiveChain

/-!
# Transverse elements do not bridge two powers of a partner with a local gap

Infrastructure for the two-sided form of Gerasimova--Osin's Lemma 4.2, the
statement `f ⟨y⟩ g⁻¹ ∩ ⟨y⟩ = 1` for `f, g` in a prescribed finite set.

Let `h` have a local gap at `o` (turn at most `C`, step more than `2(C+δ)`) and
put `ρ = d(o, h·o) − (C+δ)`.  Suppose `f` is transverse to both ends of `h` on
the two shadows of depth `ρ` — the hypothesis the ping-pong of property
`P_naive` spends — and that `f` and `g` move `o` by at most `E`, with
`ρ > C + δ + E` and `ρ > 2E`.  Then

    f · hᵃ · g⁻¹ ≠ hᵇ   for all integers a and b ≠ 0

(`mul_zpow_mul_inv_ne_zpow`).  The argument is one comparison of Gromov
products.  If `f·hᵃ = hᵇ·g`, then `f·(hᵃ·o) = hᵇ·(g·o)` lies within `E` of `hᵇ·o`.
That point is at depth `ρ` in a shadow of `h`.  So `f·(hᵃ·o)` follows an end of
`h` for at least `ρ − E`.  When `a ≠ 0`, `hᵃ·o` is itself in a shadow, and
transversality caps that at `C + δ`.  When `a = 0`, the point is `f·o`, which is
within `E` of `o`, while `hᵇ·o` is at distance at least `ρ`.

## Manuscript status

Infrastructure for `cor:regular-nonmf-algebra` (stable rank one through
Gerasimova--Osin); certifies no printed sentence on its own.
-/

namespace GroupApproximation
namespace GGT
namespace PNaive

open GroupApproximation.HullGeometry

universe u v

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X] [MulAction G X]

/-- **A nonzero power of a partner with a local gap lies deep in one shadow.** -/
theorem zpow_smul_self_mem_shadows {δ C : ℝ} (hδ : IsHyperbolicSpace δ X)
    (hiso : IsIsometricAction G X) {h : G} {o : X} (hCδ : 0 ≤ C + δ)
    (hloc : gromovProduct (h • o) (h⁻¹ • o) o ≤ C)
    (hgap : 2 * (C + δ) < dist o (h • o)) {n : ℤ} (hn : n ≠ 0) :
    (h ^ n) • o ∈ shadow o (h • o) (dist o (h • o) - (C + δ)) ∪
      shadow o (h⁻¹ • o) (dist o (h • o) - (C + δ)) := by
  have hzero : ∀ z : X, gromovProduct o z o ≤ C + δ := by
    intro z
    rw [gromovProduct_self_base]
    exact hCδ
  exact zpow_smul_mem_shadows hδ hiso hloc hgap (hzero _) (hzero _) hn

/-- **A point of either shadow is far from the basepoint.** -/
theorem le_dist_of_mem_shadows {o z z' x : X} {ρ : ℝ}
    (hx : x ∈ shadow o z ρ ∪ shadow o z' ρ) : ρ ≤ dist x o := by
  rcases hx with hx | hx
  · have hle := gromovProduct_le_right z x o
    rw [gromovProduct_comm] at hle
    exact le_trans hx hle
  · have hle := gromovProduct_le_right z' x o
    rw [gromovProduct_comm] at hle
    exact le_trans hx hle

/-- **Transverse elements do not bridge two powers of the partner.** -/
theorem mul_zpow_mul_inv_ne_zpow {δ C E : ℝ} (hδ : IsHyperbolicSpace δ X)
    (hiso : IsIsometricAction G X) {h f g : G} {o : X} (hCδ : 0 ≤ C + δ)
    (hloc : gromovProduct (h • o) (h⁻¹ • o) o ≤ C)
    (hgap : 2 * (C + δ) < dist o (h • o))
    (htrans : ∀ x ∈ shadow o (h • o) (dist o (h • o) - (C + δ)) ∪
        shadow o (h⁻¹ • o) (dist o (h • o) - (C + δ)),
      gromovProduct (f • x) (h • o) o ≤ C + δ ∧
        gromovProduct (f • x) (h⁻¹ • o) o ≤ C + δ)
    (hf : dist o (f • o) ≤ E) (hg : dist o (g • o) ≤ E)
    (hρ₁ : C + δ + E < dist o (h • o) - (C + δ))
    (hρ₂ : 2 * E < dist o (h • o) - (C + δ)) :
    ∀ a b : ℤ, b ≠ 0 → f * h ^ a * g⁻¹ ≠ h ^ b := by
  intro a b hb heq
  set ρ : ℝ := dist o (h • o) - (C + δ) with hρdef
  -- `f · (hᵃ·o) = hᵇ · (g·o)`
  have hpoint : f • (h ^ a) • o = (h ^ b) • g • o := by
    have h1 : f * h ^ a = h ^ b * g := by
      rw [← heq]
      group
    rw [smul_smul, h1, mul_smul]
  have hclose : dist ((h ^ b) • g • o) ((h ^ b) • o) ≤ E := by
    rw [hiso (h ^ b) (g • o) o, dist_comm]
    exact hg
  have hdeep := zpow_smul_self_mem_shadows hδ hiso hCδ hloc hgap hb
  by_cases ha : a = 0
  · -- `f·o` is near `o`, while `hᵇ·o` is far
    subst ha
    rw [zpow_zero, one_smul] at hpoint
    have hfar : ρ ≤ dist ((h ^ b) • o) o := le_dist_of_mem_shadows hdeep
    have htri : dist ((h ^ b) • o) o ≤
        dist ((h ^ b) • o) ((h ^ b) • g • o) + dist ((h ^ b) • g • o) o :=
      dist_triangle _ _ _
    have h2 : dist ((h ^ b) • g • o) o = dist o (f • o) := by
      rw [← hpoint, dist_comm]
    have hclose' : dist ((h ^ b) • o) ((h ^ b) • g • o) ≤ E := by
      rw [dist_comm]
      exact hclose
    linarith
  · -- `f·(hᵃ·o)` follows an end of `h` for at least `ρ − E`, against transversality
    have hsh := zpow_smul_self_mem_shadows hδ hiso hCδ hloc hgap ha
    obtain ⟨hpos, hneg⟩ := htrans _ hsh
    rcases hdeep with hdeep | hdeep
    · have hlow := gromovProduct_le_add_dist_left ((h ^ b) • o) ((h ^ b) • g • o) (h • o) o
      rw [mem_shadow] at hdeep
      rw [← hpoint, dist_comm] at hlow
      rw [← hpoint] at hclose
      linarith
    · have hlow := gromovProduct_le_add_dist_left ((h ^ b) • o) ((h ^ b) • g • o) (h⁻¹ • o) o
      rw [mem_shadow] at hdeep
      rw [← hpoint, dist_comm] at hlow
      rw [← hpoint] at hclose
      linarith

end PNaive
end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.PNaive.zpow_smul_self_mem_shadows
#audit_axioms GroupApproximation.GGT.PNaive.le_dist_of_mem_shadows
#audit_axioms GroupApproximation.GGT.PNaive.mul_zpow_mul_inv_ne_zpow
