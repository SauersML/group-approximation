import GroupApproximation.Sofic.HullSuitabilityGeometry

/-!
# Shadows and north--south dynamics under the four-point condition

First module of property `P_naive` for acylindrically hyperbolic groups
(Abbott--Dahmani, arXiv:1610.04143, Theorem 2.3), in the form this repository
can carry: there is no Gromov boundary here, so the neighbourhoods of the two
fixed points of a loxodromic element are replaced by **shadows** cut out by the
Gromov product at a basepoint,

    shadow o z ρ = { x | ρ ≤ (x | z)_o }.

Everything below uses only an isometric action and Gromov's four-point
condition `HullGeometry.IsHyperbolicSpace`; no geodesics, no boundary, no
acylindricity.

## The one identity everything rests on

For every `h`, `x`, `o`,

    (h·x | h·o)_o = d(o, h·o) − (x | h⁻¹·o)_o.

It is exact (`gromovProduct_smul_self_base`): translate by `h⁻¹` and add the two
complementary Gromov products of a segment.  So a point that does not follow
`h⁻¹·o` from `o` for long is carried by `h` deep into the shadow of `h·o`.

## North--south dynamics

Suppose `h` has a **local gap**: the turn `(h·o | h⁻¹·o)_o` at the basepoint is at
most `C`, and the step `d(o, h·o)` exceeds `2(C+δ)`.  Then every point `x` with
`(x | h⁻¹·o)_o ≤ C + δ` satisfies, for every `n ≥ 1`,

    d(o, h·o) − (C+δ) ≤ (hⁿ·x | h·o)_o   and   (hⁿ·x | h⁻¹·o)_o ≤ C + δ

(`gromovProduct_pow_smul`): the identity gives the first bound at each step, and
the upper-bound form of the four-point inequality
(`HullGeometry.gromovProduct_le_add_delta_of_lt`) turns it into the second, which
feeds the next step.  With `ρ = d(o, h·o) − (C+δ)` the two shadows of `h·o` and
`h⁻¹·o` are disjoint, each is sent into itself by the corresponding powers, and
every nonzero power of `h` sends any point transverse to both into one of them
(`zpow_smul_mem_shadows`).  This is the half of the ping-pong table that belongs
to `h`.

## Manuscript status

Infrastructure for `cor:regular-nonmf-algebra` through property `P_naive`;
certifies no printed sentence on its own.
-/

namespace GroupApproximation
namespace GGT
namespace PNaive

open GroupApproximation.HullGeometry

universe u v

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X] [MulAction G X]

/-! ## Shadows -/

/-- **The shadow of `z` seen from `o` at depth `ρ`**: the points that follow `z`
from `o` for at least `ρ`, in the sense of the Gromov product. -/
def shadow (o z : X) (ρ : ℝ) : Set X :=
  {x | ρ ≤ gromovProduct x z o}

theorem mem_shadow {o z x : X} {ρ : ℝ} :
    x ∈ shadow o z ρ ↔ ρ ≤ gromovProduct x z o :=
  Iff.rfl

/-! ## The exact identity -/

/-- **Distance moved by a translate, against the turn at the basepoint.**
`(h·x | h·o)_o = d(o, h·o) − (x | h⁻¹·o)_o`. -/
theorem gromovProduct_smul_self_base (hiso : IsIsometricAction G X) (h : G)
    (x o : X) :
    gromovProduct (h • x) (h • o) o = dist o (h • o) - gromovProduct x (h⁻¹ • o) o := by
  have h1 : gromovProduct x o (h⁻¹ • o) = gromovProduct (h • x) (h • o) o := by
    have := gromovProduct_smul hiso h⁻¹ (h • x) (h • o) o
    simpa only [inv_smul_smul] using this
  have h2 := gromovProduct_add_swap_base x (h⁻¹ • o) o
  have h3 : dist o (h • o) = dist (h⁻¹ • o) o := by
    have := hiso h (h⁻¹ • o) o
    rwa [smul_inv_smul] at this
  linarith

/-- The step of `h⁻¹` at the basepoint has the same length as the step of `h`. -/
theorem dist_inv_smul (hiso : IsIsometricAction G X) (h : G) (o : X) :
    dist o (h⁻¹ • o) = dist o (h • o) := by
  have := hiso h o (h⁻¹ • o)
  rw [smul_inv_smul] at this
  rw [← this, dist_comm]

/-! ## North--south dynamics along the positive powers -/

/-- **North--south dynamics for a local gap.**  If the turn of `h` at `o` is at
most `C` and its step exceeds `2(C+δ)`, then every point with
`(x | h⁻¹·o)_o ≤ C + δ` is carried by every positive power of `h` to depth
`d(o,h·o) − (C+δ)` in the shadow of `h·o`, and stays transverse to `h⁻¹·o`. -/
theorem gromovProduct_pow_smul {δ C : ℝ} (hδ : IsHyperbolicSpace δ X)
    (hiso : IsIsometricAction G X) {h : G} {o : X}
    (hloc : gromovProduct (h • o) (h⁻¹ • o) o ≤ C)
    (hgap : 2 * (C + δ) < dist o (h • o)) {x : X}
    (hx : gromovProduct x (h⁻¹ • o) o ≤ C + δ) (n : ℕ) (hn : 1 ≤ n) :
    dist o (h • o) - (C + δ) ≤ gromovProduct ((h ^ n) • x) (h • o) o ∧
      gromovProduct ((h ^ n) • x) (h⁻¹ • o) o ≤ C + δ := by
  induction n with
  | zero => exact absurd hn (by norm_num)
  | succ k ih =>
    have hprev : gromovProduct ((h ^ k) • x) (h⁻¹ • o) o ≤ C + δ := by
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        simpa only [pow_zero, one_smul] using hx
      · exact (ih hk).2
    have hfirst :
        dist o (h • o) - (C + δ) ≤ gromovProduct ((h ^ (k + 1)) • x) (h • o) o := by
      rw [pow_succ', mul_smul, gromovProduct_smul_self_base hiso]
      linarith
    refine ⟨hfirst, ?_⟩
    have hfar : gromovProduct (h • o) (h⁻¹ • o) o + δ <
        gromovProduct ((h ^ (k + 1)) • x) (h • o) o := by
      linarith
    have hup := gromovProduct_le_add_delta_of_lt hδ hfar
    linarith

/-! ## Both directions -/

/-- The local gap of `h⁻¹` is the local gap of `h`. -/
theorem gromovProduct_inv_turn (h : G) (o : X) :
    gromovProduct (h⁻¹ • o) (h⁻¹⁻¹ • o) o = gromovProduct (h • o) (h⁻¹ • o) o := by
  rw [inv_inv, gromovProduct_comm]

/-- **The two shadows of a local gap are disjoint.** -/
theorem disjoint_shadows {δ C : ℝ} (hδ : IsHyperbolicSpace δ X) {h : G} {o : X}
    (hloc : gromovProduct (h • o) (h⁻¹ • o) o ≤ C) {ρ : ℝ} (hρ : C + δ < ρ) :
    Disjoint (shadow o (h • o) ρ) (shadow o (h⁻¹ • o) ρ) := by
  refine Set.disjoint_left.mpr ?_
  intro x hpos hneg
  have h4 := hδ o (h • o) x (h⁻¹ • o)
  rw [gromovProduct_comm (h • o) x] at h4
  have hmin : ρ ≤ min (gromovProduct x (h • o) o) (gromovProduct x (h⁻¹ • o) o) :=
    le_min hpos hneg
  linarith

/-- **A point deep in one shadow is transverse to the other end.** -/
theorem gromovProduct_le_of_mem_shadow {δ C : ℝ} (hδ : IsHyperbolicSpace δ X)
    {o z z' : X} (hturn : gromovProduct z z' o ≤ C) {ρ : ℝ} (hρ : C + δ < ρ)
    {x : X} (hx : x ∈ shadow o z ρ) : gromovProduct x z' o ≤ C + δ := by
  have hfar : gromovProduct z z' o + δ < gromovProduct x z o := by
    rw [mem_shadow] at hx
    linarith
  have hup := gromovProduct_le_add_delta_of_lt hδ hfar
  linarith

/-- **North--south dynamics along every nonzero power.**  With
`ρ = d(o,h·o) − (C+δ)`, a point transverse to both `h·o` and `h⁻¹·o` (Gromov
product at most `C + δ` with each) is sent by every nonzero power of `h` into
the shadow of `h·o` or of `h⁻¹·o`, according to the sign. -/
theorem zpow_smul_mem_shadows {δ C : ℝ} (hδ : IsHyperbolicSpace δ X)
    (hiso : IsIsometricAction G X) {h : G} {o : X}
    (hloc : gromovProduct (h • o) (h⁻¹ • o) o ≤ C)
    (hgap : 2 * (C + δ) < dist o (h • o)) {x : X}
    (hxpos : gromovProduct x (h • o) o ≤ C + δ)
    (hxneg : gromovProduct x (h⁻¹ • o) o ≤ C + δ) {n : ℤ} (hn : n ≠ 0) :
    (h ^ n) • x ∈ shadow o (h • o) (dist o (h • o) - (C + δ)) ∪
      shadow o (h⁻¹ • o) (dist o (h • o) - (C + δ)) := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · have hm : 1 ≤ m := by omega
    left
    rw [zpow_natCast, mem_shadow]
    exact (gromovProduct_pow_smul hδ hiso hloc hgap hxneg m hm).1
  · have hm : 1 ≤ m := by omega
    right
    have hloc' : gromovProduct (h⁻¹ • o) (h⁻¹⁻¹ • o) o ≤ C := by
      rw [gromovProduct_inv_turn]
      exact hloc
    have hgap' : 2 * (C + δ) < dist o (h⁻¹ • o) := by
      rw [dist_inv_smul hiso]
      exact hgap
    have hxneg' : gromovProduct x (h⁻¹⁻¹ • o) o ≤ C + δ := by
      rw [inv_inv]
      exact hxpos
    have hstep := (gromovProduct_pow_smul hδ hiso hloc' hgap' hxneg' m hm).1
    rw [zpow_neg, zpow_natCast, ← inv_pow, mem_shadow]
    rw [dist_inv_smul hiso] at hstep
    exact hstep

/-- **The shadows are swallowed by the powers that point into them.**  A point
of either shadow is transverse to the other end, so each nonzero power of `h`
sends the union of the two shadows into itself. -/
theorem zpow_smul_shadows_subset {δ C : ℝ} (hδ : IsHyperbolicSpace δ X)
    (hiso : IsIsometricAction G X) {h : G} {o : X}
    (hloc : gromovProduct (h • o) (h⁻¹ • o) o ≤ C)
    (hgap : 2 * (C + δ) < dist o (h • o)) {x : X}
    (hxtrans : gromovProduct x (h • o) o ≤ C + δ ∧
      gromovProduct x (h⁻¹ • o) o ≤ C + δ) {n : ℤ} (hn : n ≠ 0) :
    (h ^ n) • x ∈ shadow o (h • o) (dist o (h • o) - (C + δ)) ∪
      shadow o (h⁻¹ • o) (dist o (h • o) - (C + δ)) :=
  zpow_smul_mem_shadows hδ hiso hloc hgap hxtrans.1 hxtrans.2 hn

end PNaive
end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.PNaive.gromovProduct_smul_self_base
#audit_axioms GroupApproximation.GGT.PNaive.gromovProduct_pow_smul
#audit_axioms GroupApproximation.GGT.PNaive.disjoint_shadows
#audit_axioms GroupApproximation.GGT.PNaive.gromovProduct_le_of_mem_shadow
#audit_axioms GroupApproximation.GGT.PNaive.zpow_smul_mem_shadows
