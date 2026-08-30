import GroupApproximation.GGT.HullSCRotatingFamily
import GroupApproximation.GGT.DGOWindmillBetween

/-!
# A rotation moves everything far from its apex

Third module of the windmill campaign aimed at
`Manuscript.NonMF.TheoremCDebts.dgoTheorem53` (DGO's Theorem 5.3(b)).

`GGT/HullSCRotatingFamily.lean` proves `ne_of_veryRotating`: a nontrivial
rotation about `c` fixes no point of the annulus `20δ ≤ d(·,c) ≤ 40δ`.  That is
the annulus the very rotating condition is stated on, and it is not where the
windmill argument needs the fact.  DGO use the corresponding statement for
points at distance at least `ρ ≥ 200δ` -- it is their Corollary 5.6, from which
they conclude that `G_W` acts freely on the apices `C₁` and that an equivariant
choice of nearest points can be made.

The upgrade is one application of the comparison lemma
`DGOWindmill.dist_le_four_delta_of_between_same`: a fixed point `z` at distance
at least `30δ` from `c` gives two geodesics `[c,z]` and `g·[c,z]` with the same
endpoints, so their radius-`30δ` points are `4δ` apart, while the very rotating
condition puts them `60δ` apart.

## What is proved

* `smul_between_of_mem_rot` -- a rotation about `c` carries betweenness from `c`
  to betweenness from `c`.  The action is isometric and fixes `c`, so this is
  the definition transported; recorded because it is used at every corner.
* `ne_smul_of_dist_ge` -- **a nontrivial rotation about `c` moves every point at
  distance at least `30δ` from `c`**.  DGO's Corollary 5.6, with `30δ` in place
  of their `20δ` because the comparison costs `4δ` here rather than `δ`.
* `ne_smul_of_translation_lower_bound` -- an element with a linear lower bound on
  its orbit displacement fixes nothing.  This is the loxodromic branch of the
  windmill's fifth axiom in the form the campaign states it, and it is what
  rules out an elliptic element of `G_W` fixing a new apex.

Both fixed-point lemmas are consumed by the freeness argument that makes a
one-syllable spelling cyclically reduced; see the campaign plan.
-/

namespace GroupApproximation
namespace DGOWindmill

open GroupApproximation.HullGeometry
open GroupApproximation.HullSC

universe u v

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X]
  [MulAction G X]

/-! ## Rotations transport betweenness -/

/-- **A rotation about `c` preserves betweenness from `c`.**  It fixes `c` and
acts by isometries, so it carries a geodesic from `c` to `x` to a geodesic from
`c` to `g · x`. -/
theorem smul_between_of_mem_rot {C : Set X} {Rot : X → Subgroup G}
    (hfam : IsRotatingFamily G X C Rot) {c : X} (hc : c ∈ C) {g : G}
    (hg : g ∈ Rot c) {p x : X} (h : Between c p x) :
    Between c (g • p) (g • x) := by
  have hfix : g • c = c := hfam.rot_fix hc g hg
  unfold Between at h ⊢
  have e1 : dist c (g • x) = dist c x := by
    calc dist c (g • x) = dist (g • c) (g • x) := by rw [hfix]
      _ = dist c x := hfam.isometric g c x
  have e2 : dist c (g • p) = dist c p := by
    calc dist c (g • p) = dist (g • c) (g • p) := by rw [hfix]
      _ = dist c p := hfam.isometric g c p
  have e3 : dist (g • p) (g • x) = dist p x := hfam.isometric g p x
  rw [e1, e2, e3]
  exact h

/-! ## A nontrivial rotation has no far fixed point -/

/-- **A nontrivial rotation about `c` moves every point at distance at least
`30δ` from `c`.**

DGO's Corollary 5.6.  Suppose `g · z = z` with `d(c,z) ≥ 30δ`, and let `p` be
the point at distance `30δ` from `c` between `c` and `z`.  Then `g · p` is also
at distance `30δ` from `c` and lies between `c` and `g · z = z`, so
`dist p (g · p) ≤ 4δ` by the comparison lemma -- while
`HullSC.dist_smul_eq_two_mul_of_veryRotating` puts it at exactly `60δ`, `p`
being in the annulus.  With `δ > 0` that is a contradiction.

The constant is `30δ` and not DGO's `20δ` because the comparison of two
geodesics leaving `c` costs `4δ` under the four-point condition where a tripod
costs `δ`; `30δ` is the radius at which the annulus `[20δ, 40δ]` has `10δ` of
room on both sides, which is what the transfers downstream also want. -/
theorem ne_smul_of_dist_ge {δ : ℝ} (hδ : 0 < δ) (hhyp : IsHyperbolicSpace δ X)
    (hgeo : IsGeodesicSpace X) {C : Set X} {Rot : X → Subgroup G}
    (hfam : IsRotatingFamily G X C Rot) (hvr : IsVeryRotating G X δ C Rot)
    {c : X} (hc : c ∈ C) {g : G} (hg : g ∈ Rot c) (hg1 : g ≠ 1) {z : X}
    (hz : 30 * δ ≤ dist c z) : g • z ≠ z := by
  intro hfix
  have hr0 : (0 : ℝ) ≤ 30 * δ := by linarith
  obtain ⟨p, hpr, hp⟩ := exists_between_dist_eq hgeo c z hr0 hz
  have hgp : Between c (g • p) z := by
    have h := smul_between_of_mem_rot hfam hc hg hp
    rwa [hfix] at h
  have hgpr : dist c (g • p) = 30 * δ := by
    have hfixc : g • c = c := hfam.rot_fix hc g hg
    calc dist c (g • p) = dist (g • c) (g • p) := by rw [hfixc]
      _ = dist c p := hfam.isometric g c p
      _ = 30 * δ := hpr
  have hclose : dist p (g • p) ≤ 4 * δ :=
    dist_le_four_delta_of_between_same hhyp (le_of_lt hδ) hp hpr hgp hgpr
  have hpc : dist p c = 30 * δ := by rw [dist_comm]; exact hpr
  have hlow : 20 * δ ≤ dist p c := by rw [hpc]; linarith
  have hhigh : dist p c ≤ 40 * δ := by rw [hpc]; linarith
  have hfar : dist p (g • p) = 2 * dist p c :=
    dist_smul_eq_two_mul_of_veryRotating hgeo hfam hvr hc hg hg1 hlow hhigh
  rw [hpc] at hfar
  linarith

/-! ## An element with linear displacement has no fixed point -/

/-- **Linear orbit growth forbids a fixed point.**  If `d(x₀, gⁿ · x₀) ≥ ρ n`
for every `n` with `ρ > 0`, then `g` fixes no point at all: a fixed point `z`
would bound the whole orbit by `2 d(x₀, z)`.

This is the loxodromic branch of the windmill's fifth axiom in the shape the
campaign records it -- a translation-length bound at one basepoint rather than
an invariant geodesic line -- and this lemma is why that shape suffices.  It is
used to rule out an elliptic element of `G_W` fixing an apex of `C₁`, which is
what makes a one-syllable spelling cyclically reduced. -/
theorem ne_smul_of_translation_lower_bound (hiso : IsIsometricAction G X)
    {g : G} {x₀ : X} {ρ : ℝ} (hρ : 0 < ρ)
    (h : ∀ n : ℕ, ρ * n ≤ dist x₀ ((g ^ n) • x₀)) (z : X) : g • z ≠ z := by
  intro hfix
  have hpow : ∀ n : ℕ, (g ^ n) • z = z := by
    intro n
    induction n with
    | zero => rw [pow_zero, one_smul]
    | succ k ih => rw [pow_succ, mul_smul, hfix, ih]
  obtain ⟨n, hn⟩ := exists_nat_gt ((2 * dist x₀ z) / ρ)
  have hlt : 2 * dist x₀ z < ρ * n := by
    rw [div_lt_iff₀ hρ] at hn
    linarith
  have h2 : dist z ((g ^ n) • x₀) = dist x₀ z := by
    have hiso' := hiso (g ^ n) z x₀
    rw [hpow n] at hiso'
    rw [hiso', dist_comm]
  have h1 := dist_triangle x₀ z ((g ^ n) • x₀)
  have h3 := h n
  linarith

end DGOWindmill
end GroupApproximation
