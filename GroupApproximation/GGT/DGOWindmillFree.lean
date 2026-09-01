import GroupApproximation.GGT.DGOWindmillDef

/-!
# The windmill group acts freely on the apices outside the windmill

Eighth module of the campaign aimed at
`Manuscript.NonMF.TheoremCAssembly.dgoTheorem53` (DGO's Theorem 5.3(b)).

Dahmani-Guirardel-Osin note in passing, during the proof of their Proposition
5.12, that `G_W` *acts freely on `C₁`* "by Axiom 5 and Corollary 5.6", and use it
to make an equivariant choice of nearest points.  The campaign does not need the
equivariant choice --- `DGOWindmill.spokeSet` is defined by a membership
condition and is invariant automatically --- but it does need the freeness
itself, in two places, and this module proves it.

## Where it is spent

* **The word algebra.**  In a one-syllable spelling `g = p₁ b₁` the wrap-around
  seam reads `p₁ • d₁ ≠ d₁`.  Freeness is spent in the branch where that seam
  **fails**: `p₁` then fixes `d₁`, so `hfree` forces `p₁ = 1` and `g = b₁` lands
  in `Rot d₁`, which is the second of cyclic reduction's three shapes.  Without
  it that shape is unreachable and the failing seam has nowhere to go.  The case
  `p₁ ≠ 1`, where the seam holds and the element is cyclically reduced, is the
  contrapositive and needs no separate argument.  This is the one geometric fact
  the word-combinatorial layer takes as a hypothesis, and
  `eq_one_of_smul_eq_apex` below is stated in precisely the shape it binds.
* **The broken-path induction.**  `C₁` has to be `G_W`-invariant, because the
  developed apices of a word are `G_W`-translates of its directions and the
  corner lemma needs each of them to lie in the reference set of the next.
  `GGT/DGOWindmillPath.lean` spends the invariance twice per syllable.  The word
  algebra itself does *not* need it --- in its grouping a merge keeps the
  direction the left syllable already had, so no direction is ever moved --- so
  this clause is here for the geometry alone.

## The proof is two lines of case analysis, and both branches were already built

`IsWindmill.dichotomy` splits an element of `G_W` into a rotation at an apex
*inside* `W` or a loxodromic.  A loxodromic fixes nothing at all
(`ne_smul_of_isLoxodromic`).  A nontrivial rotation about `c ∈ W` fixes nothing
at distance `30δ` or more from `c` (`ne_smul_of_dist_ge`), and an apex `d`
*outside* `W` is at least `55δ` from every point of `W`, `c` included, by the
windmill's `far` clause.  So both branches force the element to be trivial.

That the second branch lands with `55δ` against a requirement of `30δ` is not
slack to be spent elsewhere: `55δ` is what `far` gives and `30δ` is the radius at
which the annulus of the very rotating condition has room on both sides.  The
campaign's real margin is the single `δ` in `DGOWindmill.dist_le_six_delta_of_reaching`.
-/

namespace GroupApproximation
namespace DGOWindmill

open GroupApproximation.HullGeometry
open GroupApproximation.HullSC

universe u v

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X]
  [MulAction G X]

/-! ## Freeness -/

/-- **An element of `G_W` fixing an apex outside `W` is trivial.**

DGO's "`G_W` acts freely on `C₁`", from their Axiom 5 and Corollary 5.6.  Here
the two branches are `IsWindmill.dichotomy` against `ne_smul_of_isLoxodromic` and
`ne_smul_of_dist_ge`; the windmill's `far` clause supplies the `55δ` that the
second needs at `30δ`. -/
theorem eq_one_of_smul_eq_of_isWindmill {δ : ℝ} (hδ : 0 < δ)
    (hhyp : IsHyperbolicSpace δ X) (hgeo : IsGeodesicSpace X) {C : Set X}
    {Rot : X → Subgroup G} (hfam : IsRotatingFamily G X C Rot)
    (hvr : IsVeryRotating G X δ C Rot) {W : Set X}
    (hW : IsWindmill G X δ C Rot W) {a : G}
    (ha : a ∈ windmillGroup C Rot W) {d : X} (hd : d ∈ C) (hdW : d ∉ W)
    (hfix : a • d = d) : a = 1 := by
  by_contra ha1
  rcases hW.dichotomy a ha with ⟨c, hc, hcW, hac⟩ | ⟨x, hlox⟩
  · have hfar : 55 * δ ≤ dist d c := hW.far d hd hdW c hcW
    have h30 : 30 * δ ≤ dist c d := by
      rw [dist_comm]
      linarith
    exact ne_smul_of_dist_ge hδ hhyp hgeo hfam hvr hc hac ha1 h30 hfix
  · exact ne_smul_of_isLoxodromic hfam.isometric hlox d hfix

/-- **The freeness fact in the shape the word-combinatorial layer binds.**

`GGT/DGOWindmillSpelling.lean` and the cyclic reduction above it take
`∀ a ∈ GW, ∀ d ∈ C₁, a • d = d → a = 1` as a bare hypothesis, so that they can be
stated over a `MulAction` with no metric in sight.  This is that hypothesis,
discharged, for any `C₁` consisting of apices outside the windmill --- which is
what the growth step's `C₁` is by construction. -/
theorem eq_one_of_smul_eq_apex {δ : ℝ} (hδ : 0 < δ)
    (hhyp : IsHyperbolicSpace δ X) (hgeo : IsGeodesicSpace X) {C : Set X}
    {Rot : X → Subgroup G} (hfam : IsRotatingFamily G X C Rot)
    (hvr : IsVeryRotating G X δ C Rot) {W : Set X}
    (hW : IsWindmill G X δ C Rot W) {C₁ : Set X}
    (hC₁ : ∀ d ∈ C₁, d ∈ C ∧ d ∉ W) :
    ∀ a ∈ windmillGroup C Rot W, ∀ d ∈ C₁, a • d = d → a = 1 := by
  intro a ha d hd hfix
  obtain ⟨hdC, hdW⟩ := hC₁ d hd
  exact eq_one_of_smul_eq_of_isWindmill hδ hhyp hgeo hfam hvr hW ha hdC hdW hfix

/-! ## Invariance of the new apices -/

/-- **`G_W` preserves the apices outside `W`.**  It preserves the apex set,
because the family is `G`-invariant, and it preserves `W` by the windmill's
third axiom, so it preserves the complement of `W` inside the apices --- the
inverse of an element of `G_W` is again in `G_W`, which is what rules out an
apex being carried *into* `W`. -/
theorem smul_mem_diff_of_isWindmill {δ : ℝ} {C : Set X} {Rot : X → Subgroup G}
    (hfam : IsRotatingFamily G X C Rot) {W : Set X}
    (hW : IsWindmill G X δ C Rot W) {a : G} (ha : a ∈ windmillGroup C Rot W)
    {d : X} (hd : d ∈ C) (hdW : d ∉ W) : a • d ∈ C ∧ a • d ∉ W := by
  refine ⟨hfam.apex_smul a hd, ?_⟩
  intro hmem
  apply hdW
  have hainv : a⁻¹ ∈ windmillGroup C Rot W := inv_mem ha
  have h := hW.invariant a⁻¹ hainv (a • d) hmem
  rwa [inv_smul_smul] at h

/-- **`G_W` preserves the apices within reach of `W`.**  The reach is measured by
a witness in `W` rather than by an infimum, so the invariance is the isometry of
the action applied to the witness: if `w` witnesses `d`, then `a · w` witnesses
`a · d`, and it lies in `W` because `G_W` preserves `W`.

This is the `G_W`-invariance of `C₁` that the growth step needs, stated for the
membership condition `C₁` is actually defined by. -/
theorem exists_mem_dist_le_smul_of_isWindmill {δ : ℝ} {C : Set X}
    {Rot : X → Subgroup G} (hfam : IsRotatingFamily G X C Rot) {W : Set X}
    (hW : IsWindmill G X δ C Rot W) {a : G} (ha : a ∈ windmillGroup C Rot W)
    {d : X} {M : ℝ} (hreach : ∃ w ∈ W, dist d w ≤ M) :
    ∃ w ∈ W, dist (a • d) w ≤ M := by
  obtain ⟨w, hwW, hdw⟩ := hreach
  refine ⟨a • w, hW.invariant a ha w hwW, ?_⟩
  rw [hfam.isometric a d w]
  exact hdw

end DGOWindmill
end GroupApproximation
