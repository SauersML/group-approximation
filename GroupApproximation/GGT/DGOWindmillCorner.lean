import GroupApproximation.GGT.DGOWindmillGlobalVR
import GroupApproximation.GGT.DGOWindmillQuasiconvex

/-!
# The sharp corner

Sixth module of the campaign aimed at
`Manuscript.NonMF.TheoremCDebts.dgoTheorem53` (DGO's Theorem 5.3(b)).

Dahmani-Guirardel-Osin, Lemma 5.15.  This is the step where the windmill earns
its keep.  `DGOWindmill.between_of_veryRotating` turns a *coupling* between the
two radius-`30δ` points into "the apex is between the two far points", but it
does not say where a coupling comes from: two apices near `c` can be seen in
completely different directions.  The windmill supplies the missing input --- a
quasiconvex set `S`, far from `c`, that both directions have to reach --- and
then the two geodesics leaving `c` cannot separate before radius `30δ`, because
if they did, the geodesic joining their targets would come within `45δ` of `c`
while every point of `S` is `55δ` away.

## The abstract reference set

The lemma is stated for an arbitrary `S` with two properties: it is
`12δ`-quasiconvex, and every one of its points is at least `55δ` from `c`.  DGO
take `S = W ∪ ⋃_{c' ∈ C₁ \ {c}} [c', c̄']`, the windmill together with the
segments joining the *other* new apices to it, and check both properties by hand.
Keeping `S` abstract here means the growth step can choose it, and it keeps this
module independent of the construction of `W₁`.

The two constants are exactly what the argument spends: a point of a geodesic
between two points of `S` is at least `55δ - 12δ = 43δ` from `c`, the
radius-`30δ` point is `30δ` from `c`, and `3δ` of triangle thinness cannot bridge
`13δ`.  So the thin-triangle alternative "the radius point is near the far side"
is impossible, the radius point is near the *other* geodesic from `c`, and the
two radius points are within `3δ + 3δ = 6δ`.  That clears the `7δ` that
`between_of_veryRotating` demands, with `δ` to spare --- the only slack in the
campaign.

## What is proved

* `between_of_corner` --- the lemma.  Note the shape of the conclusion:
  `Between x c (h · y)`, the apex lying between the incoming point and the
  *rotated* outgoing point.  That is what makes the broken path of the induction
  turn a corner at `c`.
* `between_of_corner_of_between` --- the extension DGO make at the end of their
  proof of 5.15, for a point `x'` lying between `c` and `x`: the corner is still
  sharp at `x'`.  It is needed because the induction's starting point may sit on
  one of the segments `[c, c̄]` rather than in `W` itself, and it is four uses of
  the triangle inequality rather than a repetition of the argument.
-/

namespace GroupApproximation
namespace DGOWindmill

open GroupApproximation.HullGeometry
open GroupApproximation.HullSC

universe u v

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X]
  [MulAction G X]

/-! ## Two directions reaching a far quasiconvex set cannot separate early -/

/-- **The two radius-`30δ` points are `6δ` apart.**

`z` and `z'` lie in a `12δ`-quasiconvex set every point of which is at least
`55δ` from `c`.  On the triangle `(c, z, z')`, the point of `[c,z]` at radius
`30δ` is `3δ`-close to `[c,z']` or to `[z',z]`; the second is impossible,
because `[z',z]` stays within `12δ` of `S` and hence at least `43δ` from `c`,
while the radius point is at `30δ`.  So it is `3δ`-close to a point of `[c,z']`,
whose radius is therefore within `3δ` of `30δ`, and the radius-`30δ` point of
`[c,z']` is another `3δ` away. -/
theorem dist_le_six_delta_of_reaching {δ : ℝ} (hδ : 0 < δ)
    (hhyp : IsHyperbolicSpace δ X) (hgeo : IsGeodesicSpace X) {S : Set X}
    (hSqc : IsQuasiconvexSet S (12 * δ)) {c : X}
    (hSfar : ∀ s ∈ S, 55 * δ ≤ dist c s) {z z' : X} (hz : z ∈ S) (hz' : z' ∈ S)
    {α β : ℝ → X} (hα : IsGeodesicSegment α 0 (dist c z)) (hα0 : α 0 = c)
    (hα1 : α (dist c z) = z) (hβ : IsGeodesicSegment β 0 (dist c z'))
    (hβ0 : β 0 = c) (hβ1 : β (dist c z') = z') :
    dist (α (30 * δ)) (β (30 * δ)) ≤ 6 * δ := by
  have hδ0 : (0 : ℝ) ≤ δ := le_of_lt hδ
  have hcz : 55 * δ ≤ dist c z := hSfar z hz
  have hcz' : 55 * δ ≤ dist c z' := hSfar z' hz'
  have hmemz : 30 * δ ∈ Set.Icc (0 : ℝ) (dist c z) := ⟨by linarith, by linarith⟩
  have hmemz' : 30 * δ ∈ Set.Icc (0 : ℝ) (dist c z') :=
    ⟨by linarith, by linarith⟩
  obtain ⟨hrα, -⟩ := between_of_mem_geodesic hα hα0 hα1 hmemz
  obtain ⟨hrβ, -⟩ := between_of_mem_geodesic hβ hβ0 hβ1 hmemz'
  obtain ⟨γ, hγ, hγ0, hγ1⟩ := hgeo z' z
  rcases exists_close_on_other_side_of_geodesic_triangle hhyp hδ0 hα hα0 hα1
      hβ hβ0 hβ1 hγ hγ0 hγ1 hmemz with ⟨s, hs, hclose⟩ | ⟨s, hs, hclose⟩
  · -- the radius point is close to the other geodesic from `c`
    obtain ⟨hrs, -⟩ := between_of_mem_geodesic hβ hβ0 hβ1 hs
    have hA : dist c (β s) ≤ dist c (α (30 * δ)) + dist (α (30 * δ)) (β s) :=
      dist_triangle _ _ _
    have hB : dist c (α (30 * δ)) ≤ dist c (β s) + dist (β s) (α (30 * δ)) :=
      dist_triangle _ _ _
    have hcm : dist (β s) (α (30 * δ)) = dist (α (30 * δ)) (β s) :=
      dist_comm _ _
    have hsclose : |s - 30 * δ| ≤ 3 * δ := by
      refine abs_le.mpr ⟨?_, ?_⟩
      · rw [hrs, hrα] at hB; linarith
      · rw [hrs, hrα] at hA; linarith
    have hpar : dist (β s) (β (30 * δ)) = |s - 30 * δ| := hβ s hs (30 * δ) hmemz'
    have htri := dist_triangle (α (30 * δ)) (β s) (β (30 * δ))
    rw [hpar] at htri
    linarith
  · -- the radius point is close to the far side, which is impossible
    exfalso
    obtain ⟨q, hqS, hqd⟩ := hSqc z' hz' z hz γ hγ hγ0 hγ1 s hs
    have hfar := hSfar q hqS
    have h1 : dist c q ≤ dist c (α (30 * δ)) + dist (α (30 * δ)) q :=
      dist_triangle _ _ _
    have h2 : dist (α (30 * δ)) q ≤ dist (α (30 * δ)) (γ s) + dist (γ s) q :=
      dist_triangle _ _ _
    linarith

/-! ## The corner -/

/-- **DGO's Lemma 5.15, the sharp corner.**

`c` is an apex, `h` a nontrivial rotation about it, and `x` and `y` are two
points reached from `c` through the far quasiconvex set `S` -- `z` between `c`
and `x`, `z'` between `c` and `y`, both in `S`.  Then `c` lies between `x` and
`h · y`.

The proof is `dist_le_six_delta_of_reaching` followed by
`between_of_veryRotating` at the rotation `h⁻¹`: the radius-`30δ` point on the
way to `h · y` is `h` applied to the one on the way to `y`, and `h⁻¹` carries it
back to within `6δ` of the incoming radius point, which is the coupling the
global very rotating condition wants. -/
theorem between_of_corner {δ : ℝ} (hδ : 0 < δ) (hhyp : IsHyperbolicSpace δ X)
    (hgeo : IsGeodesicSpace X) {C : Set X} {Rot : X → Subgroup G}
    (hfam : IsRotatingFamily G X C Rot) (hvr : IsVeryRotating G X δ C Rot)
    {c : X} (hc : c ∈ C) {h : G} (hh : h ∈ Rot c) (hh1 : h ≠ 1) {S : Set X}
    (hSqc : IsQuasiconvexSet S (12 * δ)) (hSfar : ∀ s ∈ S, 55 * δ ≤ dist c s)
    {x y z z' : X} (hz : z ∈ S) (hzb : Between c z x) (hz' : z' ∈ S)
    (hz'b : Between c z' y) : Between x c (h • y) := by
  have hδ0 : (0 : ℝ) ≤ δ := le_of_lt hδ
  have hcz : 55 * δ ≤ dist c z := hSfar z hz
  have hcz' : 55 * δ ≤ dist c z' := hSfar z' hz'
  obtain ⟨α, hα, hα0, hα1⟩ := hgeo c z
  obtain ⟨β, hβ, hβ0, hβ1⟩ := hgeo c z'
  have hmemz : 30 * δ ∈ Set.Icc (0 : ℝ) (dist c z) := ⟨by linarith, by linarith⟩
  have hmemz' : 30 * δ ∈ Set.Icc (0 : ℝ) (dist c z') :=
    ⟨by linarith, by linarith⟩
  obtain ⟨hrα, hbα⟩ := between_of_mem_geodesic hα hα0 hα1 hmemz
  obtain ⟨hrβ, hbβ⟩ := between_of_mem_geodesic hβ hβ0 hβ1 hmemz'
  -- the two radius points, transported to the far endpoints
  have hq₁ : Between c (α (30 * δ)) x := Between.trans_left hzb hbα
  have hq₂ : Between c (β (30 * δ)) y := Between.trans_left hz'b hbβ
  have hq₂' : Between c (h • β (30 * δ)) (h • y) :=
    smul_between_of_mem_rot hfam hc hh hq₂
  have hr₂' : dist c (h • β (30 * δ)) = 30 * δ := by
    have hfix : h • c = c := hfam.rot_fix hc h hh
    calc dist c (h • β (30 * δ)) = dist (h • c) (h • β (30 * δ)) := by rw [hfix]
      _ = dist c (β (30 * δ)) := hfam.isometric h c (β (30 * δ))
      _ = 30 * δ := hrβ
  -- the coupling, at the inverse rotation
  have hsix := dist_le_six_delta_of_reaching hδ hhyp hgeo hSqc hSfar hz hz' hα
    hα0 hα1 hβ hβ0 hβ1
  have hinv : h⁻¹ • (h • β (30 * δ)) = β (30 * δ) := inv_smul_smul h _
  have hcoup : dist (α (30 * δ)) (h⁻¹ • (h • β (30 * δ))) ≤ 7 * δ := by
    rw [hinv]
    linarith
  exact between_of_veryRotating hδ hhyp hgeo hfam hvr hc (inv_mem hh)
    (inv_ne_one.mpr hh1) hq₁ hrα hq₂' hr₂' hcoup

/-- **The corner survives moving the incoming point inwards** (the last paragraph
of DGO's proof of Lemma 5.15).

If `c` is between `x` and `w`, and `x'` lies between `c` and `x`, then `c` is
between `x'` and `w`.  The induction needs this because its starting point may
lie on one of the segments joining a new apex to the windmill rather than in the
windmill itself, and for such a point the corner lemma is applied at the
segment's other end.

Four uses of the triangle inequality; no geometry. -/
theorem between_of_corner_of_between {x x' c w : X} (hxc : Between x c w)
    (hx' : Between c x' x) : Between x' c w := by
  unfold Between at hxc hx' ⊢
  have h1 : dist x w ≤ dist x x' + dist x' w := dist_triangle x x' w
  have h2 : dist x' w ≤ dist x' c + dist c w := dist_triangle x' c w
  have hxx' : dist x x' = dist x' x := dist_comm x x'
  have hxc' : dist x c = dist c x := dist_comm x c
  have hcx' : dist c x' = dist x' c := dist_comm c x'
  linarith

/-- **The corner also survives moving the outgoing point inwards.**

Together with `between_of_corner_of_between`, this peels both boundary pieces
of a reduced windmill word: an endpoint on the excluded spoke is moved out to
its foot in the reference set for the corner argument, then moved back in by
this metric prefix calculation. -/
theorem between_of_corner_of_between_right {x c w' w : X}
    (hxc : Between x c w) (hw' : Between c w' w) : Between x c w' := by
  unfold Between at hxc hw' ⊢
  have h1 : dist x w' ≤ dist x c + dist c w' := dist_triangle x c w'
  have h2 : dist x w ≤ dist x w' + dist w' w := dist_triangle x w' w
  linarith

end DGOWindmill
end GroupApproximation
