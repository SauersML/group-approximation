import GroupApproximation.GGT.DGOWindmillRotationFree

/-!
# The global very rotating condition

Fifth module of the campaign aimed at
`Manuscript.NonMF.TheoremCAssembly.dgoTheorem53` (DGO's Theorem 5.3(b)).

Dahmani-Guirardel-Osin, Lemma 5.5.  `HullSC.IsVeryRotating` is a statement about
points of the annulus `20δ ≤ d(·,c) ≤ 40δ`; everything the windmill induction
does happens at apices `ρ ≥ 200δ` apart, far outside it.  This module bridges
the two: if `q₁` and `q₂` sit at radius `30δ` on the way from `c` out to `x₁`
and `x₂` respectively, and `q₁` is within `7δ` of the rotate `h · q₂`, then
**every** geodesic from `x₁` to `x₂` passes through `c`.

## The coupling constant is `7δ`, and it is forced

DGO transfer their radius points onto the geodesic `[x₁,x₂]` at a cost of `δ`
each and can afford a hypothesis of `10δ`.  Under the four-point condition the
transfer is `DGOWindmill.dist_le_four_delta_of_between` and costs `4δ` each, so
the coupling the very rotating condition receives is `d + 8δ`.  Since
`HullSC.IsVeryRotating` admits `15δ`, the hypothesis here can be at most `7δ`.
The sharp-corner lemma downstream delivers `6δ`, so there is exactly `δ` of
slack in the campaign at this point and nowhere else; if a later estimate has to
be loosened, this is the constant that has to be re-derived first.

## Structure of the proof

* `exists_apex_of_subsegment` isolates all of the parametrisation work: given a
  geodesic `f` on `[0,D]` and two parameters `a ≤ b` whose points lie in the
  annulus and satisfy the coupling, the reversed restriction of `f` to `[a,b]`
  is a geodesic from `f b` to `f a`, so `HullSC.IsVeryRotating` applies to it and
  places `c` on `f`.  Nothing about rotating families is used except the
  condition itself.
* `exists_apex_mem_geodesic` is the lemma proper.  It bounds `(x₁|x₂)_c` by
  `11δ/2` -- the rotation pushes `q₁` and `q₂` `53δ` apart, so their Gromov
  product at `c` is at most `7δ/2`, and two applications of the four-point
  condition carry that out to `x₁` and `x₂` -- and then transfers the two radius
  points onto the geodesic and calls the helper.
* `between_of_veryRotating` is the corollary the induction actually consumes:
  `d(x₁,x₂) = d(x₁,c) + d(c,x₂)`.
-/

namespace GroupApproximation
namespace DGOWindmill

open GroupApproximation.HullGeometry
open GroupApproximation.HullSC

universe u v

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X]
  [MulAction G X]

/-! ## Reading the very rotating condition along a subsegment -/

/-- **The very rotating condition applied to a subsegment.**  If the points of a
geodesic `f` at two parameters `a ≤ b` lie in the annulus about `c` and are
coupled by a nontrivial rotation, then `c` is on `f`.

The reversed restriction `u ↦ f (b - u)` is a geodesic from `f b` to `f a` of
length `b - a = d(f b, f a)`, which is what `HullSC.IsVeryRotating` asks for;
the apex it produces sits at a parameter of the restriction, and `b - s` is the
corresponding parameter of `f`. -/
theorem exists_apex_of_subsegment {δ : ℝ} {C : Set X} {Rot : X → Subgroup G}
    (hvr : IsVeryRotating G X δ C Rot) {c : X} (hc : c ∈ C) {h : G}
    (hh : h ∈ Rot c) (hh1 : h ≠ 1) {D : ℝ} {f : ℝ → X}
    (hf : IsGeodesicSegment f 0 D) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hbD : b ≤ D)
    (hlow₁ : 20 * δ ≤ dist (f a) c) (hhigh₁ : dist (f a) c ≤ 40 * δ)
    (hlow₂ : 20 * δ ≤ dist (f b) c) (hhigh₂ : dist (f b) c ≤ 40 * δ)
    (hcoup : dist (h • f b) (f a) ≤ 15 * δ) :
    ∃ s ∈ Set.Icc (0 : ℝ) D, f s = c := by
  have hba : (0 : ℝ) ≤ b - a := by linarith
  have hlen : dist (f b) (f a) = b - a := by
    have hd := hf b ⟨le_trans ha hab, hbD⟩ a ⟨ha, le_trans hab hbD⟩
    rwa [abs_of_nonneg hba] at hd
  have hk : IsGeodesicSegment (fun u => f (b - u)) 0 (dist (f b) (f a)) := by
    rw [hlen]
    intro s hs u hu
    have hs' : b - s ∈ Set.Icc (0 : ℝ) D :=
      ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have hu' : b - u ∈ Set.Icc (0 : ℝ) D :=
      ⟨by linarith [hu.2], by linarith [hu.1]⟩
    have hd := hf (b - s) hs' (b - u) hu'
    have he : b - s - (b - u) = -(s - u) := by ring
    rw [he, abs_neg] at hd
    exact hd
  have hk0 : (fun u => f (b - u)) 0 = f b := by
    show f (b - 0) = f b
    rw [sub_zero]
  have hk1 : (fun u => f (b - u)) (dist (f b) (f a)) = f a := by
    rw [hlen]
    show f (b - (b - a)) = f a
    congr 1
    ring
  obtain ⟨s, hs, hks⟩ :=
    hvr c hc h hh hh1 (f b) (f a) hlow₂ hhigh₂ hlow₁ hhigh₁ hcoup
      (fun u => f (b - u)) hk hk0 hk1
  rw [hlen] at hs
  refine ⟨b - s, ⟨by linarith [hs.2], by linarith [hs.1]⟩, ?_⟩
  exact hks

/-! ## The lemma -/

/-- **DGO's Lemma 5.5, the global very rotating condition.**

`q₁` at radius `30δ` on the way from `c` to `x₁`, `q₂` at radius `30δ` on the
way from `c` to `x₂`, and `d(q₁, h · q₂) ≤ 7δ` for a nontrivial rotation `h`
about `c`.  Then every geodesic from `x₁` to `x₂` contains `c`.

The chain: the rotation moves `q₂` by exactly `60δ`, so `q₁` and `q₂` are at
least `53δ` apart and `(q₁|q₂)_c ≤ 7δ/2`; two applications of the four-point
condition carry that to `(x₁|x₂)_c ≤ 11δ/2`, which is what makes the parameters
`d(x₁,c) - 30δ` and `d(x₁,x₂) - (d(x₂,c) - 30δ)` land in the right order on the
geodesic and lets `dist_le_four_delta_of_between` place its points within `4δ`
of `q₁` and `q₂`.  The coupling handed to `HullSC.IsVeryRotating` is then
`4δ + 7δ + 4δ = 15δ` exactly. -/
theorem exists_apex_mem_geodesic {δ : ℝ} (hδ : 0 < δ)
    (hhyp : IsHyperbolicSpace δ X) (hgeo : IsGeodesicSpace X) {C : Set X}
    {Rot : X → Subgroup G} (hfam : IsRotatingFamily G X C Rot)
    (hvr : IsVeryRotating G X δ C Rot) {c : X} (hc : c ∈ C) {h : G}
    (hh : h ∈ Rot c) (hh1 : h ≠ 1) {x₁ x₂ q₁ q₂ : X}
    (hq₁ : Between c q₁ x₁) (hq₁r : dist c q₁ = 30 * δ)
    (hq₂ : Between c q₂ x₂) (hq₂r : dist c q₂ = 30 * δ)
    (hcoup : dist q₁ (h • q₂) ≤ 7 * δ)
    (f : ℝ → X) (hf : IsGeodesicSegment f 0 (dist x₁ x₂)) (hf0 : f 0 = x₁)
    (hf1 : f (dist x₁ x₂) = x₂) :
    ∃ s ∈ Set.Icc (0 : ℝ) (dist x₁ x₂), f s = c := by
  have hδ0 : (0 : ℝ) ≤ δ := le_of_lt hδ
  have hq₁c : dist q₁ c = 30 * δ := by rw [dist_comm]; exact hq₁r
  have hq₂c : dist q₂ c = 30 * δ := by rw [dist_comm]; exact hq₂r
  -- the rotation displaces `q₂` by exactly `60δ`
  have hlow₂ : 20 * δ ≤ dist q₂ c := by rw [hq₂c]; linarith
  have hhigh₂ : dist q₂ c ≤ 40 * δ := by rw [hq₂c]; linarith
  have hdisp : dist q₂ (h • q₂) = 2 * dist q₂ c :=
    dist_smul_eq_two_mul_of_veryRotating hgeo hfam hvr hc hh hh1 hlow₂ hhigh₂
  rw [hq₂c] at hdisp
  have hcomm : dist q₂ q₁ = dist q₁ q₂ := dist_comm q₂ q₁
  have htri2 : dist q₂ (h • q₂) ≤ dist q₂ q₁ + dist q₁ (h • q₂) :=
    dist_triangle _ _ _
  have hfar12 : 53 * δ ≤ dist q₁ q₂ := by linarith
  -- so their Gromov product at `c` is small, and so is that of `x₁` and `x₂`
  have hgp12 : gromovProduct q₁ q₂ c ≤ 7 * δ / 2 := by
    unfold gromovProduct
    rw [hq₁c, hq₂c]
    linarith
  have hgp1x : gromovProduct q₁ x₁ c = 30 * δ := by
    rw [gromovProduct_eq_of_between hq₁, hq₁r]
  have hgp2x : gromovProduct q₂ x₂ c = 30 * δ := by
    rw [gromovProduct_eq_of_between hq₂, hq₂r]
  have hx2q2 : gromovProduct x₂ q₂ c = 30 * δ := by
    rw [gromovProduct_comm x₂ q₂ c]; exact hgp2x
  have h2 := hhyp c q₁ x₂ q₂
  rw [hx2q2] at h2
  have hq1x2 : gromovProduct q₁ x₂ c ≤ 9 * δ / 2 := by
    have hm : min (gromovProduct q₁ x₂ c) (30 * δ) ≤ 9 * δ / 2 := by linarith
    rcases min_le_iff.mp hm with hl | hr
    · exact hl
    · linarith
  have h1 := hhyp c q₁ x₁ x₂
  rw [hgp1x] at h1
  have hx1x2 : gromovProduct x₁ x₂ c ≤ 11 * δ / 2 := by
    have hm : min (30 * δ) (gromovProduct x₁ x₂ c) ≤ 11 * δ / 2 := by linarith
    rcases min_le_iff.mp hm with hl | hr
    · linarith
    · exact hr
  -- the two radii, and the order of the corresponding parameters
  have hcx₁ : 30 * δ ≤ dist c x₁ := by rw [← hq₁r]; exact Between.dist_le_left hq₁
  have hcx₂ : 30 * δ ≤ dist c x₂ := by rw [← hq₂r]; exact Between.dist_le_left hq₂
  have hx₁c : dist x₁ c = dist c x₁ := dist_comm x₁ c
  have hx₂c : dist x₂ c = dist c x₂ := dist_comm x₂ c
  have hgpexp : gromovProduct x₁ x₂ c
      = (dist x₁ c + dist x₂ c - dist x₁ x₂) / 2 := rfl
  have hgpval : (dist x₁ c + dist x₂ c - dist x₁ x₂) / 2 ≤ 11 * δ / 2 := by
    rw [← hgpexp]; exact hx1x2
  have ht₁0 : (0 : ℝ) ≤ dist x₁ c - 30 * δ := by rw [hx₁c]; linarith
  have ht₂0 : (0 : ℝ) ≤ dist x₂ c - 30 * δ := by rw [hx₂c]; linarith
  have horder : dist x₁ c - 30 * δ
      ≤ dist x₁ x₂ - (dist x₂ c - 30 * δ) := by linarith
  have hmem₁ : dist x₁ c - 30 * δ ∈ Set.Icc (0 : ℝ) (dist x₁ x₂) :=
    ⟨ht₁0, by linarith⟩
  have hmem₂ : dist x₁ x₂ - (dist x₂ c - 30 * δ)
      ∈ Set.Icc (0 : ℝ) (dist x₁ x₂) := ⟨by linarith, by linarith⟩
  -- transfer `q₁` onto the geodesic, based at `x₁`
  obtain ⟨hd₁, hb₁⟩ := between_of_mem_geodesic hf hf0 hf1 hmem₁
  have hq₁sym : Between x₁ q₁ c := Between.symm hq₁
  have hd₁' : dist x₁ q₁ = dist x₁ c - 30 * δ := by
    have hb := hq₁sym
    unfold Between at hb
    linarith
  have hgpcx₂ : gromovProduct c x₂ x₁
      = dist x₁ c - gromovProduct x₁ x₂ c := by
    unfold gromovProduct
    rw [dist_comm c x₁, dist_comm x₂ x₁, dist_comm c x₂]
    ring
  have hcmp₁ : dist x₁ c - 30 * δ ≤ gromovProduct c x₂ x₁ := by
    rw [hgpcx₂]; linarith
  have hnear₁ : dist q₁ (f (dist x₁ c - 30 * δ)) ≤ 4 * δ :=
    dist_le_four_delta_of_between hhyp hδ0 hq₁sym hd₁' hb₁ hd₁ hcmp₁
  -- transfer `q₂` onto the geodesic, based at `x₂`
  obtain ⟨hd₂a, hb₂a⟩ := between_of_mem_geodesic hf hf0 hf1 hmem₂
  have hb₂ : Between x₂ (f (dist x₁ x₂ - (dist x₂ c - 30 * δ))) x₁ := Between.symm hb₂a
  have hd₂ : dist x₂ (f (dist x₁ x₂ - (dist x₂ c - 30 * δ)))
      = dist x₂ c - 30 * δ := by
    have hfar := Between.dist_far hb₂a
    rw [hd₂a] at hfar
    rw [dist_comm x₂ (f (dist x₁ x₂ - (dist x₂ c - 30 * δ)))]
    linarith
  have hq₂sym : Between x₂ q₂ c := Between.symm hq₂
  have hd₂' : dist x₂ q₂ = dist x₂ c - 30 * δ := by
    have hb := hq₂sym
    unfold Between at hb
    linarith
  have hgpcx₁ : gromovProduct c x₁ x₂
      = dist x₂ c - gromovProduct x₁ x₂ c := by
    unfold gromovProduct
    rw [dist_comm c x₂, dist_comm c x₁]
    ring
  have hcmp₂ : dist x₂ c - 30 * δ ≤ gromovProduct c x₁ x₂ := by
    rw [hgpcx₁]; linarith
  have hnear₂ : dist q₂ (f (dist x₁ x₂ - (dist x₂ c - 30 * δ))) ≤ 4 * δ :=
    dist_le_four_delta_of_between hhyp hδ0 hq₂sym hd₂' hb₂ hd₂ hcmp₂
  -- the annulus bounds and the coupling on the geodesic
  have hann₁ : 20 * δ ≤ dist (f (dist x₁ c - 30 * δ)) c
      ∧ dist (f (dist x₁ c - 30 * δ)) c ≤ 40 * δ := by
    have hA := dist_triangle (f (dist x₁ c - 30 * δ)) q₁ c
    have hB := dist_triangle q₁ (f (dist x₁ c - 30 * δ)) c
    have hcm : dist (f (dist x₁ c - 30 * δ)) q₁
        = dist q₁ (f (dist x₁ c - 30 * δ)) := dist_comm _ _
    constructor <;> linarith
  have hann₂ : 20 * δ ≤ dist (f (dist x₁ x₂ - (dist x₂ c - 30 * δ))) c
      ∧ dist (f (dist x₁ x₂ - (dist x₂ c - 30 * δ))) c ≤ 40 * δ := by
    have hA := dist_triangle (f (dist x₁ x₂ - (dist x₂ c - 30 * δ))) q₂ c
    have hB := dist_triangle q₂ (f (dist x₁ x₂ - (dist x₂ c - 30 * δ))) c
    have hcm : dist (f (dist x₁ x₂ - (dist x₂ c - 30 * δ))) q₂
        = dist q₂ (f (dist x₁ x₂ - (dist x₂ c - 30 * δ))) := dist_comm _ _
    constructor <;> linarith
  have hiso := hfam.isometric h (f (dist x₁ x₂ - (dist x₂ c - 30 * δ))) q₂
  have hcoup' : dist (h • f (dist x₁ x₂ - (dist x₂ c - 30 * δ)))
      (f (dist x₁ c - 30 * δ)) ≤ 15 * δ := by
    have hA := dist_triangle (h • f (dist x₁ x₂ - (dist x₂ c - 30 * δ)))
      (h • q₂) (f (dist x₁ c - 30 * δ))
    have hB := dist_triangle (h • q₂) q₁ (f (dist x₁ c - 30 * δ))
    have hC : dist (h • q₂) q₁ = dist q₁ (h • q₂) := dist_comm _ _
    have hD : dist (f (dist x₁ x₂ - (dist x₂ c - 30 * δ))) q₂
        = dist q₂ (f (dist x₁ x₂ - (dist x₂ c - 30 * δ))) := dist_comm _ _
    linarith
  exact exists_apex_of_subsegment hvr hc hh hh1 hf ht₁0 horder hmem₂.2
    hann₁.1 hann₁.2 hann₂.1 hann₂.2 hcoup'

/-- **The form the induction consumes**: under the hypotheses of
`exists_apex_mem_geodesic`, the apex `c` is metrically between `x₁` and `x₂`.

Betweenness rather than "lies on every geodesic" is what the broken-path
induction propagates; a geodesic is reconstructed through `c` only where a
genuine triangle is needed. -/
theorem between_of_veryRotating {δ : ℝ} (hδ : 0 < δ)
    (hhyp : IsHyperbolicSpace δ X) (hgeo : IsGeodesicSpace X) {C : Set X}
    {Rot : X → Subgroup G} (hfam : IsRotatingFamily G X C Rot)
    (hvr : IsVeryRotating G X δ C Rot) {c : X} (hc : c ∈ C) {h : G}
    (hh : h ∈ Rot c) (hh1 : h ≠ 1) {x₁ x₂ q₁ q₂ : X}
    (hq₁ : Between c q₁ x₁) (hq₁r : dist c q₁ = 30 * δ)
    (hq₂ : Between c q₂ x₂) (hq₂r : dist c q₂ = 30 * δ)
    (hcoup : dist q₁ (h • q₂) ≤ 7 * δ) : Between x₁ c x₂ := by
  obtain ⟨f, hf, hf0, hf1⟩ := hgeo x₁ x₂
  obtain ⟨s, hs, hfs⟩ := exists_apex_mem_geodesic hδ hhyp hgeo hfam hvr hc hh
    hh1 hq₁ hq₁r hq₂ hq₂r hcoup f hf hf0 hf1
  obtain ⟨-, hb⟩ := between_of_mem_geodesic hf hf0 hf1 hs
  rwa [hfs] at hb

end DGOWindmill
end GroupApproximation
