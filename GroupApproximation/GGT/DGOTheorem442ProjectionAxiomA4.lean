import GroupApproximation.GGT.DGOTheorem442ProjectionAxiomA3

/-!
# DGO Theorem 4.42: projection axiom (A4)

For two distinct coset-orbit vertices `A` and `B`, projection axiom (A4)
asserts that only finitely many vertices `Y` have large projection distance
`dᵖ_Y(A,B)`.

The last sentence of the printed proof of DGO Lemma 4.47 says that a compact
geodesic segment has only finitely many subsegments.  Taken literally, that
sentence is false.  The argument only needs a finite *coarse* set of
subsegments.  We implement that missing step: the parameter interval of the
fixed geodesic is covered by finitely many balls of radius `δ / 2`, and a
shadowing subsegment is assigned the ordered pair of balls containing its two
endpoints.  Two shadows with the same assignment have corresponding points
at distance at most `26δ`.  Geometric separation therefore says that their
coset-orbit vertices coincide.

The constants otherwise follow Lemma 4.47 verbatim:

* `ε = 26δ + 2σ`;
* `c = max {R(ε) + 2σ, 30δ + σ}`;
* `ξ = 6000c + 2ν + 1`.

The repository's polygon lemma supplies `12δ`-close endpoints.  Its two
units of slack relative to the source's `13δ` bound pay exactly for the
finite discretisation above, so the source's `26δ` separation radius is
unchanged.
-/

namespace GroupApproximation
namespace GGT
namespace Elementary

open GroupApproximation.HullGeometry
open GroupApproximation.DGOWindmill

universe u v

variable {G : Type u} [Group G] {S : Type v} [PseudoMetricSpace S]
  [MulAction G S]

/-- A shadow of a long geodesic in the coset orbit `Y` on one fixed geodesic
segment.  The two ordered parameters on the fixed side are the data which
will be discretised in the finite-grid argument. -/
structure FixedSideShadow
    (H : Subgroup G) (s : S) (Y : G ⧸ H) (b a : S)
    (fixed : ℝ → S) (c D : ℝ) where
  y₀ : S
  y₁ : S
  hy₀ : y₀ ∈ cosetOrbitAt H s Y
  hy₁ : y₁ ∈ cosetOrbitAt H s Y
  path : ℝ → S
  path_geodesic : IsGeodesicSegment path 0 (dist y₀ y₁)
  path_zero : path 0 = y₀
  path_dist : path (dist y₀ y₁) = y₁
  u : ℝ
  u' : ℝ
  hu : u ∈ Set.Icc (0 : ℝ) (dist y₀ y₁)
  hu' : u' ∈ Set.Icc (0 : ℝ) (dist y₀ y₁)
  t : ℝ
  t' : ℝ
  ht : t ∈ Set.Icc (0 : ℝ) (dist b a)
  ht' : t' ∈ Set.Icc (0 : ℝ) (dist b a)
  long : c ≤ |u' - u|
  close : dist (path u) (fixed t) ≤ D
  close' : dist (path u') (fixed t') ≤ D

/-- A selected point in each of the two projection sets controls the diameter
of their union up to the two uniform within-projection errors. -/
theorem approxCosetProjectionDistance_le_two_mul_add_dist
    {H : Subgroup G} {s : S} {κ ν : ℝ} {ν₀ : 0 ≤ ν}
    {Y A B : G ⧸ H} (hYA : Y ≠ A) (hYB : Y ≠ B)
    (hν : ∀ (Z W : G ⧸ H), Z ≠ W →
      ∀ x ∈ approxCosetProjectionSet H s κ Z W,
        ∀ y ∈ approxCosetProjectionSet H s κ Z W, dist x y ≤ ν)
    {x y : S} (hx : x ∈ approxCosetProjectionSet H s κ Y A)
    (hy : y ∈ approxCosetProjectionSet H s κ Y B) :
    approxCosetProjectionDistance H s κ Y A B ≤ 2 * ν + dist x y := by
  apply Metric.diam_le_of_forall_dist_le
  · positivity
  · intro p hp q hq
    change p ∈ approxCosetProjectionPairSet H s κ Y A B at hp
    change q ∈ approxCosetProjectionPairSet H s κ Y A B at hq
    rcases hp with hpA | hpB
    · rcases hq with hqA | hqB
      · have hpq := hν Y A hYA p hpA q hqA
        linarith [ν₀, dist_nonneg (x := x) (y := y)]
      · have hpx := hν Y A hYA p hpA x hx
        have hyq := hν Y B hYB y hy q hqB
        have htri := dist_triangle4 p x y q
        linarith
    · rcases hq with hqA | hqB
      · have hpy := hν Y B hYB p hpB y hy
        have hxq := hν Y A hYA x hx q hqA
        have htri := dist_triangle4 p y x q
        rw [dist_comm y x] at htri
        linarith
      · have hpq := hν Y B hYB p hpB q hqB
        linarith [ν₀, dist_nonneg (x := x) (y := y)]

/-- The hexagon part of DGO's (A4) proof, with the two points on `A` and the
two points on `B` chosen equal.  Thus the only non-transverse side that can
carry the long close segment is the fixed geodesic from `b` to `a`. -/
theorem nonempty_fixedSideShadow_of_large_projection
    {δ σ ν ξ c : ℝ}
    (hδ : IsHyperbolicSpace δ S) (hδ0 : 0 ≤ δ) (hδpos : 0 < δ)
    (hgeo : IsGeodesicSpace S) (hiso : IsIsometricAction G S)
    {H : Subgroup G} {s : S}
    (hquasi : ∀ (p q : G), p ∈ H → q ∈ H →
      ∀ f : ℝ → S, IsGeodesicSegment f 0 (dist (p • s) (q • s)) →
        f 0 = p • s → f (dist (p • s) (q • s)) = q • s →
          ∀ t ∈ Set.Icc (0 : ℝ) (dist (p • s) (q • s)),
            ∃ z : G, z ∈ H ∧ dist (f t) (z • s) ≤ σ)
    (hcδ : 30 * δ ≤ c)
    (htransverse : 12 * δ + σ + δ < c)
    (hν0 : 0 ≤ ν)
    (hν : ∀ (Z W : G ⧸ H), Z ≠ W →
      ∀ x ∈ approxCosetProjectionSet H s δ Z W,
        ∀ y ∈ approxCosetProjectionSet H s δ Z W, dist x y ≤ ν)
    (hξ : 6000 * c + 2 * ν < ξ)
    {A B Y : G ⧸ H} (hYA : Y ≠ A) (hYB : Y ≠ B)
    {a b : S} (ha : a ∈ cosetOrbitAt H s A)
    (hb : b ∈ cosetOrbitAt H s B)
    {fixed : ℝ → S} (hfixed : IsGeodesicSegment fixed 0 (dist b a))
    (hfixed0 : fixed 0 = b) (hfixed1 : fixed (dist b a) = a)
    (hlarge : ξ ≤ approxCosetProjectionDistance H s δ Y A B) :
    Nonempty (FixedSideShadow H s Y b a fixed c (12 * δ)) := by
  obtain ⟨x, hxproj⟩ := exists_isApproxProjectionTo
    (cosetOrbitAt H s Y) a (cosetOrbitAt_nonempty H s Y) hδpos
  obtain ⟨y, hyproj⟩ := exists_isApproxProjectionTo
    (cosetOrbitAt H s Y) b (cosetOrbitAt_nonempty H s Y) hδpos
  have hxSet : x ∈ approxCosetProjectionSet H s δ Y A := ⟨a, ha, hxproj⟩
  have hySet : y ∈ approxCosetProjectionSet H s δ Y B := ⟨b, hb, hyproj⟩
  have hdiam := approxCosetProjectionDistance_le_two_mul_add_dist
    (ν₀ := hν0) hYA hYB hν hxSet hySet
  have hxy : 6000 * c < dist x y := by linarith
  obtain ⟨fXY, hfXY, hfXY0, hfXY1⟩ := hgeo x y
  obtain ⟨fYB, hfYB, hfYB0, hfYB1⟩ := hgeo y b
  obtain ⟨fBB, hfBB, hfBB0, hfBB1⟩ := hgeo b b
  obtain ⟨fAA, hfAA, hfAA0, hfAA1⟩ := hgeo a a
  obtain ⟨fAX, hfAX, hfAX0, hfAX1⟩ := hgeo a x
  obtain ⟨i, hi0, hi6, u, hu, u', hu', t, ht, t', ht',
      huu', htt', hclose, hclose'⟩ :=
    exists_source_close_pair_on_hexagon hδ hδ0 hgeo
      (lt_of_lt_of_le (by positivity : 0 < 30 * δ) hcδ) hcδ
      hfXY hfXY0 hfXY1 hfYB hfYB0 hfYB1 hfBB hfBB0 hfBB1
      hfixed hfixed0 hfixed1 hfAA hfAA0 hfAA1 hfAX hfAX0 hfAX1 hxy
  have hqY := isQuasiconvexSet_cosetOrbitAt hiso hquasi Y
  have hi : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · norm_num at ht ht' hclose hclose'
    exact False.elim (not_exists_long_close_pair_on_projection_segment_rev hqY hyproj
      hfYB hfYB0 hfYB1 hxproj.1 hyproj.1 hfXY hfXY0 hfXY1
      hu hu' ht ht' htt' hclose hclose' htransverse)
  · norm_num at ht ht'
    exfalso
    subst t
    subst t'
    norm_num at htt'
    linarith [hcδ, hδpos]
  · norm_num at ht ht' hclose hclose'
    exact ⟨⟨x, y, hxproj.1, hyproj.1, fXY, hfXY, hfXY0, hfXY1,
      u, u', hu, hu', t, t', ht, ht', huu'.trans (le_abs_self _),
      hclose, hclose'⟩⟩
  · norm_num at ht ht'
    exfalso
    subst t
    subst t'
    norm_num at htt'
    linarith [hcδ, hδpos]
  · norm_num at ht ht' hclose hclose'
    exact False.elim (not_exists_long_close_pair_on_projection_segment hqY hxproj
      hfAX hfAX0 hfAX1 hxproj.1 hyproj.1 hfXY hfXY0 hfXY1
      hu hu' ht ht' htt' hclose hclose' htransverse)

/-- Two fixed-side shadows whose two ordered parameters lie in the same two
grid cells determine the same coset.  The open-cell estimates spend less than
`2δ`, while the two polygon shadows spend `24δ`; this is precisely the
`26δ` radius used in the source proof of (A4). -/
theorem eq_of_fixedSideShadows_of_parameter_dist_lt
    {δ σ R c : ℝ} (hδpos : 0 < δ)
    (hiso : IsIsometricAction G S)
    {H : Subgroup G} {s : S}
    (hquasi : ∀ (p q : G), p ∈ H → q ∈ H →
      ∀ f : ℝ → S, IsGeodesicSegment f 0 (dist (p • s) (q • s)) →
        f 0 = p • s → f (dist (p • s) (q • s)) = q • s →
          ∀ t ∈ Set.Icc (0 : ℝ) (dist (p • s) (q • s)),
            ∃ z : G, z ∈ H ∧ dist (f t) (z • s) ≤ σ)
    (hforce : ∀ g : G,
      (∀ E : ℝ, E < R → ∃ p q : G, p ∈ H ∧ q ∈ H ∧
        E ≤ dist (p • s) (q • s) ∧
        (∃ z : G, z ∈ H ∧
          dist (p • s) ((g * z) • s) ≤ 26 * δ + 2 * σ) ∧
        (∃ z : G, z ∈ H ∧
          dist (q • s) ((g * z) • s) ≤ 26 * δ + 2 * σ)) → g ∈ H)
    (hcR : R + 2 * σ ≤ c)
    {Y Z : G ⧸ H} {b a : S} {fixed : ℝ → S}
    (hfixed : IsGeodesicSegment fixed 0 (dist b a))
    (wY : FixedSideShadow H s Y b a fixed c (12 * δ))
    (wZ : FixedSideShadow H s Z b a fixed c (12 * δ))
    (ht : dist wY.t wZ.t < δ) (ht' : dist wY.t' wZ.t' < δ) :
    Y = Z := by
  have hfixed₀ : dist (fixed wY.t) (fixed wZ.t) = |wY.t - wZ.t| :=
    hfixed wY.t wY.ht wZ.t wZ.ht
  have hfixed₁ : dist (fixed wY.t') (fixed wZ.t') = |wY.t' - wZ.t'| :=
    hfixed wY.t' wY.ht' wZ.t' wZ.ht'
  have hparam₀ : |wY.t - wZ.t| < δ := by simpa [Real.dist_eq] using ht
  have hparam₁ : |wY.t' - wZ.t'| < δ := by simpa [Real.dist_eq] using ht'
  have hclose₀ : dist (wY.path wY.u) (wZ.path wZ.u) ≤ 26 * δ := by
    have htri := dist_triangle4 (wY.path wY.u) (fixed wY.t)
      (fixed wZ.t) (wZ.path wZ.u)
    have hrev : dist (fixed wZ.t) (wZ.path wZ.u) ≤ 12 * δ := by
      rw [dist_comm]
      exact wZ.close
    rw [hfixed₀] at htri
    linarith [wY.close, hrev, hparam₀, hδpos]
  have hclose₁ : dist (wY.path wY.u') (wZ.path wZ.u') ≤ 26 * δ := by
    have htri := dist_triangle4 (wY.path wY.u') (fixed wY.t')
      (fixed wZ.t') (wZ.path wZ.u')
    have hrev : dist (fixed wZ.t') (wZ.path wZ.u') ≤ 12 * δ := by
      rw [dist_comm]
      exact wZ.close'
    rw [hfixed₁] at htri
    linarith [wY.close', hrev, hparam₁, hδpos]
  exact eq_of_long_close_coset_geodesics hiso hquasi hforce hcR
    (by linarith : 26 * δ + 2 * σ ≤ 26 * δ + 2 * σ)
    wY.hy₀ wY.hy₁ wZ.hy₀ wZ.hy₁
    wY.path_geodesic wY.path_zero wY.path_dist
    wZ.path_geodesic wZ.path_zero wZ.path_dist
    wY.hu wY.hu' wZ.hu wZ.hu' wY.long hclose₀ hclose₁

/-- **DGO projection axiom (A4), single-subgroup coset form.**  For every
pair of distinct vertices, only finitely many projection vertices see that
pair with projection distance at least one uniform threshold. -/
theorem exists_approxCosetProjectionDistance_ge_finite
    {δ : ℝ} (hδ : IsHyperbolicSpace δ S) (hδ0 : 0 ≤ δ) (hδpos : 0 < δ)
    (hgeo : IsGeodesicSpace S) (hiso : IsIsometricAction G S)
    {H : Subgroup G} {s : S} (hqc : IsQuasiconvexOrbitAt H s)
    (hsep : GeometricallySeparatedAt H s) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ (A B : G ⧸ H), A ≠ B →
      {Y : G ⧸ H |
        ξ ≤ approxCosetProjectionDistance H s δ Y A B}.Finite := by
  have hqc0 := hqc
  obtain ⟨σ, hσ0, hquasi⟩ := hqc
  let ε : ℝ := 26 * δ + 2 * σ
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨R, hR0, hforce⟩ := hsep ε hε
  let c : ℝ := max (R + 2 * σ) (30 * δ + σ)
  have hc : 0 < c := by dsimp [c]; positivity
  have hcR : R + 2 * σ ≤ c := le_max_left _ _
  have hcδσ : 30 * δ + σ ≤ c := le_max_right _ _
  have hcδ : 30 * δ ≤ c := by linarith
  have htransverse : 12 * δ + σ + δ < c := by linarith
  obtain ⟨ν, hν0, hν⟩ :=
    exists_approxCosetProjectionSet_diameter_bound hδ hδ0 hgeo hiso hqc0 hsep
  let ξ : ℝ := 6000 * c + 2 * ν + 1
  have hξ : 0 < ξ := by dsimp [ξ]; positivity
  have hξLarge : 6000 * c + 2 * ν < ξ := by dsimp [ξ]; linarith
  refine ⟨ξ, hξ, ?_⟩
  intro A B hAB
  obtain ⟨a, ha⟩ := cosetOrbitAt_nonempty H s A
  obtain ⟨b, hb⟩ := cosetOrbitAt_nonempty H s B
  obtain ⟨fixed, hfixed, hfixed0, hfixed1⟩ := hgeo b a
  let Good : Set (G ⧸ H) := {Y | Y ≠ A ∧ Y ≠ B ∧
    ξ ≤ approxCosetProjectionDistance H s δ Y A B}
  have hwitness : ∀ Y : Good,
      Nonempty (FixedSideShadow H s Y.1 b a fixed c (12 * δ)) := by
    intro Y
    exact nonempty_fixedSideShadow_of_large_projection hδ hδ0 hδpos
      hgeo hiso hquasi hcδ htransverse
      hν0 hν hξLarge Y.2.1 Y.2.2.1 ha hb hfixed hfixed0 hfixed1 Y.2.2.2
  let witness : ∀ Y : Good,
      FixedSideShadow H s Y.1 b a fixed c (12 * δ) :=
    fun Y => Classical.choice (hwitness Y)
  obtain ⟨grid, hgridFinite, hgrid⟩ := Metric.totallyBounded_iff.mp
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) (dist b a))).totallyBounded
      (δ / 2) (by positivity)
  have hcenter₀ : ∀ Y : Good, ∃ z ∈ grid,
      (witness Y).t ∈ Metric.ball z (δ / 2) := by
    intro Y
    obtain ⟨z, hz, hball⟩ := Set.mem_iUnion₂.mp (hgrid (witness Y).ht)
    exact ⟨z, hz, hball⟩
  have hcenter₁ : ∀ Y : Good, ∃ z ∈ grid,
      (witness Y).t' ∈ Metric.ball z (δ / 2) := by
    intro Y
    obtain ⟨z, hz, hball⟩ := Set.mem_iUnion₂.mp (hgrid (witness Y).ht')
    exact ⟨z, hz, hball⟩
  choose center₀ hcenter₀Grid hcenter₀Ball using hcenter₀
  choose center₁ hcenter₁Grid hcenter₁Ball using hcenter₁
  let code : Good → grid × grid := fun Y =>
    (⟨center₀ Y, hcenter₀Grid Y⟩, ⟨center₁ Y, hcenter₁Grid Y⟩)
  have hcode : Function.Injective code := by
    intro Y Z hYZ
    have hc₀ : center₀ Y = center₀ Z := congrArg (fun q => q.1.1) hYZ
    have hc₁ : center₁ Y = center₁ Z := congrArg (fun q => q.2.1) hYZ
    have htYZ : dist (witness Y).t (witness Z).t < δ := by
      have hY := Metric.mem_ball.mp (hcenter₀Ball Y)
      have hZ := Metric.mem_ball.mp (hcenter₀Ball Z)
      have htri := dist_triangle (witness Y).t (center₀ Y) (witness Z).t
      rw [hc₀] at htri
      have hYsame : dist (witness Y).t (center₀ Z) < δ / 2 := by
        rwa [← hc₀]
      have hZrev : dist (center₀ Z) (witness Z).t < δ / 2 := by
        rwa [dist_comm]
      linarith [hYsame, hZrev]
    have htYZ' : dist (witness Y).t' (witness Z).t' < δ := by
      have hY := Metric.mem_ball.mp (hcenter₁Ball Y)
      have hZ := Metric.mem_ball.mp (hcenter₁Ball Z)
      have htri := dist_triangle (witness Y).t' (center₁ Y) (witness Z).t'
      rw [hc₁] at htri
      have hYsame : dist (witness Y).t' (center₁ Z) < δ / 2 := by
        rwa [← hc₁]
      have hZrev : dist (center₁ Z) (witness Z).t' < δ / 2 := by
        rwa [dist_comm]
      linarith [hYsame, hZrev]
    apply Subtype.ext
    exact eq_of_fixedSideShadows_of_parameter_dist_lt hδpos hiso hquasi
      (by simpa [ε] using hforce) hcR hfixed (witness Y) (witness Z) htYZ htYZ'
  letI : Finite grid := hgridFinite.to_subtype
  letI : Finite Good := Finite.of_injective code hcode
  have hGoodFinite : Good.Finite := Set.toFinite Good
  refine ((hGoodFinite.insert B).insert A).subset ?_
  intro Y hY
  by_cases hYA : Y = A
  · simp [hYA]
  by_cases hYB : Y = B
  · simp [hYB]
  simp only [Set.mem_insert_iff]
  exact Or.inr (Or.inr ⟨hYA, hYB, hY⟩)

end Elementary
end GGT
end GroupApproximation
