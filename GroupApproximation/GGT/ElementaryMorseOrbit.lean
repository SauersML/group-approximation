import GroupApproximation.GGT.ElementaryMorseChord
import GroupApproximation.GGT.ElementaryTransfer
import GroupApproximation.GGT.CayleyGeodesicRealisation

/-!
# The Morse lemma for orbits: `CentralizerOrbitNearAxis` is a theorem

`ElementaryMorseChord` proves the two halves of the Morse lemma for chains with
bounded steps and linear progress up to additive slack.  An orbit chain
`i ↦ q^{i−n} z` of a loxodromic `q` is such a chain, with step
`d(z, q z)` and the progress constants of `IsLoxodromic`, so both halves apply
to it directly; no subsampling is needed.

## Step 4 of the plan in `ElementaryMorse`, carried out

For `c` commuting with `q` and `w = cᵏ x`, the orbit chain of `q` through `w` is
the translate by `cᵏ` of the orbit chain through `x`, so it has the *same* step
and progress constants, and the chord `γ'` joining its ends has endpoints at
distance `d(x, w)` from those of the chord `γ` through the ends of the chain at
`x`.  Two thin triangles put every point of `γ'` within `6δ` of `γ` or within
`d(x, w) + 6δ` of an end of `γ'`; the chain half of the Morse lemma puts `w`
within `K₂` of a point `γ' s`, and for `n` large that point is far from both
ends, so it is within `6δ` of `γ`; the chord half puts `γ` within `K₁` of the
chain through `x`.  So `w` is within `K₁ + K₂ + 6δ` of an orbit point `qʲ x`, a
bound that does not depend on `c`, on `k` or on `n`.

## At Hull's Cayley graph

`Γ(G,A)` is not geodesic, but its metric realisation is
(`CayleyGeodesicModel.hasGeodesicModel_of_hullGeneratingSet`), and
`Elementary.centralizerOrbitNearAxis_of_map` pulls the statement back along
the vertex inclusion.  `centralizerOrbitNearAxis_cayley` is the residual
`hnear` of `Elementary.osinNonElementary_of_torsionFree_normal`, discharged.

## Status

**Not compiled**, written while builds were frozen.
-/

namespace GroupApproximation
namespace GGT
namespace ElementaryMorse

open GroupApproximation.HullGeometry

universe u v

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X] [MulAction G X]

/-! ## Orbit chains -/

/-- Two commuting elements act commutingly. -/
theorem smul_smul_comm_of_commute {a b : G} (hab : Commute a b) (x : X) :
    a • (b • x) = b • (a • x) := by
  rw [← mul_smul, hab.eq, mul_smul]

/-- The orbit chain of `q` through `z`, shifted so that vertex `n` is `z`. -/
def orbitChain (q : G) (z : X) (n : ℕ) (i : ℕ) : X := (q ^ ((i : ℤ) - n)) • z

theorem orbitChain_dist (hiso : IsIsometricAction G X) (q : G) (z : X)
    (n i j : ℕ) :
    dist (orbitChain q z n i) (orbitChain q z n j) =
      dist z ((q ^ ((j : ℤ) - i)) • z) := by
  unfold orbitChain
  rw [dist_zpow_orbit hiso]
  have h : ((j : ℤ) - n) - ((i : ℤ) - n) = (j : ℤ) - i := by omega
  rw [h]

theorem orbitChain_edge (hiso : IsIsometricAction G X) (q : G) (z : X)
    (n i : ℕ) :
    dist (orbitChain q z n i) (orbitChain q z n (i + 1)) = dist z (q • z) := by
  rw [orbitChain_dist hiso]
  have h : (((i + 1 : ℕ) : ℤ) - (i : ℤ)) = 1 := by omega
  rw [h, zpow_one]

theorem orbitChain_prog (hiso : IsIsometricAction G X) {q : G} {z : X}
    {l B : ℝ} (hz : ∀ m : ℕ, l * m - B ≤ dist z ((q ^ m) • z)) (n : ℕ)
    {i j : ℕ} (hij : i ≤ j) :
    l * ((j - i : ℕ) : ℝ) - B ≤ dist (orbitChain q z n i) (orbitChain q z n j) := by
  rw [orbitChain_dist hiso]
  have h : ((j : ℤ) - i) = ((j - i : ℕ) : ℤ) := by omega
  rw [h, zpow_natCast]
  exact hz (j - i)

theorem orbitChain_self (q : G) (z : X) (n : ℕ) : orbitChain q z n n = z := by
  unfold orbitChain
  rw [sub_self, zpow_zero, one_smul]

/-- The orbit chain through a translate by a commuting element is the translate
of the orbit chain. -/
theorem orbitChain_smul_of_commute {c q : G} (hcq : Commute c q) (k : ℤ) (x : X)
    (n i : ℕ) :
    orbitChain q ((c ^ k) • x) n i = (c ^ k) • orbitChain q x n i := by
  unfold orbitChain
  exact smul_smul_comm_of_commute ((hcq.symm.zpow_left _).zpow_right k) x

/-- A commuting element displaces every point of the `q`-orbit by the same
amount as the basepoint. -/
theorem dist_smul_orbit_of_commute (hiso : IsIsometricAction G X) {c q : G}
    (hcq : Commute c q) (k e : ℤ) (x : X) :
    dist ((q ^ e) • x) ((c ^ k) • ((q ^ e) • x)) = dist x ((c ^ k) • x) := by
  rw [smul_smul_comm_of_commute ((hcq.zpow_left k).zpow_right e) x, hiso]

/-- The `q`-displacement of a translate by a commuting element is the
`q`-displacement of the basepoint. -/
theorem dist_zpow_smul_translate_of_commute (hiso : IsIsometricAction G X)
    {c q : G} (hcq : Commute c q) (k e : ℤ) (x : X) :
    dist ((c ^ k) • x) ((q ^ e) • ((c ^ k) • x)) = dist x ((q ^ e) • x) := by
  rw [smul_smul_comm_of_commute ((hcq.symm.zpow_left e).zpow_right k) x, hiso]

/-! ## The orbit of a loxodromic element is near the chord it spans -/

/-- **`OrbitNearGeodesic`**, the intermediate residual of `ElementaryMorse`, is a
theorem: the chain half of the Morse lemma at the orbit chain. -/
theorem orbitNearGeodesic : OrbitNearGeodesic G X := by
  intro δ hδ hδ0 hgeo hiso g x hg
  obtain ⟨l, hl, B, hB, hlox⟩ := hg
  obtain ⟨K₂, hK₂0, hK₂⟩ :=
    exists_bound_chain_near_chord (D := dist x (g • x)) hδ hδ0 dist_nonneg hl hB
  refine ⟨K₂, hK₂0, ?_⟩
  intro n f hf hf0 hfL k hkn
  have hchain : ∀ i : ℕ, orbitChain g x 0 i = (g ^ (i : ℤ)) • x := by
    intro i
    unfold orbitChain
    rw [Nat.cast_zero, sub_zero]
  have hedge : ∀ i, i < n →
      dist (orbitChain g x 0 i) (orbitChain g x 0 (i + 1)) ≤ dist x (g • x) :=
    fun i _ => le_of_eq (orbitChain_edge hiso g x 0 i)
  have hprog : ∀ i j, i ≤ j → j ≤ n →
      l * ((j - i : ℕ) : ℝ) - B ≤ dist (orbitChain g x 0 i) (orbitChain g x 0 j) :=
    fun i j hij _ => orbitChain_prog hiso hlox 0 hij
  have hf0' : f 0 = orbitChain g x 0 0 := by
    rw [hchain 0, Nat.cast_zero, zpow_zero, one_smul]
    exact hf0
  have hfL' : f (dist x ((g ^ (n : ℤ)) • x)) = orbitChain g x 0 n := by
    rw [hchain n]
    exact hfL
  obtain ⟨s, hs, hd⟩ := hK₂ (orbitChain g x 0) n hedge hprog
    (dist x ((g ^ (n : ℤ)) • x)) dist_nonneg f hf hf0' hfL' k hkn
  refine ⟨s, hs, ?_⟩
  rw [← hchain k]
  exact hd

/-! ## The centralizer statement -/

/-- **`CentralizerOrbitNearAxis` holds in every geodesic hyperbolic space with an
isometric action.**  This is step 4 of the plan recorded in `ElementaryMorse`. -/
theorem centralizerOrbitNearAxis_of_geodesic {δ : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (hgeo : IsGeodesicSpace X)
    (hiso : IsIsometricAction G X) (x : X) :
    Elementary.CentralizerOrbitNearAxis G x := by
  intro q hq
  obtain ⟨l, hl, B, hB, hlox⟩ := hq
  have hD0 : 0 ≤ dist x (q • x) := dist_nonneg
  obtain ⟨K₁, hK₁0, hK₁⟩ :=
    exists_bound_chord_near_chain (D := dist x (q • x)) hδ hδ0 hD0 hl hB
  obtain ⟨K₂, hK₂0, hK₂⟩ :=
    exists_bound_chain_near_chord (D := dist x (q • x)) hδ hδ0 hD0 hl hB
  refine ⟨K₁ + K₂ + 6 * δ, by linarith, ?_⟩
  intro c hcq k
  obtain ⟨w, hw_def⟩ : ∃ w : X, w = (c ^ k) • x := ⟨_, rfl⟩
  rw [← hw_def]
  -- the translate carries the same orbit constants
  have hw : ∀ m : ℕ, l * m - B ≤ dist w ((q ^ m) • w) := by
    intro m
    rw [hw_def]
    have h := dist_zpow_smul_translate_of_commute hiso hcq k (m : ℤ) x
    rw [zpow_natCast] at h
    rw [h]
    exact hlox m
  have hDw : dist w (q • w) = dist x (q • x) := by
    rw [hw_def]
    have h := dist_zpow_smul_translate_of_commute hiso hcq k 1 x
    rw [zpow_one] at h
    exact h
  -- the length of the chain
  obtain ⟨n, hn⟩ := exists_nat_gt ((dist x w + 6 * δ + B + K₂ + 1) / l)
  have hln : dist x w + 6 * δ + B + K₂ + 1 < l * n := by
    rw [div_lt_iff₀ hl] at hn
    linarith
  have hfar : dist x w + 6 * δ + K₂ + 1 < dist w ((q ^ n) • w) := by
    have := hw n
    linarith
  -- the two chains
  have hedge_x : ∀ i, i < 2 * n →
      dist (orbitChain q x n i) (orbitChain q x n (i + 1)) ≤ dist x (q • x) :=
    fun i _ => le_of_eq (orbitChain_edge hiso q x n i)
  have hprog_x : ∀ i j, i ≤ j → j ≤ 2 * n →
      l * ((j - i : ℕ) : ℝ) - B ≤ dist (orbitChain q x n i) (orbitChain q x n j) :=
    fun i j hij _ => orbitChain_prog hiso hlox n hij
  have hedge_w : ∀ i, i < 2 * n →
      dist (orbitChain q w n i) (orbitChain q w n (i + 1)) ≤ dist x (q • x) :=
    fun i _ => le_of_eq (by rw [orbitChain_edge hiso q w n i, hDw])
  have hprog_w : ∀ i j, i ≤ j → j ≤ 2 * n →
      l * ((j - i : ℕ) : ℝ) - B ≤ dist (orbitChain q w n i) (orbitChain q w n j) :=
    fun i j hij _ => orbitChain_prog hiso hw n hij
  -- the two chords
  obtain ⟨f', hf', hf'0, hf'L⟩ :=
    hgeo (orbitChain q w n 0) (orbitChain q w n (2 * n))
  obtain ⟨f, hf, hf0, hfL⟩ :=
    hgeo (orbitChain q x n 0) (orbitChain q x n (2 * n))
  -- `w` is near the chord `f'`
  obtain ⟨s, hs, hws⟩ := hK₂ (orbitChain q w n) (2 * n) hedge_w hprog_w
    (dist (orbitChain q w n 0) (orbitChain q w n (2 * n))) dist_nonneg f' hf'
    hf'0 hf'L n (by omega)
  rw [orbitChain_self] at hws
  -- the ends of the `w`-chain are far from `w`
  have h0n : dist (orbitChain q w n 0) w = dist w ((q ^ n) • w) := by
    have h := orbitChain_dist hiso q w n 0 n
    rw [orbitChain_self] at h
    have he : ((n : ℤ) - ((0 : ℕ) : ℤ)) = ((n : ℕ) : ℤ) := by omega
    rw [he, zpow_natCast] at h
    exact h
  have hn2n : dist w (orbitChain q w n (2 * n)) = dist w ((q ^ n) • w) := by
    have h := orbitChain_dist hiso q w n n (2 * n)
    rw [orbitChain_self] at h
    have he : (((2 * n : ℕ) : ℤ) - ((n : ℕ) : ℤ)) = ((n : ℕ) : ℤ) := by omega
    rw [he, zpow_natCast] at h
    exact h
  -- so the chord point near `w` is far from both ends of `f'`
  have hfar0 : dist x w + 6 * δ + 1 < dist (f' s) (orbitChain q w n 0) := by
    have h1 := dist_triangle (orbitChain q w n 0) (f' s) w
    have h2 : dist (f' s) w = dist w (f' s) := dist_comm _ _
    have h3 : dist (f' s) (orbitChain q w n 0) =
        dist (orbitChain q w n 0) (f' s) := dist_comm _ _
    linarith
  have hfar2 : dist x w + 6 * δ + 1 < dist (f' s) (orbitChain q w n (2 * n)) := by
    have h1 := dist_triangle w (f' s) (orbitChain q w n (2 * n))
    linarith
  -- the ends of the two chords are `d(x, w)` apart
  have hΔ0 : dist (orbitChain q w n 0) (orbitChain q x n 0) = dist x w := by
    rw [hw_def, orbitChain_smul_of_commute hcq k x n 0,
      dist_comm ((c ^ k) • orbitChain q x n 0) (orbitChain q x n 0)]
    exact dist_smul_orbit_of_commute hiso hcq k _ x
  have hΔ2 : dist (orbitChain q x n (2 * n)) (orbitChain q w n (2 * n)) =
      dist x w := by
    rw [hw_def, orbitChain_smul_of_commute hcq k x n (2 * n)]
    exact dist_smul_orbit_of_commute hiso hcq k _ x
  -- the first thin triangle: `f'`, a diagonal, and the right side
  obtain ⟨g₁, hg₁, hg₁0, hg₁1⟩ :=
    hgeo (orbitChain q w n 0) (orbitChain q x n (2 * n))
  obtain ⟨g₂, hg₂, hg₂0, hg₂1⟩ :=
    hgeo (orbitChain q x n (2 * n)) (orbitChain q w n (2 * n))
  rcases exists_close_on_other_side_of_geodesic_triangle hδ hδ0 hf' hf'0 hf'L
      hg₁ hg₁0 hg₁1 hg₂ hg₂0 hg₂1 hs with ⟨s', hs', hd⟩ | ⟨s'', hs'', hd⟩
  swap
  · -- near the right side: too close to the far end of `f'`
    exfalso
    have h1 : dist (g₂ s'') (orbitChain q w n (2 * n)) ≤ dist x w := by
      rw [← hg₂1, hg₂.dist_eq hs'' ⟨dist_nonneg, le_refl _⟩,
        abs_of_nonpos (by linarith [hs''.2])]
      linarith [hs''.1, hΔ2]
    have h2 := dist_triangle (f' s) (g₂ s'') (orbitChain q w n (2 * n))
    linarith
  -- the second thin triangle: the diagonal, the left side, and `f`
  obtain ⟨g₃, hg₃, hg₃0, hg₃1⟩ :=
    hgeo (orbitChain q w n 0) (orbitChain q x n 0)
  rcases exists_close_on_other_side_of_geodesic_triangle hδ hδ0 hg₁ hg₁0 hg₁1
      hg₃ hg₃0 hg₃1 hf hf0 hfL hs' with ⟨u, hu, hd'⟩ | ⟨t, ht, hd'⟩
  · -- near the left side: too close to the near end of `f'`
    exfalso
    have h1 : dist (g₃ u) (orbitChain q w n 0) ≤ dist x w := by
      rw [← hg₃0, hg₃.dist_eq hu ⟨le_refl _, dist_nonneg⟩, sub_zero,
        abs_of_nonneg hu.1]
      linarith [hu.2, hΔ0]
    have h2 := dist_triangle (f' s) (g₁ s') (orbitChain q w n 0)
    have h3 := dist_triangle (g₁ s') (g₃ u) (orbitChain q w n 0)
    linarith
  -- near `f`: the chord half of the Morse lemma at the chain through `x`
  obtain ⟨i, -, hit⟩ := hK₁ (orbitChain q x n) (2 * n) hedge_x hprog_x
    (dist (orbitChain q x n 0) (orbitChain q x n (2 * n))) dist_nonneg f hf hf0
    hfL t ht
  refine ⟨(i : ℤ) - n, ?_⟩
  show dist w (orbitChain q x n i) ≤ K₁ + K₂ + 6 * δ
  have h1 := dist_triangle w (f' s) (f t)
  have h2 := dist_triangle (f' s) (g₁ s') (f t)
  have h3 := dist_triangle w (f t) (orbitChain q x n i)
  have h4 : dist (f t) (orbitChain q x n i) = dist (orbitChain q x n i) (f t) :=
    dist_comm _ _
  linarith

/-! ## At Hull's Cayley graph -/

section Cayley

open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Manuscript.NonMF.AxisDichotomyRoute

/-- **The Morse residual of Osin's Lemma 7.1 is discharged at `Γ(G,A)`**: the
geodesic realisation carries the theorem, and the vertex inclusion pulls it
back. -/
theorem centralizerOrbitNearAxis_cayley {G : Type u} [Group G]
    (A : HullGeneratingSet G) :
    Elementary.CentralizerOrbitNearAxis G (Cayley.base A.alphabet) := by
  obtain ⟨M⟩ := CayleyGeodesicModel.hasGeodesicModel_of_hullGeneratingSet A
  exact Elementary.centralizerOrbitNearAxis_of_map M.distortion_nonneg
    M.hasAdditiveDistortion M.equivariant
    (centralizerOrbitNearAxis_of_geodesic M.hyperbolic M.delta_nonneg M.geodesic
      M.isometric _)

end Cayley

end ElementaryMorse
end GGT
end GroupApproximation
