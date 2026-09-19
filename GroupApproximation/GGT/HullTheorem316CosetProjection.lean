import GroupApproximation.GGT.HullTheorem316RelativePolygon
import GroupApproximation.GGT.ElementaryCoarseTranslationQuasiconvex

/-!
# Coset projection in Hull's Theorem 3.16

The long-side polygon argument produces points on geodesics in the prescribed-
alphabet geodesic model.  This file supplies the next bridge in Hull's proof:
a geodesic whose endpoints lie in a translate of a cyclic peripheral orbit
stays uniformly close to that same translate.

Unlike an appeal to a projection theorem, this is proved from the repository's
unconditional Morse argument.  The only identification needed is Hull's
conclusion `E(g) = ⟨g⟩`.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.GGT
open GroupApproximation.GGT.Elementary
open GroupApproximation.GGT.OsinComponents
open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.HullGeometry
open GroupApproximation.Olshanskii
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

variable {G : Type u} [Group G]

/-- The group vertex in the geodesic model is the orbit of the identity
vertex. -/
theorem iotaG_eq_smul_one (A : Alphabet G) (g : G) :
    iotaG A g = g • iotaG A 1 := by
  unfold iotaG
  have hc : Cayley.of A g = g • Cayley.of A 1 := by
    change g = g * 1
    rw [mul_one]
  rw [hc]
  rw [CayleyGeodesicModel.isEquivariant_iotaQuot A g (Cayley.of A 1)]

/-- Quasiconvexity of the cyclic orbit in the prescribed-alphabet geodesic
model.  The constant is uniform over both endpoints and over the chosen
geodesic segment. -/
theorem isQuasiconvexOrbitAt_zpowers_pointQuot
    (A : HullGeneratingSet G) {g : G}
    (hlox : IsLoxodromic g (Cayley.base A.alphabet))
    (hcyc : elementaryClosure g = Subgroup.zpowers g) :
    IsQuasiconvexOrbitAt (Subgroup.zpowers g) (iotaG A.alphabet 1) := by
  have hhyp : IsHyperbolicSpace (A.delta + 6)
      (CayleyGeodesicModel.PointQuot A.alphabet) :=
    CayleyGeodesicModel.isHyperbolicSpace_pointQuot
      (CayleyGeodesicModel.isHyperbolicSpace_point A.alphabet A.hyperbolic)
  have hdelta0 : 0 ≤ A.delta + 6 := by
    have := Elementary.nonneg_of_isHyperbolicSpace A.hyperbolic
      (Cayley.base A.alphabet)
    linarith
  have hiso : IsIsometricAction G
      (CayleyGeodesicModel.PointQuot A.alphabet) :=
    CayleyGeodesicModel.isIsometricAction_pointQuot A.alphabet
  have hlox' : IsLoxodromic g (iotaG A.alphabet 1) := by
    apply isLoxodromic_map (C := (1 : ℝ)) zero_le_one
      (CayleyGeodesicModel.hasAdditiveDistortion_iotaQuot A.alphabet)
      (CayleyGeodesicModel.isEquivariant_iotaQuot A.alphabet)
      hlox
  have hclose : ElementaryClosureOrbitClose g (iotaG A.alphabet 1) := by
    refine ⟨0, le_rfl, ?_⟩
    intro a ha
    rw [hcyc] at ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact ⟨k, by rw [dist_self]⟩
  have hqc := isQuasiconvexOrbitAt_elementaryClosure_of_orbitClose
    hhyp hdelta0 hiso hlox' hclose
  rwa [hcyc] at hqc

/-- Translate orbit quasiconvexity from `H·x` to an arbitrary left coset
`vH·x`.  This is the precise coset-projection operation used on a peripheral
side of Hull's polygon. -/
theorem exists_coset_point_ne_of_quasiconvexOrbitAt
    {X : Type w} [PseudoMetricSpace X] [MulAction G X]
    (hiso : IsIsometricAction G X) {H : Subgroup G} {x : X}
    (hqc : IsQuasiconvexOrbitAt H x) :
    ∃ σ : ℝ, 0 ≤ σ ∧ ∀ (v a b : G), a ∈ H → b ∈ H →
      ∀ f : ℝ → X,
        IsGeodesicSegment f 0 (dist ((v * a) • x) ((v * b) • x)) →
        f 0 = (v * a) • x →
        f (dist ((v * a) • x) ((v * b) • x)) = (v * b) • x →
        ∀ t ∈ Set.Icc (0 : ℝ) (dist ((v * a) • x) ((v * b) • x)),
          ∃ c : G, c ∈ H ∧ dist (f t) ((v * c) • x) ≤ σ := by
  obtain ⟨σ, hσ0, hσ⟩ := hqc
  refine ⟨σ, hσ0, ?_⟩
  intro v a b ha hb f hf hf0 hfL t ht
  let f' : ℝ → X := fun s => v⁻¹ • f s
  have hlen : dist ((v * a) • x) ((v * b) • x) = dist (a • x) (b • x) := by
    have hm := hiso v⁻¹ ((v * a) • x) ((v * b) • x)
    simpa only [← mul_smul, inv_mul_cancel_left] using hm.symm
  have hf' : IsGeodesicSegment f' 0 (dist (a • x) (b • x)) := by
    rw [← hlen]
    intro s hs r hr
    dsimp [f']
    rw [hiso]
    exact hf s hs r hr
  have hf'0 : f' 0 = a • x := by
    dsimp [f']
    rw [hf0, ← mul_smul, inv_mul_cancel_left]
  have hf'L : f' (dist (a • x) (b • x)) = b • x := by
    dsimp [f']
    rw [← hlen, hfL, ← mul_smul, inv_mul_cancel_left]
  obtain ⟨c, hc, hnear⟩ := hσ a b ha hb f' hf' hf'0 hf'L t (by rwa [← hlen])
  refine ⟨c, hc, ?_⟩
  have hm := hiso v (f' t) (c • x)
  calc
    dist (f t) ((v * c) • x) = dist (v • f' t) (v • (c • x)) := by
      simp [f', ← mul_smul]
    _ = dist (f' t) (c • x) := hm
    _ ≤ σ := hnear

/-- Every geodesic side whose endpoints are vertices in a left coset of a
cyclic peripheral subgroup stays uniformly close to vertices of that coset. -/
theorem exists_zpowers_coset_projection_pointQuot
    (A : HullGeneratingSet G) {g : G}
    (hlox : IsLoxodromic g (Cayley.base A.alphabet))
    (hcyc : elementaryClosure g = Subgroup.zpowers g) :
    ∃ σ : ℝ, 0 ≤ σ ∧ ∀ (v a b : G),
      a ∈ Subgroup.zpowers g → b ∈ Subgroup.zpowers g →
      ∀ f : ℝ → CayleyGeodesicModel.PointQuot A.alphabet,
        IsGeodesicSegment f 0
          (dist (iotaG A.alphabet (v * a)) (iotaG A.alphabet (v * b))) →
        f 0 = iotaG A.alphabet (v * a) →
        f (dist (iotaG A.alphabet (v * a))
          (iotaG A.alphabet (v * b))) = iotaG A.alphabet (v * b) →
        ∀ t ∈ Set.Icc (0 : ℝ)
            (dist (iotaG A.alphabet (v * a)) (iotaG A.alphabet (v * b))),
          ∃ c : G, c ∈ Subgroup.zpowers g ∧
            dist (f t) (iotaG A.alphabet (v * c)) ≤ σ := by
  have hqc := isQuasiconvexOrbitAt_zpowers_pointQuot A hlox hcyc
  obtain ⟨σ, hσ0, hσ⟩ := exists_coset_point_ne_of_quasiconvexOrbitAt
    (CayleyGeodesicModel.isIsometricAction_pointQuot A.alphabet) hqc
  refine ⟨σ, hσ0, ?_⟩
  intro v a b ha hb f hf hf0 hfL t ht
  have hva := iotaG_eq_smul_one A.alphabet (v * a)
  have hvb := iotaG_eq_smul_one A.alphabet (v * b)
  have hf' : IsGeodesicSegment f 0
      (dist ((v * a) • iotaG A.alphabet 1)
        ((v * b) • iotaG A.alphabet 1)) := by
    rwa [← hva, ← hvb]
  have hf0' : f 0 = (v * a) • iotaG A.alphabet 1 := by rwa [← hva]
  have hfL' : f (dist ((v * a) • iotaG A.alphabet 1)
      ((v * b) • iotaG A.alphabet 1)) =
      (v * b) • iotaG A.alphabet 1 := by
    rwa [← hva, ← hvb]
  have ht' : t ∈ Set.Icc (0 : ℝ)
      (dist ((v * a) • iotaG A.alphabet 1)
        ((v * b) • iotaG A.alphabet 1)) := by
    rwa [← hva, ← hvb]
  obtain ⟨c, hc, hnear⟩ := hσ v a b ha hb f hf' hf0' hfL' t ht'
  refine ⟨c, hc, ?_⟩
  rwa [← iotaG_eq_smul_one A.alphabet (v * c)] at hnear

/-- The distinguished closing side of Hull's actual relative-word polygon is
uniformly close to the cyclic subgroup whenever the word endpoint lies in that
subgroup.  This discharges the closing-side half of the projection step after
`exists_peripheral_side_close_to_long_closing_side`. -/
theorem exists_closingSide_zpowers_projection
    (A : HullGeneratingSet G) {g : G}
    (hlox : IsLoxodromic g (Cayley.base A.alphabet))
    (hcyc : elementaryClosure g = Subgroup.zpowers g) :
    ∃ σ : ℝ, 0 ≤ σ ∧ ∀ {L : Type w}
      (q : List (RelLetter G L)),
      RelLetter.listVal q ∈ Subgroup.zpowers g →
      ∀ t ∈ Set.Icc (0 : ℝ)
          (dist (iotaG A.alphabet (RelLetter.listVal q))
            (iotaG A.alphabet 1)),
        ∃ c : G, c ∈ Subgroup.zpowers g ∧
          dist ((Classical.choose (exists_relativeClosingPolygon A.alphabet q)) 0 t)
            (iotaG A.alphabet c) ≤ σ := by
  obtain ⟨σ, hσ0, hproj⟩ := exists_zpowers_coset_projection_pointQuot A hlox hcyc
  refine ⟨σ, hσ0, ?_⟩
  intro L q hq t ht
  let sides := Classical.choose (exists_relativeClosingPolygon A.alphabet q)
  have hpoly : IsClosedPolygonAt (relativeClosingVertex A.alphabet q) sides 0
      (q.length + 1) :=
    Classical.choose_spec (exists_relativeClosingPolygon A.alphabet q)
  have hside := hpoly.1 0 (by omega) (by omega)
  have hgeo : IsGeodesicSegment (sides 0) 0
      (dist (iotaG A.alphabet (1 * RelLetter.listVal q))
        (iotaG A.alphabet (1 * 1))) := by
    simpa [relativeClosingVertex] using hside.1
  have hzero : sides 0 0 = iotaG A.alphabet (1 * RelLetter.listVal q) := by
    simpa [relativeClosingVertex] using hside.2.1
  have hlast : sides 0
      (dist (iotaG A.alphabet (1 * RelLetter.listVal q))
        (iotaG A.alphabet (1 * 1))) = iotaG A.alphabet (1 * 1) := by
    simpa [relativeClosingVertex] using hside.2.2
  have ht' : t ∈ Set.Icc (0 : ℝ)
      (dist (iotaG A.alphabet (1 * RelLetter.listVal q))
        (iotaG A.alphabet (1 * 1))) := by simpa using ht
  obtain ⟨c, hc, hnear⟩ := hproj 1 (RelLetter.listVal q) 1 hq (one_mem _) (sides 0)
    hgeo hzero hlast t ht'
  exact ⟨c, hc, by simpa [sides] using hnear⟩

/-- A peripheral side selected by the long-side lemma is uniformly close to
the corresponding left cyclic coset.  The conclusion names the coset vertex
at which the peripheral letter is read, which is exactly the translating
element consumed by geometric separation. -/
theorem exists_peripheralSide_zpowers_projection
    (A : HullGeneratingSet G) {g : G}
    (hlox : IsLoxodromic g (Cayley.base A.alphabet))
    (hcyc : elementaryClosure g = Subgroup.zpowers g) :
    ∃ σ : ℝ, 0 ≤ σ ∧ ∀ {L : Type w}
      (q : List (RelLetter G L)) (i : ℕ) (lam : L) (h : G),
      0 < i → i < q.length + 1 →
      q[i - 1]? = some (RelLetter.comp lam h) →
      h ∈ Subgroup.zpowers g →
      ∀ t ∈ Set.Icc (0 : ℝ)
          (dist (relativeClosingVertex A.alphabet q i)
            (relativeClosingVertex A.alphabet q (i + 1))),
        ∃ c : G, c ∈ Subgroup.zpowers g ∧
          dist ((Classical.choose (exists_relativeClosingPolygon A.alphabet q)) i t)
            (iotaG A.alphabet (vertex 1 q (i - 1) * c)) ≤ σ := by
  obtain ⟨σ, hσ0, hproj⟩ := exists_zpowers_coset_projection_pointQuot A hlox hcyc
  refine ⟨σ, hσ0, ?_⟩
  intro L q i lam h hi0 hi hletter hh t ht
  let j := i - 1
  have hj : j < q.length := by dsimp [j]; omega
  have hij : i = j + 1 := by dsimp [j]; omega
  have hget : q[j]? = some (q[j]'hj) := List.getElem?_eq_getElem hj
  have hletter' : q[j]'hj = RelLetter.comp lam h := by
    have heq : some (q[j]'hj) = some (RelLetter.comp lam h) := by
      rw [← hget]
      simpa [j] using hletter
    exact Option.some.inj heq
  let sides := Classical.choose (exists_relativeClosingPolygon A.alphabet q)
  have hpoly : IsClosedPolygonAt (relativeClosingVertex A.alphabet q) sides 0
      (q.length + 1) :=
    Classical.choose_spec (exists_relativeClosingPolygon A.alphabet q)
  have hside := hpoly.1 i (by omega) (by omega)
  have hv0 : relativeClosingVertex A.alphabet q i =
      iotaG A.alphabet (vertex 1 q j * 1) := by
    rw [hij, relativeClosingVertex_succ, mul_one]
  have hv1 : relativeClosingVertex A.alphabet q (i + 1) =
      iotaG A.alphabet (vertex 1 q j * h) := by
    rw [show i + 1 = (j + 1) + 1 by omega, relativeClosingVertex_succ,
      vertex_succ q 1 j hj, hletter']
    rfl
  have hgeo : IsGeodesicSegment (sides i) 0
      (dist (iotaG A.alphabet (vertex 1 q j * 1))
        (iotaG A.alphabet (vertex 1 q j * h))) := by
    simpa only [hv0, hv1] using hside.1
  have hzero : sides i 0 = iotaG A.alphabet (vertex 1 q j * 1) := by
    simpa only [hv0] using hside.2.1
  have hlast : sides i
      (dist (iotaG A.alphabet (vertex 1 q j * 1))
        (iotaG A.alphabet (vertex 1 q j * h))) =
      iotaG A.alphabet (vertex 1 q j * h) := by
    simpa only [hv0, hv1] using hside.2.2
  have ht' : t ∈ Set.Icc (0 : ℝ)
      (dist (iotaG A.alphabet (vertex 1 q j * 1))
        (iotaG A.alphabet (vertex 1 q j * h))) := by
    simpa only [hv0, hv1] using ht
  obtain ⟨c, hc, hnear⟩ := hproj (vertex 1 q j) 1 h (one_mem _) hh
    (sides i) hgeo hzero hlast t ht'
  refine ⟨c, hc, ?_⟩
  simpa [sides, j] using hnear

/-- Two sufficiently far-apart group vertices which are model-close to one
translated peripheral coset force the geometric-separation conclusion.  This
is the metric conversion needed after projecting Hull's two close pairs; the
additive `1` is exactly the distortion of `iotaG`. -/
theorem geometricSeparation_of_pointQuot_witness
    {L : Type w} (A : Alphabet G) (K : L → Subgroup G)
    (hsep : IsGeometricallySeparated A K) (E : ℝ) :
    ∃ R : ℕ, ∀ (v : G) (lam mu : L) (a b c d : G),
      a ∈ K mu → b ∈ K mu → c ∈ K lam → d ∈ K lam →
      dist (iotaG A a) (iotaG A (v * c)) ≤ E →
      dist (iotaG A b) (iotaG A (v * d)) ≤ E →
      R ≤ wordDist A.carrier a b →
      lam = mu ∧ v ∈ K lam := by
  let eps : ℕ := ⌈E + 1⌉₊
  obtain ⟨R, hR⟩ := hsep eps
  refine ⟨R, ?_⟩
  intro v lam mu a b c d ha hb hc hd hac hbd hab
  apply hR v lam mu
  intro D hDR
  refine ⟨a, b, ha, hb, le_trans (Nat.le_of_lt hDR) hab, ?_, ?_⟩
  · refine ⟨c, hc, ?_⟩
    have hlower := le_dist_iotaG A a (v * c)
    have hcast : ((wordDist A.carrier a (v * c) : ℕ) : ℝ) ≤ E + 1 := by
      linarith
    have hceil : E + 1 ≤ ((eps : ℕ) : ℝ) := Nat.le_ceil (E + 1)
    exact_mod_cast hcast.trans hceil
  · refine ⟨d, hd, ?_⟩
    have hlower := le_dist_iotaG A b (v * d)
    have hcast : ((wordDist A.carrier b (v * d) : ℕ) : ℝ) ≤ E + 1 := by
      linarith
    have hceil : E + 1 ≤ ((eps : ℕ) : ℝ) := Nat.le_ceil (E + 1)
    exact_mod_cast hcast.trans hceil

end HullSC
end GroupApproximation
