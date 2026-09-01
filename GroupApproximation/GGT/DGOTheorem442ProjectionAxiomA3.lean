import GroupApproximation.GGT.DGOTheorem442ProjectionAxioms
import GroupApproximation.GGT.OlshanskiiLemma25

/-!
# DGO Theorem 4.42: projection axiom (A3)

For three distinct coset-orbit vertices, DGO's axiom (A3) is the
Behrstock inequality

`min {d^π_Y(A,B), d^π_B(A,Y)} < ξ`.

The constants below follow the proof of Lemma 4.47.  If `σ` is the orbit
quasiconvexity constant, put

* `ε = 13δ + 2σ`;
* `c = max {R(ε) + 2σ, 30δ + σ}`;
* choose `ν` as in Lemma 4.46; and
* `ξ = 6000c + 2ν + 1`.

The final `1` is only the slack needed to turn the source's strict choice
`ξ > 6000c + 2ν` into a canonical witness.  The source uses its polygon
Lemma 3.2 twice, first on a hexagon and then on a pentagon.  The repository's
four-point hyperbolicity convention gives `12δ`-close witnesses for both
polygons, which is stronger than the printed `13δ` allowance.
-/

namespace GroupApproximation
namespace GGT
namespace Elementary

open GroupApproximation.HullGeometry
open GroupApproximation.DGOWindmill
open GroupApproximation.Olshanskii

universe u v

variable {G : Type u} [Group G] {S : Type v} [PseudoMetricSpace S]
  [MulAction G S]

/-- Two nonempty sets admit a pair which is a `κ`-approximate projection in
both directions.  This is the infimum-free content of choosing points whose
distance is within `κ` of the distance between the two sets. -/
theorem exists_mutual_isApproxProjectionTo
    (A B : Set S) (hA : A.Nonempty) (hB : B.Nonempty)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ a ∈ A, ∃ b ∈ B,
      IsApproxProjectionTo B a b κ ∧ IsApproxProjectionTo A b a κ := by
  let values : Set ℝ :=
    {r | ∃ a : S, a ∈ A ∧ ∃ b : S, b ∈ B ∧ dist a b = r}
  have hvalues : values.Nonempty := by
    obtain ⟨a, ha⟩ := hA
    obtain ⟨b, hb⟩ := hB
    exact ⟨dist a b, a, ha, b, hb, rfl⟩
  have hbelow : BddBelow values := by
    refine ⟨0, ?_⟩
    intro r hr
    obtain ⟨a, -, b, -, rfl⟩ := hr
    exact dist_nonneg
  have hinf : sInf values < sInf values + κ := by linarith
  obtain ⟨r, hrvalues, hr⟩ := exists_lt_of_csInf_lt hvalues hinf
  obtain ⟨a, ha, b, hb, hrab⟩ := hrvalues
  refine ⟨a, ha, b, hb, ⟨hb, ?_⟩, ⟨ha, ?_⟩⟩
  · intro z hz
    have hzvalues : dist a z ∈ values := ⟨a, ha, z, hz, rfl⟩
    have hinf_le : sInf values ≤ dist a z := csInf_le hbelow hzvalues
    rw [hrab]
    linarith
  · intro z hz
    have hzvalues : dist z b ∈ values := ⟨z, hz, b, hb, rfl⟩
    have hinf_le : sInf values ≤ dist z b := csInf_le hbelow hzvalues
    rw [dist_comm b a, hrab, dist_comm b z]
    linarith

/-- The common quasiconvexity constant of the subgroup orbit also works for
every quotient-indexed coset orbit. -/
theorem isQuasiconvexSet_cosetOrbitAt
    (hiso : IsIsometricAction G S)
    {H : Subgroup G} {s : S} {σ : ℝ}
    (hquasi : ∀ (p q : G), p ∈ H → q ∈ H →
      ∀ f : ℝ → S, IsGeodesicSegment f 0 (dist (p • s) (q • s)) →
        f 0 = p • s → f (dist (p • s) (q • s)) = q • s →
          ∀ t ∈ Set.Icc (0 : ℝ) (dist (p • s) (q • s)),
            ∃ c : G, c ∈ H ∧ dist (f t) (c • s) ≤ σ)
    (Y : G ⧸ H) : IsQuasiconvexSet (cosetOrbitAt H s Y) σ := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective Y
  rw [cosetOrbitAt_mk]
  exact isQuasiconvexSet_leftCosetOrbitAt hiso hquasi g

/-- A long shadow on a geodesic ending at an approximate projection is
impossible.  This is the elementary exclusion used for the transverse sides
of both source polygons. -/
theorem not_exists_long_close_pair_on_projection_segment
    {δ σ D c : ℝ} {Q : Set S} {a x p q : S}
    (hQ : IsQuasiconvexSet Q σ)
    (hx : IsApproxProjectionTo Q a x δ)
    {fax fpq : ℝ → S}
    (hax : IsGeodesicSegment fax 0 (dist a x))
    (hax0 : fax 0 = a) (hax1 : fax (dist a x) = x)
    (hp : p ∈ Q) (hq : q ∈ Q)
    (hpq : IsGeodesicSegment fpq 0 (dist p q))
    (hpq0 : fpq 0 = p) (hpq1 : fpq (dist p q) = q)
    {u u' t t' : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) (dist p q))
    (hu' : u' ∈ Set.Icc (0 : ℝ) (dist p q))
    (ht : t ∈ Set.Icc (0 : ℝ) (dist a x))
    (ht' : t' ∈ Set.Icc (0 : ℝ) (dist a x))
    (hspan : c ≤ |t' - t|)
    (hclose : dist (fpq u) (fax t) ≤ D)
    (hclose' : dist (fpq u') (fax t') ≤ D)
    (hlarge : D + σ + δ < c) : False := by
  rcases le_total t t' with htt | htt
  · obtain ⟨w, hwQ, huw⟩ := hQ p hp q hq fpq hpq hpq0 hpq1 u hu
    have htx : dist (fax t) x = dist a x - t := by
      calc
        dist (fax t) x = dist (fax t) (fax (dist a x)) := by rw [hax1]
        _ = |t - dist a x| := hax t ht _ ⟨dist_nonneg, le_rfl⟩
        _ = dist a x - t := by
          rw [abs_of_nonpos (by linarith [ht.2])]
          ring
    have hat : dist a (fax t) = t := by
      calc
        dist a (fax t) = dist (fax 0) (fax t) := by rw [hax0]
        _ = |(0 : ℝ) - t| := hax 0 ⟨le_rfl, dist_nonneg⟩ t ht
        _ = t := by rw [abs_of_nonpos (by linarith [ht.1])]; ring
    have hnear := hx.2 w hwQ
    have haw := dist_triangle4 a (fax t) (fpq u) w
    have hcloseRev : dist (fax t) (fpq u) ≤ D := by rwa [dist_comm]
    have hdist : c ≤ dist (fax t) x := by
      rw [htx]
      rw [abs_of_nonneg (sub_nonneg.mpr htt)] at hspan
      linarith [ht'.2]
    linarith

  · obtain ⟨w, hwQ, hu'w⟩ := hQ p hp q hq fpq hpq hpq0 hpq1 u' hu'
    have ht'x : dist (fax t') x = dist a x - t' := by
      calc
        dist (fax t') x = dist (fax t') (fax (dist a x)) := by rw [hax1]
        _ = |t' - dist a x| := hax t' ht' _ ⟨dist_nonneg, le_rfl⟩
        _ = dist a x - t' := by
          rw [abs_of_nonpos (by linarith [ht'.2])]
          ring
    have hat' : dist a (fax t') = t' := by
      calc
        dist a (fax t') = dist (fax 0) (fax t') := by rw [hax0]
        _ = |(0 : ℝ) - t'| := hax 0 ⟨le_rfl, dist_nonneg⟩ t' ht'
        _ = t' := by rw [abs_of_nonpos (by linarith [ht'.1])]; ring
    have hnear := hx.2 w hwQ
    have haw := dist_triangle4 a (fax t') (fpq u') w
    have hcloseRev : dist (fax t') (fpq u') ≤ D := by rwa [dist_comm]
    have hdist : c ≤ dist (fax t') x := by
      rw [ht'x]
      rw [abs_of_nonpos (sub_nonpos.mpr htt)] at hspan
      linarith [ht.2]
    linarith

/-- The preceding transverse-side exclusion with the projection segment read
from its projection endpoint back to its source endpoint. -/
theorem not_exists_long_close_pair_on_projection_segment_rev
    {δ σ D c : ℝ} {Q : Set S} {a x p q : S}
    (hQ : IsQuasiconvexSet Q σ)
    (hx : IsApproxProjectionTo Q a x δ)
    {fxa fpq : ℝ → S}
    (hxa : IsGeodesicSegment fxa 0 (dist x a))
    (hxa0 : fxa 0 = x) (hxa1 : fxa (dist x a) = a)
    (hp : p ∈ Q) (hq : q ∈ Q)
    (hpq : IsGeodesicSegment fpq 0 (dist p q))
    (hpq0 : fpq 0 = p) (hpq1 : fpq (dist p q) = q)
    {u u' t t' : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) (dist p q))
    (hu' : u' ∈ Set.Icc (0 : ℝ) (dist p q))
    (ht : t ∈ Set.Icc (0 : ℝ) (dist x a))
    (ht' : t' ∈ Set.Icc (0 : ℝ) (dist x a))
    (hspan : c ≤ |t' - t|)
    (hclose : dist (fpq u) (fxa t) ≤ D)
    (hclose' : dist (fpq u') (fxa t') ≤ D)
    (hlarge : D + σ + δ < c) : False := by
  let fax : ℝ → S := fun r => fxa (dist x a - r)
  have hdist : dist x a = dist a x := dist_comm x a
  have hax : IsGeodesicSegment fax 0 (dist a x) := by
    rw [← hdist]
    exact IsGeodesicSegment.reverse_zero dist_nonneg hxa
  have hax0 : fax 0 = a := by simp only [fax, sub_zero, hxa1]
  have hax1 : fax (dist a x) = x := by simp only [fax, ← hdist, sub_self, hxa0]
  have ht0 : dist x a - t ∈ Set.Icc (0 : ℝ) (dist a x) := by
    rw [← hdist]
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have ht0' : dist x a - t' ∈ Set.Icc (0 : ℝ) (dist a x) := by
    rw [← hdist]
    exact ⟨by linarith [ht'.2], by linarith [ht'.1]⟩
  apply not_exists_long_close_pair_on_projection_segment hQ hx hax hax0 hax1
    hp hq hpq hpq0 hpq1 hu hu' ht0 ht0'
      (by
        rw [show (dist x a - t') - (dist x a - t) = -(t' - t) by ring, abs_neg]
        exact hspan)
      (by
        change dist (fpq u) (fxa (dist x a - (dist x a - t))) ≤ D
        rw [show dist x a - (dist x a - t) = t by ring]
        exact hclose)
      (by
        change dist (fpq u') (fxa (dist x a - (dist x a - t'))) ≤ D
        rw [show dist x a - (dist x a - t') = t' by ring]
        exact hclose')
      hlarge

/-- A source-faithful long-side witness for a geodesic hexagon.  The selected
side is numbered `1` through `5`; side `0` is the distinguished long side.
The `12δ` endpoint error comes from the dyadic chord bound for the other five
sides. -/
theorem exists_source_close_pair_on_hexagon
    {δ c : ℝ} (hδ : IsHyperbolicSpace δ S) (hδ0 : 0 ≤ δ)
    (hgeo : IsGeodesicSpace S) (hc : 0 < c) (hcδ : 30 * δ ≤ c)
    {x₀ x₁ x₂ x₃ x₄ x₅ : S}
    {f₀ f₁ f₂ f₃ f₄ f₅ : ℝ → S}
    (hf₀ : IsGeodesicSegment f₀ 0 (dist x₀ x₁))
    (hf₀0 : f₀ 0 = x₀) (hf₀1 : f₀ (dist x₀ x₁) = x₁)
    (hf₁ : IsGeodesicSegment f₁ 0 (dist x₁ x₂))
    (hf₁0 : f₁ 0 = x₁) (hf₁1 : f₁ (dist x₁ x₂) = x₂)
    (hf₂ : IsGeodesicSegment f₂ 0 (dist x₂ x₃))
    (hf₂0 : f₂ 0 = x₂) (hf₂1 : f₂ (dist x₂ x₃) = x₃)
    (hf₃ : IsGeodesicSegment f₃ 0 (dist x₃ x₄))
    (hf₃0 : f₃ 0 = x₃) (hf₃1 : f₃ (dist x₃ x₄) = x₄)
    (hf₄ : IsGeodesicSegment f₄ 0 (dist x₄ x₅))
    (hf₄0 : f₄ 0 = x₄) (hf₄1 : f₄ (dist x₄ x₅) = x₅)
    (hf₅ : IsGeodesicSegment f₅ 0 (dist x₅ x₀))
    (hf₅0 : f₅ 0 = x₅) (hf₅1 : f₅ (dist x₅ x₀) = x₀)
    (hlong : 6000 * c < dist x₀ x₁) :
    ∃ i : ℕ, 0 < i ∧ i < 6 ∧
      ∃ u ∈ Set.Icc (0 : ℝ) (dist x₀ x₁),
        ∃ u' ∈ Set.Icc (0 : ℝ) (dist x₀ x₁),
          ∃ t ∈ Set.Icc (0 : ℝ)
              (dist (![x₀, x₁, x₂, x₃, x₄, x₅]
                  (⟨i % 6, Nat.mod_lt i (by omega)⟩ : Fin 6))
                (![x₀, x₁, x₂, x₃, x₄, x₅]
                  (⟨(i + 1) % 6, Nat.mod_lt (i + 1) (by omega)⟩ : Fin 6))),
            ∃ t' ∈ Set.Icc (0 : ℝ)
              (dist (![x₀, x₁, x₂, x₃, x₄, x₅]
                  (⟨i % 6, Nat.mod_lt i (by omega)⟩ : Fin 6))
                (![x₀, x₁, x₂, x₃, x₄, x₅]
                  (⟨(i + 1) % 6, Nat.mod_lt (i + 1) (by omega)⟩ : Fin 6))),
              c ≤ u' - u ∧ c ≤ |t' - t| ∧
                dist (f₀ u)
                    (![f₀, f₁, f₂, f₃, f₄, f₅]
                      (⟨i % 6, Nat.mod_lt i (by omega)⟩ : Fin 6) t) ≤ 12 * δ ∧
                dist (f₀ u')
                    (![f₀, f₁, f₂, f₃, f₄, f₅]
                      (⟨i % 6, Nat.mod_lt i (by omega)⟩ : Fin 6) t') ≤ 12 * δ := by
  let vs : ℕ → S := fun i => ![x₀, x₁, x₂, x₃, x₄, x₅]
    (⟨i % 6, Nat.mod_lt i (by omega)⟩ : Fin 6)
  let sides : ℕ → ℝ → S :=
    fun i => ![f₀, f₁, f₂, f₃, f₄, f₅]
      (⟨i % 6, Nat.mod_lt i (by omega)⟩ : Fin 6)
  have hpoly : IsClosedPolygonAt vs sides 0 6 := by
    constructor
    · intro i hi hlt
      have hi6 : i < 6 := by omega
      interval_cases i <;> simp [vs, sides] <;> aesop
    · simp [vs]
  have hD : 3 * δ * (((3 : ℕ) : ℝ) + 1) ≤ 12 * δ := by ring_nf; exact le_rfl
  have hlong' : ((6 : ℝ) - 1) * (c + 4 * (12 * δ)) + 0 < dist x₀ x₁ := by
    nlinarith
  obtain ⟨i, hi0, hi6, -, u, hu, u', hu', t, ht, t', ht',
      huu', htt', hclose, hclose'⟩ :=
    exists_long_close_pair hδ hδ0 hgeo (n := 6) (c := 3) (b := 0)
      (by omega) (by norm_num) hpoly hD Set.univ (fun _ => 0)
      (fun _ => (le_refl (0 : ℝ))) (by simp) (by simp) hc hlong'
  have hvs0 : vs 0 = x₀ := rfl
  have hvs1 : vs 1 = x₁ := rfl
  have hu0 : u ∈ Set.Icc (0 : ℝ) (dist x₀ x₁) := by
    simpa only [hvs0, hvs1, zero_add] using hu
  have hu0' : u' ∈ Set.Icc (0 : ℝ) (dist x₀ x₁) := by
    simpa only [hvs0, hvs1, zero_add] using hu'
  exact ⟨i, hi0, hi6, u, hu0,
    u', hu0', t, by simpa [vs] using ht,
    t', by simpa [vs] using ht', huu', htt',
    by simpa [sides] using hclose, by simpa [sides] using hclose'⟩

/-- The pentagon instance used in the second half of DGO's A3 argument. -/
theorem exists_source_close_pair_on_pentagon
    {δ c : ℝ} (hδ : IsHyperbolicSpace δ S) (hδ0 : 0 ≤ δ)
    (hgeo : IsGeodesicSpace S) (hc : 0 < c) (hcδ : 30 * δ ≤ c)
    {x₀ x₁ x₂ x₃ x₄ : S} {f₀ f₁ f₂ f₃ f₄ : ℝ → S}
    (hf₀ : IsGeodesicSegment f₀ 0 (dist x₀ x₁))
    (hf₀0 : f₀ 0 = x₀) (hf₀1 : f₀ (dist x₀ x₁) = x₁)
    (hf₁ : IsGeodesicSegment f₁ 0 (dist x₁ x₂))
    (hf₁0 : f₁ 0 = x₁) (hf₁1 : f₁ (dist x₁ x₂) = x₂)
    (hf₂ : IsGeodesicSegment f₂ 0 (dist x₂ x₃))
    (hf₂0 : f₂ 0 = x₂) (hf₂1 : f₂ (dist x₂ x₃) = x₃)
    (hf₃ : IsGeodesicSegment f₃ 0 (dist x₃ x₄))
    (hf₃0 : f₃ 0 = x₃) (hf₃1 : f₃ (dist x₃ x₄) = x₄)
    (hf₄ : IsGeodesicSegment f₄ 0 (dist x₄ x₀))
    (hf₄0 : f₄ 0 = x₄) (hf₄1 : f₄ (dist x₄ x₀) = x₀)
    (hlong : 5000 * c < dist x₀ x₁) :
    ∃ i : ℕ, 0 < i ∧ i < 5 ∧
      ∃ u ∈ Set.Icc (0 : ℝ) (dist x₀ x₁),
        ∃ u' ∈ Set.Icc (0 : ℝ) (dist x₀ x₁),
          ∃ t ∈ Set.Icc (0 : ℝ)
              (dist (![x₀, x₁, x₂, x₃, x₄]
                  (⟨i % 5, Nat.mod_lt i (by omega)⟩ : Fin 5))
                (![x₀, x₁, x₂, x₃, x₄]
                  (⟨(i + 1) % 5, Nat.mod_lt (i + 1) (by omega)⟩ : Fin 5))),
            ∃ t' ∈ Set.Icc (0 : ℝ)
              (dist (![x₀, x₁, x₂, x₃, x₄]
                  (⟨i % 5, Nat.mod_lt i (by omega)⟩ : Fin 5))
                (![x₀, x₁, x₂, x₃, x₄]
                  (⟨(i + 1) % 5, Nat.mod_lt (i + 1) (by omega)⟩ : Fin 5))),
              c ≤ u' - u ∧ c ≤ |t' - t| ∧
                dist (f₀ u) (![f₀, f₁, f₂, f₃, f₄]
                    (⟨i % 5, Nat.mod_lt i (by omega)⟩ : Fin 5) t)
                    ≤ 12 * δ ∧
                dist (f₀ u') (![f₀, f₁, f₂, f₃, f₄]
                    (⟨i % 5, Nat.mod_lt i (by omega)⟩ : Fin 5) t')
                    ≤ 12 * δ := by
  let vs : ℕ → S := fun i => ![x₀, x₁, x₂, x₃, x₄]
    (⟨i % 5, Nat.mod_lt i (by omega)⟩ : Fin 5)
  let sides : ℕ → ℝ → S := fun i => ![f₀, f₁, f₂, f₃, f₄]
    (⟨i % 5, Nat.mod_lt i (by omega)⟩ : Fin 5)
  have hpoly : IsClosedPolygonAt vs sides 0 5 := by
    constructor
    · intro i hi hlt
      have hi5 : i < 5 := by omega
      interval_cases i <;> simp [vs, sides] <;> aesop
    · simp [vs]
  have hD : 3 * δ * (((2 : ℕ) : ℝ) + 1) ≤ 12 * δ := by
    norm_num
    nlinarith
  have hlong' : ((5 : ℝ) - 1) * (c + 4 * (12 * δ)) + 0 < dist x₀ x₁ := by
    nlinarith
  obtain ⟨i, hi0, hi5, -, u, hu, u', hu', t, ht, t', ht',
      huu', htt', hclose, hclose'⟩ :=
    exists_long_close_pair hδ hδ0 hgeo (n := 5) (c := 2) (b := 0)
      (by omega) (by norm_num) hpoly hD Set.univ (fun _ => 0)
      (fun _ => (le_refl (0 : ℝ))) (by simp) (by simp) hc hlong'
  have hvs0 : vs 0 = x₀ := rfl
  have hvs1 : vs 1 = x₁ := rfl
  have hu0 : u ∈ Set.Icc (0 : ℝ) (dist x₀ x₁) := by
    simpa only [hvs0, hvs1, zero_add] using hu
  have hu0' : u' ∈ Set.Icc (0 : ℝ) (dist x₀ x₁) := by
    simpa only [hvs0, hvs1, zero_add] using hu'
  exact ⟨i, hi0, hi5, u, hu0, u', hu0', t, by simpa [vs] using ht,
    t', by simpa [vs] using ht', huu', htt', by simpa [sides] using hclose,
    by simpa [sides] using hclose'⟩

/-- Geometric separation forbids long close subsegments on geodesics in two
distinct coset orbits.  The hypotheses are arranged exactly as they arise
from the polygon lemma. -/
theorem eq_of_long_close_coset_geodesics
    (hiso : IsIsometricAction G S)
    {H : Subgroup G} {s : S} {σ ε R D c : ℝ}
    (hquasi : ∀ (p q : G), p ∈ H → q ∈ H →
      ∀ f : ℝ → S, IsGeodesicSegment f 0 (dist (p • s) (q • s)) →
        f 0 = p • s → f (dist (p • s) (q • s)) = q • s →
          ∀ t ∈ Set.Icc (0 : ℝ) (dist (p • s) (q • s)),
            ∃ z : G, z ∈ H ∧ dist (f t) (z • s) ≤ σ)
    (hforce : ∀ g : G,
      (∀ E : ℝ, E < R → ∃ a b : G, a ∈ H ∧ b ∈ H ∧
        E ≤ dist (a • s) (b • s) ∧
        (∃ z : G, z ∈ H ∧ dist (a • s) ((g * z) • s) ≤ ε) ∧
        (∃ z : G, z ∈ H ∧ dist (b • s) ((g * z) • s) ≤ ε)) → g ∈ H)
    (hR : R + 2 * σ ≤ c) (hDε : D + 2 * σ ≤ ε)
    {Y Z : G ⧸ H} {y₀ y₁ z₀ z₁ : S}
    (hy₀ : y₀ ∈ cosetOrbitAt H s Y) (hy₁ : y₁ ∈ cosetOrbitAt H s Y)
    (hz₀ : z₀ ∈ cosetOrbitAt H s Z) (hz₁ : z₁ ∈ cosetOrbitAt H s Z)
    {fY fZ : ℝ → S}
    (hfY : IsGeodesicSegment fY 0 (dist y₀ y₁))
    (hfY0 : fY 0 = y₀) (hfY1 : fY (dist y₀ y₁) = y₁)
    (hfZ : IsGeodesicSegment fZ 0 (dist z₀ z₁))
    (hfZ0 : fZ 0 = z₀) (hfZ1 : fZ (dist z₀ z₁) = z₁)
    {u u' t t' : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) (dist y₀ y₁))
    (hu' : u' ∈ Set.Icc (0 : ℝ) (dist y₀ y₁))
    (ht : t ∈ Set.Icc (0 : ℝ) (dist z₀ z₁))
    (ht' : t' ∈ Set.Icc (0 : ℝ) (dist z₀ z₁))
    (hspan : c ≤ |u' - u|)
    (hclose : dist (fY u) (fZ t) ≤ D)
    (hclose' : dist (fY u') (fZ t') ≤ D) : Y = Z := by
  have hY := isQuasiconvexSet_cosetOrbitAt hiso hquasi Y
  have hZ := isQuasiconvexSet_cosetOrbitAt hiso hquasi Z
  obtain ⟨p, hpY, hup⟩ := hY y₀ hy₀ y₁ hy₁ fY hfY hfY0 hfY1 u hu
  obtain ⟨p', hpY', hu'p'⟩ := hY y₀ hy₀ y₁ hy₁ fY hfY hfY0 hfY1 u' hu'
  obtain ⟨q, hqZ, htq⟩ := hZ z₀ hz₀ z₁ hz₁ fZ hfZ hfZ0 hfZ1 t ht
  obtain ⟨q', hqZ', ht'q'⟩ := hZ z₀ hz₀ z₁ hz₁ fZ hfZ hfZ0 hfZ1 t' ht'
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective Y
  obtain ⟨f, rfl⟩ := QuotientGroup.mk_surjective Z
  rw [cosetOrbitAt_mk] at hpY hpY' hqZ hqZ'
  obtain ⟨a, haH, rfl⟩ := hpY
  obtain ⟨a', ha'H, rfl⟩ := hpY'
  obtain ⟨b, hbH, rfl⟩ := hqZ
  obtain ⟨b', hb'H, rfl⟩ := hqZ'
  apply QuotientGroup.eq.mpr
  apply hforce (g⁻¹ * f)
  intro E hER
  refine ⟨a, a', haH, ha'H, ?_, ⟨b, hbH, ?_⟩, ⟨b', hb'H, ?_⟩⟩
  · have hmain : dist (fY u) (fY u') = |u - u'| := hfY u hu u' hu'
    have htri := dist_triangle4 (fY u) ((g * a) • s) ((g * a') • s) (fY u')
    have hu'p'Rev : dist ((g * a') • s) (fY u') ≤ σ := by rwa [dist_comm]
    have hfar : R ≤ dist ((g * a) • s) ((g * a') • s) := by
      rw [hmain, abs_sub_comm] at htri
      linarith
    have hnorm : dist (a • s) (a' • s) =
        dist ((g * a) • s) ((g * a') • s) := by
      calc
        dist (a • s) (a' • s) =
            dist (g⁻¹ • ((g * a) • s)) (g⁻¹ • ((g * a') • s)) := by
              simp only [← mul_smul, inv_mul_cancel_left]
        _ = dist ((g * a) • s) ((g * a') • s) := hiso g⁻¹ _ _
    rw [hnorm]
    exact le_trans (le_of_lt hER) hfar
  · have hnear : dist ((g * a) • s) ((f * b) • s) ≤ ε := by
      have htri := dist_triangle4 ((g * a) • s) (fY u) (fZ t) ((f * b) • s)
      have hupRev : dist ((g * a) • s) (fY u) ≤ σ := by rwa [dist_comm]
      linarith
    calc
      dist (a • s) (((g⁻¹ * f) * b) • s) =
          dist (g⁻¹ • ((g * a) • s)) (g⁻¹ • ((f * b) • s)) := by
            simp only [← mul_smul, inv_mul_cancel_left, mul_assoc]
      _ = dist ((g * a) • s) ((f * b) • s) := hiso g⁻¹ _ _
      _ ≤ ε := hnear
  · have hnear : dist ((g * a') • s) ((f * b') • s) ≤ ε := by
      have htri := dist_triangle4 ((g * a') • s) (fY u') (fZ t') ((f * b') • s)
      have hu'p'Rev : dist ((g * a') • s) (fY u') ≤ σ := by rwa [dist_comm]
      linarith
    calc
      dist (a' • s) (((g⁻¹ * f) * b') • s) =
          dist (g⁻¹ • ((g * a') • s)) (g⁻¹ • ((f * b') • s)) := by
            simp only [← mul_smul, inv_mul_cancel_left, mul_assoc]
      _ = dist ((g * a') • s) ((f * b') • s) := hiso g⁻¹ _ _
      _ ≤ ε := hnear

/-- **DGO projection axiom (A3), single-subgroup coset form.**  There is one
uniform Behrstock constant for all triples of distinct coset-orbit vertices. -/
theorem exists_approxCosetProjectionDistance_min_lt
    {δ : ℝ} (hδ : IsHyperbolicSpace δ S) (hδ0 : 0 ≤ δ) (hδpos : 0 < δ)
    (hgeo : IsGeodesicSpace S) (hiso : IsIsometricAction G S)
    {H : Subgroup G} {s : S} (hqc : IsQuasiconvexOrbitAt H s)
    (hsep : GeometricallySeparatedAt H s) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ (Y A B : G ⧸ H), Y ≠ A → Y ≠ B → A ≠ B →
      min (approxCosetProjectionDistance H s δ Y A B)
          (approxCosetProjectionDistance H s δ B A Y) < ξ := by
  have hqc0 := hqc
  obtain ⟨σ, hσ0, hquasi⟩ := hqc
  let ε : ℝ := 13 * δ + 2 * σ
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨R, hR0, hforce⟩ := hsep ε hε
  let c : ℝ := max (R + 2 * σ) (30 * δ + σ)
  have hc : 0 < c := by dsimp [c]; positivity
  have hcR : R + 2 * σ ≤ c := le_max_left _ _
  have hcδ : 30 * δ + σ ≤ c := le_max_right _ _
  have hcδ' : 30 * δ ≤ c := by linarith
  have hcloseε : 12 * δ + 2 * σ ≤ ε := by dsimp [ε]; linarith
  have htransverse : 12 * δ + σ + δ < c := by linarith
  obtain ⟨ν, hν0, hν⟩ :=
    exists_approxCosetProjectionSet_diameter_bound hδ hδ0 hgeo hiso hqc0 hsep
  let ξ : ℝ := 6000 * c + 2 * ν + 1
  have hξ : 0 < ξ := by dsimp [ξ]; positivity
  refine ⟨ξ, hξ, ?_⟩
  intro Y A B hYA hYB hAB
  obtain ⟨a, haA, x, hxY, hxproj, -⟩ :=
    exists_mutual_isApproxProjectionTo (cosetOrbitAt H s A)
      (cosetOrbitAt H s Y) (cosetOrbitAt_nonempty H s A)
      (cosetOrbitAt_nonempty H s Y) hδpos
  obtain ⟨b, hbB, y, hyY, hyproj, hbproj⟩ :=
    exists_mutual_isApproxProjectionTo (cosetOrbitAt H s B)
      (cosetOrbitAt H s Y) (cosetOrbitAt_nonempty H s B)
      (cosetOrbitAt_nonempty H s Y) hδpos
  have hxSet : x ∈ approxCosetProjectionSet H s δ Y A := ⟨a, haA, hxproj⟩
  have hySet : y ∈ approxCosetProjectionSet H s δ Y B := ⟨b, hbB, hyproj⟩
  have hbSet : b ∈ approxCosetProjectionSet H s δ B Y := ⟨y, hyY, hbproj⟩
  by_cases hsmall : approxCosetProjectionDistance H s δ Y A B < ξ
  · exact lt_of_le_of_lt (min_le_left _ _) hsmall
  have hdiamXY : approxCosetProjectionDistance H s δ Y A B ≤
      2 * ν + dist x y := by
    apply Metric.diam_le_of_forall_dist_le
    · positivity
    · intro p hp q hq
      change p ∈ approxCosetProjectionPairSet H s δ Y A B at hp
      change q ∈ approxCosetProjectionPairSet H s δ Y A B at hq
      rcases hp with hpA | hpB
      · rcases hq with hqA | hqB
        · have hpq := hν Y A hYA p hpA q hqA
          linarith [hν0, dist_nonneg (x := x) (y := y)]
        · have hpx := hν Y A hYA p hpA x hxSet
          have hyq := hν Y B hYB y hySet q hqB
          have htri := dist_triangle4 p x y q
          linarith
      · rcases hq with hqA | hqB
        · have hpy := hν Y B hYB p hpB y hySet
          have hxq := hν Y A hYA x hxSet q hqA
          have htri := dist_triangle4 p y x q
          rw [dist_comm y x] at htri
          linarith
        · have hpq := hν Y B hYB p hpB q hqB
          linarith [hν0, dist_nonneg (x := x) (y := y)]
  have hxy : 6000 * c < dist x y := by
    have hnot : ξ ≤ approxCosetProjectionDistance H s δ Y A B := not_lt.mp hsmall
    dsimp [ξ] at hnot
    linarith
  obtain ⟨fXY, hfXY, hfXY0, hfXY1⟩ := hgeo x y
  obtain ⟨fYB, hfYB, hfYB0, hfYB1⟩ := hgeo y b
  obtain ⟨fAX, hfAX, hfAX0, hfAX1⟩ := hgeo a x
  have hqY := isQuasiconvexSet_cosetOrbitAt hiso hquasi Y
  have hqB := isQuasiconvexSet_cosetOrbitAt hiso hquasi B
  have hcross : ∀ z ∈ approxCosetProjectionSet H s δ B A,
      dist z b ≤ 5000 * c := by
    intro b' hb'
    obtain ⟨a', ha'A, hb'proj⟩ := hb'
    by_contra hbb'
    have hbb'long : 5000 * c < dist b' b := lt_of_not_ge hbb'
    obtain ⟨fBB', hfBB', hfBB'0, hfBB'1⟩ := hgeo b b'
    obtain ⟨fB'A', hfB'A', hfB'A'0, hfB'A'1⟩ := hgeo b' a'
    obtain ⟨fA'A, hfA'A, hfA'A0, hfA'A1⟩ := hgeo a' a
    obtain ⟨i, hi0, hi6, u, hu, u', hu', t, ht, t', ht',
        huu', htt', hclose, hclose'⟩ :=
      exists_source_close_pair_on_hexagon hδ hδ0 hgeo hc hcδ'
        hfXY hfXY0 hfXY1 hfYB hfYB0 hfYB1 hfBB' hfBB'0 hfBB'1
        hfB'A' hfB'A'0 hfB'A'1 hfA'A hfA'A0 hfA'A1
        hfAX hfAX0 hfAX1 hxy
    have hi : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
    rcases hi with rfl | rfl | hi
    · norm_num at ht ht' hclose hclose'
      exact not_exists_long_close_pair_on_projection_segment_rev hqY hyproj
        hfYB hfYB0 hfYB1 hxY hyY hfXY hfXY0 hfXY1 hu hu' ht ht' htt'
        hclose hclose' htransverse
    · norm_num at ht ht' hclose hclose'
      have heq := eq_of_long_close_coset_geodesics hiso hquasi hforce hcR hcloseε
        hxY hyY hbB hb'proj.1 hfXY hfXY0 hfXY1 hfBB' hfBB'0 hfBB'1
        hu hu' ht ht' (by rw [abs_of_nonneg (by linarith)]; linarith)
        hclose hclose'
      exact hYB heq
    · rcases hi with rfl | rfl | rfl
      · norm_num at ht ht' hclose hclose'
        -- This is the one side which can survive the hexagon argument.
        change t ∈ Set.Icc (0 : ℝ) (dist b' a') at ht
        change t' ∈ Set.Icc (0 : ℝ) (dist b' a') at ht'
        change dist (fXY u) (fB'A' t) ≤ 12 * δ at hclose
        change dist (fXY u') (fB'A' t') ≤ 12 * δ at hclose'
        let U : S := fXY u
        let V : S := fB'A' t
        obtain ⟨fB'B, hfB'B, hfB'B0, hfB'B1⟩ := hgeo b' b
        obtain ⟨fBY, hfBY, hfBY0, hfBY1⟩ := hgeo b y
        obtain ⟨fUV, hfUV, hfUV0, hfUV1⟩ := hgeo U V
        let fYU : ℝ → S := fun r => fXY (dist x y - r)
        have hfYU : IsGeodesicSegment fYU 0 (dist y U) := by
          have hrev := isGeodesicSegment_shift_rev hfXY hu.1 (le_refl (dist x y))
          have hdistYU : dist y U = dist x y - u := by
            dsimp [U]
            calc
              dist y (fXY u) = dist (fXY (dist x y)) (fXY u) := by rw [hfXY1]
              _ = |dist x y - u| := hfXY _ ⟨dist_nonneg, le_rfl⟩ u hu
              _ = dist x y - u := abs_of_nonneg (sub_nonneg.mpr hu.2)
          simpa only [fYU, hdistYU] using hrev
        have hfYU0 : fYU 0 = y := by simp [fYU, hfXY1]
        have hfYU1 : fYU (dist y U) = U := by
          have hdistYU : dist y U = dist x y - u := by
            dsimp [U]
            calc
              dist y (fXY u) = dist (fXY (dist x y)) (fXY u) := by rw [hfXY1]
              _ = |dist x y - u| := hfXY _ ⟨dist_nonneg, le_rfl⟩ u hu
              _ = dist x y - u := abs_of_nonneg (sub_nonneg.mpr hu.2)
          simp [fYU, hdistYU, U]
        let fVB' : ℝ → S := fun r => fB'A' (t - r)
        have hfVB' : IsGeodesicSegment fVB' 0 (dist V b') := by
          have hrev := isGeodesicSegment_shift_rev hfB'A' (show (0 : ℝ) ≤ 0 by rfl) ht.2
          have hdist : dist V b' = t := by
            dsimp [V]
            calc
              dist (fB'A' t) b' = dist (fB'A' t) (fB'A' 0) := by rw [hfB'A'0]
              _ = |t - 0| := hfB'A' t ht 0 ⟨le_rfl, dist_nonneg⟩
              _ = t := by rw [sub_zero, abs_of_nonneg ht.1]
          simpa only [fVB', sub_zero, hdist] using hrev
        have hfVB'0 : fVB' 0 = V := by simp [fVB', V]
        have hfVB'1 : fVB' (dist V b') = b' := by
          have hdist : dist V b' = t := by
            dsimp [V]
            calc
              dist (fB'A' t) b' = dist (fB'A' t) (fB'A' 0) := by rw [hfB'A'0]
              _ = |t - 0| := hfB'A' t ht 0 ⟨le_rfl, dist_nonneg⟩
              _ = t := by rw [sub_zero, abs_of_nonneg ht.1]
          simp [fVB', hdist, hfB'A'0]
        obtain ⟨j, hj0, hj5, r, hr, r', hr', w, hw, w', hw',
            hrr', hww', hpclose, hpclose'⟩ :=
          exists_source_close_pair_on_pentagon hδ hδ0 hgeo hc hcδ'
            hfB'B hfB'B0 hfB'B1 hfBY hfBY0 hfBY1 hfYU hfYU0 hfYU1
            hfUV hfUV0 hfUV1 hfVB' hfVB'0 hfVB'1 hbb'long
        have hj : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
        rcases hj with rfl | rfl | rfl | rfl
        · norm_num at hw hw' hpclose hpclose'
          exact not_exists_long_close_pair_on_projection_segment_rev hqB hbproj
            hfBY hfBY0 hfBY1 hb'proj.1 hbB hfB'B hfB'B0 hfB'B1
            hr hr' hw hw' hww' hpclose hpclose' htransverse
        · norm_num at hw hw' hpclose hpclose'
          have hdistYU : dist y U = dist x y - u := by
            dsimp [U]
            calc
              dist y (fXY u) = dist (fXY (dist x y)) (fXY u) := by rw [hfXY1]
              _ = |dist x y - u| := hfXY _ ⟨dist_nonneg, le_rfl⟩ u hu
              _ = dist x y - u := abs_of_nonneg (sub_nonneg.mpr hu.2)
          have hw0 : dist x y - w ∈ Set.Icc (0 : ℝ) (dist x y) :=
            ⟨by linarith [hw.2, hdistYU, hu.1], by linarith [hw.1]⟩
          have hw0' : dist x y - w' ∈ Set.Icc (0 : ℝ) (dist x y) :=
            ⟨by linarith [hw'.2, hdistYU, hu.1], by linarith [hw'.1]⟩
          have heq := eq_of_long_close_coset_geodesics hiso hquasi hforce hcR
            hcloseε hb'proj.1 hbB hxY hyY hfB'B hfB'B0 hfB'B1
            hfXY hfXY0 hfXY1 hr hr' hw0 hw0'
            (by rw [abs_of_nonneg (by linarith)]; linarith)
            (by simpa [fYU] using hpclose) (by simpa [fYU] using hpclose')
          exact hYB heq.symm
        · norm_num at hw hw' hpclose hpclose'
          have hconnector : dist U V ≤ 12 * δ := by simpa [U, V] using hclose
          have hparam : |w' - w| ≤ dist U V := by
            rw [abs_le]
            constructor <;> linarith [hw.1, hw.2, hw'.1, hw'.2]
          linarith [hcδ', hδpos]
        · norm_num at hw hw' hpclose hpclose'
          have hdistVB' : dist V b' = t := by
            dsimp [V]
            calc
              dist (fB'A' t) b' = dist (fB'A' t) (fB'A' 0) := by rw [hfB'A'0]
              _ = |t - 0| := hfB'A' t ht 0 ⟨le_rfl, dist_nonneg⟩
              _ = t := by rw [sub_zero, abs_of_nonneg ht.1]
          have hw0 : t - w ∈ Set.Icc (0 : ℝ) (dist b' a') :=
            ⟨by linarith [hw.2], by linarith [hw.1, ht.2]⟩
          have hw0' : t - w' ∈ Set.Icc (0 : ℝ) (dist b' a') :=
            ⟨by linarith [hw'.2], by linarith [hw'.1, ht.2]⟩
          exact not_exists_long_close_pair_on_projection_segment_rev hqB hb'proj
            hfB'A' hfB'A'0 hfB'A'1 hb'proj.1 hbB hfB'B hfB'B0 hfB'B1
            hr hr' hw0 hw0'
            (by
              have he : |(t - w') - (t - w)| = |w' - w| := by
                rw [show (t - w') - (t - w) = -(w' - w) by ring, abs_neg]
              rwa [he])
            (by simpa [fVB'] using hpclose) (by simpa [fVB'] using hpclose')
            htransverse
      · norm_num at ht ht' hclose hclose'
        have heq := eq_of_long_close_coset_geodesics hiso hquasi hforce hcR hcloseε
          hxY hyY ha'A haA hfXY hfXY0 hfXY1 hfA'A hfA'A0 hfA'A1
          hu hu' ht ht' (by rw [abs_of_nonneg (by linarith)]; linarith)
          hclose hclose'
        exact hYA heq
      · norm_num at ht ht' hclose hclose'
        exact not_exists_long_close_pair_on_projection_segment hqY hxproj
          hfAX hfAX0 hfAX1 hxY hyY hfXY hfXY0 hfXY1 hu hu' ht ht' htt'
          hclose hclose' htransverse
  have hdiamB : approxCosetProjectionDistance H s δ B A Y ≤
      5000 * c + ν := by
    apply Metric.diam_le_of_forall_dist_le
    · positivity
    · intro p hp q hq
      change p ∈ approxCosetProjectionPairSet H s δ B A Y at hp
      change q ∈ approxCosetProjectionPairSet H s δ B A Y at hq
      rcases hp with hpA | hpY
      · rcases hq with hqA | hqY
        · have hpq := hν B A hAB.symm p hpA q hqA
          linarith [hν0, hc]
        · have hpb := hcross p hpA
          have hbq := hν B Y hYB.symm b hbSet q hqY
          exact (dist_triangle p b q).trans (by linarith)
      · rcases hq with hqA | hqY
        · have hpb := hν B Y hYB.symm p hpY b hbSet
          have hbq := hcross q hqA
          have htri := dist_triangle p b q
          have hbq' : dist b q ≤ 5000 * c := by rwa [dist_comm]
          linarith
        · have hpq := hν B Y hYB.symm p hpY q hqY
          linarith [hν0, hc]
  have hsecond : approxCosetProjectionDistance H s δ B A Y < ξ := by
    dsimp [ξ]
    linarith
  exact lt_of_le_of_lt (min_le_right _ _) hsecond

end Elementary
end GGT
end GroupApproximation
