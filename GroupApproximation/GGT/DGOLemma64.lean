import GroupApproximation.GGT.DGOWindmillQuasiconvex
import GroupApproximation.GGT.ElementaryMorseOrbit
import GroupApproximation.GGT.WPDElement

/-!
# DGO Lemma 6.4: WPD at every sufficiently large power

Dahmani--Guirardel--Osin strengthen the defining existential power in WPD to
all sufficiently large powers for a loxodromic element of a geodesic
hyperbolic space.  The proof below follows theirs: a power-orbit vertex is
uniformly close to the long chord, and a quadrilateral with close endpoints
shows that an element almost fixing the chord's ends almost fixes that vertex.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.HullGeometry
open GroupApproximation.DGOWindmill

universe u v

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X]
  [MulAction G X]

/-- The strengthened WPD conclusion used in DGO §6.1: for each error, every
sufficiently large power has finite coarse pair stabilizer. -/
def IsWPDAtEventually (g : G) (x : X) : Prop :=
  ∀ ε : ℝ, 0 ≤ ε → ∃ N : ℕ, ∀ M : ℕ, N ≤ M →
    (pairStab G ε x ((g ^ M) • x)).Finite

/-- Geodesics whose corresponding endpoints are `E`-close coarsely
fellow-travel, with no restriction on where the chosen point lies. -/
theorem exists_close_of_geodesic_close_endpoints {δ E Lp Lq : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (hgeo : IsGeodesicSpace X)
    (hE : 0 ≤ E) {p q : ℝ → X}
    (hp : IsGeodesicSegment p 0 Lp) (hLp : 0 ≤ Lp)
    (hq : IsGeodesicSegment q 0 Lq) (hLq : 0 ≤ Lq)
    (h0 : dist (p 0) (q 0) ≤ E) (h1 : dist (p Lp) (q Lq) ≤ E)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) Lp) :
    ∃ s ∈ Set.Icc (0 : ℝ) Lq, dist (p t) (q s) ≤ E + 6 * δ := by
  have hp' : IsGeodesicSegment p 0 (dist (p 0) (p Lp)) := by
    have hlen : dist (p 0) (p Lp) = Lp := by
      simpa [abs_of_nonneg hLp] using hp.dist_endpoints hLp
    rwa [hlen]
  have hq' : IsGeodesicSegment q 0 (dist (q 0) (q Lq)) := by
    have hlen : dist (q 0) (q Lq) = Lq := by
      simpa [abs_of_nonneg hLq] using hq.dist_endpoints hLq
    rwa [hlen]
  obtain ⟨e0, he0, he00, he01⟩ := hgeo (p 0) (q 0)
  obtain ⟨e1, he1, he10, he11⟩ := hgeo (q Lq) (p Lp)
  have hp1 : p (dist (p 0) (p Lp)) = p Lp := by
    have hlen : dist (p 0) (p Lp) = Lp := by
      simpa [abs_of_nonneg hLp] using hp.dist_endpoints hLp
    rw [hlen]
  have hq1 : q (dist (q 0) (q Lq)) = q Lq := by
    have hlen : dist (q 0) (q Lq) = Lq := by
      simpa [abs_of_nonneg hLq] using hq.dist_endpoints hLq
    rw [hlen]
  have ht' : t ∈ Set.Icc (0 : ℝ) (dist (p 0) (p Lp)) := by
    have hlen : dist (p 0) (p Lp) = Lp := by
      simpa [abs_of_nonneg hLp] using hp.dist_endpoints hLp
    rwa [hlen]
  rcases exists_close_on_other_sides_of_quadrilateral hδ hδ0 hgeo
      hp' rfl hp1 he0 he00 he01 hq' rfl hq1 he1 he10 he11 ht' with
    ⟨s, hs, hclose⟩ | ⟨s, hs, hclose⟩ | ⟨s, hs, hclose⟩
  · refine ⟨0, ⟨le_rfl, hLq⟩, ?_⟩
    have hside : dist (e0 s) (q 0) ≤ E := by
      have hd := he0 s hs (dist (p 0) (q 0)) ⟨dist_nonneg, le_rfl⟩
      calc
        dist (e0 s) (q 0) = dist (e0 s) (e0 (dist (p 0) (q 0))) := by rw [he01]
        _ = |s - dist (p 0) (q 0)| := hd
        _ ≤ E := by
          rw [abs_of_nonpos (by linarith [hs.2])]
          linarith [hs.1]
    exact (dist_triangle _ (e0 s) _).trans (by linarith)
  · refine ⟨s, ?_, by linarith⟩
    have hlen : dist (q 0) (q Lq) = Lq := by
      simpa [abs_of_nonneg hLq] using hq.dist_endpoints hLq
    rwa [hlen] at hs
  · refine ⟨Lq, ⟨hLq, le_rfl⟩, ?_⟩
    have hside : dist (e1 s) (q Lq) ≤ E := by
      have hd := he1 s hs 0 ⟨le_rfl, dist_nonneg⟩
      calc
        dist (e1 s) (q Lq) = dist (e1 s) (e1 0) := by rw [he10]
        _ = |s - 0| := hd
        _ ≤ E := by
          rw [abs_of_nonneg (by linarith [hs.1])]
          have h1' : dist (q Lq) (p Lp) ≤ E := by rwa [dist_comm]
          linarith [hs.2, h1']
    exact (dist_triangle _ (e1 s) _).trans (by linarith)

/-- Geodesics with the same initial point and `E`-close terminal points are
uniformly close at every common arclength parameter.  This is the
same-parameter form of the quadrilateral estimate used for the oriented-axis
overlap in DGO Lemma 6.7. -/
theorem dist_same_parameter_le_of_geodesic_close_endpoints
    {δ E Lp Lq : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (hgeo : IsGeodesicSpace X)
    (hE : 0 ≤ E) {p q : ℝ → X}
    (hp : IsGeodesicSegment p 0 Lp) (hLp : 0 ≤ Lp)
    (hq : IsGeodesicSegment q 0 Lq) (hLq : 0 ≤ Lq)
    (h0 : p 0 = q 0) (h1 : dist (p Lp) (q Lq) ≤ E)
    {t : ℝ} (htp : t ∈ Set.Icc (0 : ℝ) Lp)
    (htq : t ∈ Set.Icc (0 : ℝ) Lq) :
    dist (p t) (q t) ≤ 2 * (E + 6 * δ) := by
  have hstart : dist (p 0) (q 0) ≤ E := by
    simpa only [h0, dist_self] using hE
  obtain ⟨s, hs, hclose⟩ := exists_close_of_geodesic_close_endpoints
    hδ hδ0 hgeo hE hp hLp hq hLq hstart h1 htp
  have hpt : dist (p 0) (p t) = t := by
    rw [hp.dist_eq ⟨le_rfl, htp.1.trans htp.2⟩ htp, zero_sub,
      abs_neg, abs_of_nonneg htp.1]
  have hqs : dist (q 0) (q s) = s := by
    rw [hq.dist_eq ⟨le_rfl, hs.1.trans hs.2⟩ hs, zero_sub,
      abs_neg, abs_of_nonneg hs.1]
  have hts : t ≤ s + (E + 6 * δ) := by
    calc
      t = dist (p 0) (p t) := hpt.symm
      _ ≤ dist (p 0) (q s) + dist (q s) (p t) := dist_triangle _ _ _
      _ = s + dist (p t) (q s) := by rw [h0, hqs, dist_comm]
      _ ≤ s + (E + 6 * δ) := by linarith
  have hst : s ≤ t + (E + 6 * δ) := by
    calc
      s = dist (q 0) (q s) := hqs.symm
      _ ≤ dist (q 0) (p t) + dist (p t) (q s) := dist_triangle _ _ _
      _ = t + dist (p t) (q s) := by rw [← h0, hpt]
      _ ≤ t + (E + 6 * δ) := by linarith
  have hparam : dist (q s) (q t) = |s - t| := hq.dist_eq hs htq
  have habs : |s - t| ≤ E + 6 * δ := by
    rw [abs_le]
    constructor <;> linarith
  calc
    dist (p t) (q t) ≤ dist (p t) (q s) + dist (q s) (q t) :=
      dist_triangle _ _ _
    _ = dist (p t) (q s) + |s - t| := by rw [hparam]
    _ ≤ 2 * (E + 6 * δ) := by linarith

/-- Equal arclength parameters on geodesics with both pairs of endpoints
`E`-close remain uniformly close.  Unlike the preceding common-start
specialization, this is the form used for two translated axial segments in
Bestvina--Fujiwara Proposition 6. -/
theorem dist_same_parameter_le_of_geodesic_endpoints_close
    {δ E Lp Lq : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (hgeo : IsGeodesicSpace X)
    (hE : 0 ≤ E) {p q : ℝ → X}
    (hp : IsGeodesicSegment p 0 Lp) (hLp : 0 ≤ Lp)
    (hq : IsGeodesicSegment q 0 Lq) (hLq : 0 ≤ Lq)
    (h0 : dist (p 0) (q 0) ≤ E)
    (h1 : dist (p Lp) (q Lq) ≤ E)
    {t : ℝ} (htp : t ∈ Set.Icc (0 : ℝ) Lp)
    (htq : t ∈ Set.Icc (0 : ℝ) Lq) :
    dist (p t) (q t) ≤ 3 * E + 12 * δ := by
  obtain ⟨s, hs, hclose⟩ := exists_close_of_geodesic_close_endpoints
    hδ hδ0 hgeo hE hp hLp hq hLq h0 h1 htp
  have hpt : dist (p 0) (p t) = t := by
    rw [hp.dist_eq ⟨le_rfl, htp.1.trans htp.2⟩ htp, zero_sub,
      abs_neg, abs_of_nonneg htp.1]
  have hqs : dist (q 0) (q s) = s := by
    rw [hq.dist_eq ⟨le_rfl, hs.1.trans hs.2⟩ hs, zero_sub,
      abs_neg, abs_of_nonneg hs.1]
  have hts : t ≤ s + (2 * E + 6 * δ) := by
    have htri := dist_triangle4 (p 0) (q 0) (q s) (p t)
    rw [hpt, hqs, dist_comm (q s) (p t)] at htri
    linarith
  have hst : s ≤ t + (2 * E + 6 * δ) := by
    have htri := dist_triangle4 (q 0) (p 0) (p t) (q s)
    rw [hqs, dist_comm (q 0) (p 0), hpt] at htri
    linarith
  have hparam : dist (q s) (q t) = |s - t| := hq.dist_eq hs htq
  have habs : |s - t| ≤ 2 * E + 6 * δ := by
    rw [abs_le]
    constructor <;> linarith
  calc
    dist (p t) (q t) ≤ dist (p t) (q s) + dist (q s) (q t) :=
      dist_triangle _ _ _
    _ = dist (p t) (q s) + |s - t| := by rw [hparam]
    _ ≤ 3 * E + 12 * δ := by linarith

/-- **DGO Lemma 6.4.**  A loxodromic WPD element of a geodesic hyperbolic
space satisfies WPD at every sufficiently large power. -/
theorem isWPDAtEventually_of_geodesic {δ : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (hgeo : IsGeodesicSpace X)
    (hiso : IsIsometricAction G X) {h : G} {x : X}
    (hlox : IsLoxodromic h x) (hwpd : IsWPDAt h x) :
    IsWPDAtEventually h x := by
  obtain ⟨l, hl, B, hB, hlin⟩ := hlox
  obtain ⟨K, hK, hchain⟩ :=
    ElementaryMorse.exists_bound_chain_near_chord
      (D := dist x (h • x)) hδ hδ0 dist_nonneg hl hB
  intro ε hε
  let ε' : ℝ := 3 * ε + 12 * δ + 2 * K
  have hε' : 0 ≤ ε' := by dsimp [ε']; linarith
  obtain ⟨N, hNfin⟩ := hwpd ε' hε'
  refine ⟨N, ?_⟩
  intro M hNM
  refine hNfin.subset ?_
  intro g hg
  rw [mem_pairStab] at hg ⊢
  obtain ⟨f, hf, hf0, hfL⟩ := hgeo x ((h ^ M) • x)
  let y : ℕ → X := ElementaryMorse.orbitChain h x 0
  have hedge : ∀ i, i < M →
      dist (y i) (y (i + 1)) ≤ dist x (h • x) := by
    intro i _
    exact le_of_eq (ElementaryMorse.orbitChain_edge hiso h x 0 i)
  have hprog : ∀ i j, i ≤ j → j ≤ M →
      l * ((j - i : ℕ) : ℝ) - B ≤ dist (y i) (y j) := by
    intro i j hij _
    exact ElementaryMorse.orbitChain_prog hiso hlin 0 hij
  have hy0 : y 0 = x := ElementaryMorse.orbitChain_self h x 0
  have hyM : y M = (h ^ M) • x := by
    unfold y ElementaryMorse.orbitChain
    rw [Nat.cast_zero, sub_zero, zpow_natCast]
  obtain ⟨t, ht, hNt⟩ := hchain y M hedge hprog
    (dist x ((h ^ M) • x)) dist_nonneg f hf
    (by rwa [hy0]) (by rwa [hyM]) N hNM
  let q : ℝ → X := fun s => g • f s
  have hq : IsGeodesicSegment q 0 (dist x ((h ^ M) • x)) := by
    intro s hs u hu
    dsimp [q]
    rw [hiso]
    exact hf s hs u hu
  have hq0 : q 0 = g • x := by rw [show q 0 = g • f 0 from rfl, hf0]
  have hqL : q (dist x ((h ^ M) • x)) = g • ((h ^ M) • x) := by
    rw [show q (dist x ((h ^ M) • x)) =
      g • f (dist x ((h ^ M) • x)) from rfl, hfL]
  obtain ⟨s, hs, hts⟩ := exists_close_of_geodesic_close_endpoints
    hδ hδ0 hgeo hε hf dist_nonneg hq dist_nonneg
    (by simpa only [hf0, hq0] using hg.1)
    (by simpa only [hfL, hqL] using hg.2) ht
  have htval : dist x (f t) = t := by
    have hd := hf 0 ⟨le_rfl, dist_nonneg⟩ t ht
    calc
      dist x (f t) = dist (f 0) (f t) := by rw [hf0]
      _ = |0 - t| := hd
      _ = t := by rw [abs_of_nonpos (by linarith [ht.1])]; ring
  have hsval : dist (g • x) (q s) = s := by
    have hd := hq 0 ⟨le_rfl, dist_nonneg⟩ s hs
    calc
      dist (g • x) (q s) = dist (q 0) (q s) := by rw [hq0]
      _ = |0 - s| := hd
      _ = s := by rw [abs_of_nonpos (by linarith [hs.1])]; ring
  have htsabs : |t - s| ≤ 2 * ε + 6 * δ := by
    rw [abs_le]
    have hforward := dist_triangle4 x (g • x) (q s) (f t)
    have hback := dist_triangle4 (g • x) x (f t) (q s)
    rw [htval, hsval, dist_comm (q s) (f t)] at hforward
    rw [hsval, dist_comm (g • x) x, htval] at hback
    constructor <;> linarith [hg.1, hts]
  have hft : dist (f t) (g • f t) ≤ 3 * ε + 12 * δ := by
    have hmove : dist (q s) (g • f t) = dist (f s) (f t) := by
      exact hiso g (f s) (f t)
    have hparam : dist (f s) (f t) = |s - t| := hf s hs t ht
    have habs : |s - t| = |t - s| := abs_sub_comm s t
    calc
      dist (f t) (g • f t) ≤ dist (f t) (q s) + dist (q s) (g • f t) :=
        dist_triangle _ _ _
      _ = dist (f t) (q s) + |t - s| := by rw [hmove, hparam, habs]
      _ ≤ 3 * ε + 12 * δ := by linarith
  have hyN : y N = (h ^ N) • x := by
    unfold y ElementaryMorse.orbitChain
    rw [Nat.cast_zero, sub_zero, zpow_natCast]
  constructor
  · dsimp [ε']
    linarith [hg.1]
  · rw [← hyN]
    have htri := dist_triangle4 (y N) (f t) (g • f t) (g • y N)
    have hisoN := hiso g (f t) (y N)
    rw [hisoN] at htri
    have hsym : dist (f t) (y N) = dist (y N) (f t) := dist_comm _ _
    rw [hsym] at htri
    dsimp [ε']
    linarith

end GGT
end GroupApproximation
