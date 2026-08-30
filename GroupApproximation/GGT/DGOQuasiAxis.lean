import GroupApproximation.GGT.ElementaryIndependence

/-!
# DGO Definition 6.3: the quasi-geodesic axis

Dahmani--Guirardel--Osin define the axis `lₓ` of an element `h` by choosing a
geodesic connector from `x` to `h • x` and translating that connector by every
integer power of `h`.  When `h` is loxodromic the resulting bi-infinite path is
quasi-geodesic.

This file formalizes the construction itself, independently of a chosen global
parametrization of the concatenated path.  Its carrier is the union of all
translated connector segments.  It contains the full power orbit, is
`h`-invariant, and translation by `t ∈ G` carries it exactly to the analogous
axis of `t h t⁻¹` based at `t • x`.  These are the structural facts used when
Lemma 6.7 speaks of two `G`-translations of one quasi-axis.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.HullGeometry

universe u v

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X]
  [MulAction G X]

/-- A geodesic connector from `x` to `h • x`, the fundamental segment in DGO
Definition 6.3. -/
def IsAxisConnector (h : G) (x : X) (f : ℝ → X) : Prop :=
  IsGeodesicSegment f 0 (dist x (h • x)) ∧
    f 0 = x ∧ f (dist x (h • x)) = h • x

/-- **DGO Definition 6.3, carrier of `lₓ`.**  Join successive points of the
bi-infinite orbit by translates of one connector. -/
def quasiAxis (h : G) (x : X) (f : ℝ → X) : Set X :=
  {y : X | ∃ n : ℤ, ∃ s ∈ Set.Icc (0 : ℝ) (dist x (h • x)),
    y = (h ^ n) • f s}

/-- The chosen basepoint belongs to its axis. -/
theorem self_mem_quasiAxis {h : G} {x : X} {f : ℝ → X}
    (hf : IsAxisConnector h x f) : x ∈ quasiAxis h x f := by
  refine ⟨0, 0, ⟨le_rfl, dist_nonneg⟩, ?_⟩
  rw [zpow_zero, one_smul, hf.2.1]

/-- Every integer power-orbit point belongs to the axis. -/
theorem zpow_smul_mem_quasiAxis {h : G} {x : X} {f : ℝ → X}
    (hf : IsAxisConnector h x f) (n : ℤ) :
    (h ^ n) • x ∈ quasiAxis h x f := by
  refine ⟨n, 0, ⟨le_rfl, dist_nonneg⟩, ?_⟩
  rw [hf.2.1]

/-- The axis carrier is invariant under `h`; this is the setwise form of the
`h`-invariance asserted in Definition 6.3. -/
theorem smul_mem_quasiAxis_iff (h : G) (x : X) (f : ℝ → X) (y : X) :
    h • y ∈ quasiAxis h x f ↔ y ∈ quasiAxis h x f := by
  constructor
  · rintro ⟨n, s, hs, heq⟩
    refine ⟨n - 1, s, hs, ?_⟩
    calc
      y = h⁻¹ • (h • y) := by simp
      _ = h⁻¹ • ((h ^ n) • f s) := by rw [heq]
      _ = (h ^ (n - 1)) • f s := by
        rw [← mul_smul]
        congr 1
        group
  · rintro ⟨n, s, hs, rfl⟩
    refine ⟨n + 1, s, hs, ?_⟩
    rw [← mul_smul]
    congr 1
    group

/-- Translate a connector pointwise by a group element. -/
def translateConnector (t : G) (f : ℝ → X) : ℝ → X :=
  fun s => t • f s

/-- Translating a connector gives a connector for the conjugate element at
the translated basepoint. -/
theorem isAxisConnector_translate (hiso : IsIsometricAction G X)
    {h t : G} {x : X} {f : ℝ → X} (hf : IsAxisConnector h x f) :
    IsAxisConnector (t * h * t⁻¹) (t • x) (translateConnector t f) := by
  have hend : (t * h * t⁻¹) • (t • x) = t • (h • x) := by
    simp only [mul_smul, inv_smul_smul]
  have hlen : dist (t • x) ((t * h * t⁻¹) • (t • x)) = dist x (h • x) := by
    rw [hend, hiso]
  refine ⟨?_, ?_, ?_⟩
  · rw [hlen]
    intro s hs u hu
    dsimp [translateConnector]
    rw [hiso]
    exact hf.1 s hs u hu
  · dsimp [translateConnector]
    rw [hf.2.1]
  · rw [hlen]
    dsimp [translateConnector]
    rw [hf.2.2, hend]

/-- **Translations of DGO axes are axes of conjugates.**  This is the exact
set identity behind the notation `t(l)` in Lemma 6.7. -/
theorem image_quasiAxis_eq_quasiAxis_conj
    (hiso : IsIsometricAction G X) (h t : G) (x : X) (f : ℝ → X) :
    (fun y : X => t • y) '' quasiAxis h x f =
      quasiAxis (t * h * t⁻¹) (t • x) (translateConnector t f) := by
  have hend : (t * h * t⁻¹) • (t • x) = t • (h • x) := by
    simp only [mul_smul, inv_smul_smul]
  have hlen : dist (t • x) ((t * h * t⁻¹) • (t • x)) = dist x (h • x) := by
    rw [hend, hiso]
  ext y
  constructor
  · rintro ⟨z, ⟨n, s, hs, rfl⟩, rfl⟩
    refine ⟨n, s, ?_, ?_⟩
    · rwa [hlen]
    · dsimp [translateConnector]
      rw [conj_zpow]
      simp only [mul_smul, inv_smul_smul]
  · rintro ⟨n, s, hs, rfl⟩
    refine ⟨(h ^ n) • f s, ⟨n, s, ?_, rfl⟩, ?_⟩
    · rwa [hlen] at hs
    · dsimp [translateConnector]
      rw [conj_zpow]
      simp only [mul_smul, inv_smul_smul]

/-! ## Arbitrary oriented segments of the concatenated axis -/

/-- A point on the concatenated axis, recorded by an integer translate of the
fundamental connector and its arclength parameter on that connector.  The two
descriptions of a shared connector endpoint are intentionally both allowed. -/
structure AxisPoint (h : G) (x : X) (f : ℝ → X) where
  index : ℤ
  parameter : ℝ
  parameter_mem : parameter ∈ Set.Icc (0 : ℝ) (dist x (h • x))

namespace AxisPoint

variable {h : G} {x : X} {f : ℝ → X}

/-- The point in the metric space represented by an axis coordinate. -/
def value (p : AxisPoint h x f) : X :=
  (h ^ p.index) • f p.parameter

/-- Arclength coordinate along the bi-infinite concatenated path. -/
def coordinate (p : AxisPoint h x f) : ℝ :=
  (p.index : ℝ) * dist x (h • x) + p.parameter

/-- Every represented point lies in the carrier of the quasi-axis. -/
theorem value_mem_quasiAxis (p : AxisPoint h x f) :
    p.value ∈ quasiAxis h x f :=
  ⟨p.index, p.parameter, p.parameter_mem, rfl⟩

end AxisPoint

/-- The concatenated axis, with its arclength coordinates, is a
`(λ,c)`-quasi-geodesic.  This is the parametrized condition meant by DGO when
they call the carrier `lₓ` a quasi-axis. -/
def IsQuasiGeodesicAxis (lam c : ℝ) (h : G) (x : X) (f : ℝ → X) : Prop :=
  ∀ p q : AxisPoint h x f,
    |p.coordinate - q.coordinate| / lam - c ≤ dist p.value q.value ∧
      dist p.value q.value ≤ lam * |p.coordinate - q.coordinate| + c

/-- An oriented segment of a translated concatenated axis.  Its path length
is the difference of the two arclength coordinates. -/
structure AxisSegment (h : G) (x : X) (f : ℝ → X) where
  translate : G
  initial : AxisPoint h x f
  terminal : AxisPoint h x f
  oriented : initial.coordinate ≤ terminal.coordinate

namespace AxisSegment

variable {h : G} {x : X} {f : ℝ → X}

/-- Initial endpoint after translating the axis. -/
def initialValue (p : AxisSegment h x f) : X :=
  p.translate • p.initial.value

/-- Terminal endpoint after translating the axis. -/
def terminalValue (p : AxisSegment h x f) : X :=
  p.translate • p.terminal.value

/-- Path length of the oriented segment. -/
def length (p : AxisSegment h x f) : ℝ :=
  p.terminal.coordinate - p.initial.coordinate

theorem length_nonneg (p : AxisSegment h x f) : 0 ≤ p.length :=
  sub_nonneg.mpr p.oriented

/-- Both endpoints lie on the translated quasi-axis carrier. -/
theorem endpoints_mem_translated_quasiAxis (p : AxisSegment h x f) :
    p.initialValue ∈ (fun y : X => p.translate • y) '' quasiAxis h x f ∧
      p.terminalValue ∈ (fun y : X => p.translate • y) '' quasiAxis h x f := by
  exact ⟨⟨p.initial.value, p.initial.value_mem_quasiAxis, rfl⟩,
    ⟨p.terminal.value, p.terminal.value_mem_quasiAxis, rfl⟩⟩

/-- DGO's oriented endpoint-closeness condition for arbitrary translated axis
segments. -/
def OrientedClose (B : ℝ) (p q : AxisSegment h x f) : Prop :=
  dist p.initialValue q.initialValue ≤ B ∧
    dist p.terminalValue q.terminalValue ≤ B

theorem orientedClose_comm {B : ℝ} (p q : AxisSegment h x f) :
    OrientedClose B p q ↔ OrientedClose B q p := by
  simp only [OrientedClose, dist_comm]

end AxisSegment

/-! ## Oriented power-vertex subsegments -/

/-- A translated, oriented subsegment of the axis whose endpoints are orbit
vertices.  Every sufficiently long segment of the concatenated axis contains
one of these after deleting at most one fundamental connector at each end. -/
structure PowerAxisSegment (h : G) (x : X) where
  translate : G
  start : ℤ
  stop : ℤ
  start_le_stop : start ≤ stop

namespace PowerAxisSegment

variable {h : G} {x : X}

/-- Initial endpoint of an oriented translated power-axis segment. -/
def initial (p : PowerAxisSegment h x) : X :=
  (p.translate * h ^ p.start) • x

/-- Terminal endpoint of an oriented translated power-axis segment. -/
def terminal (p : PowerAxisSegment h x) : X :=
  (p.translate * h ^ p.stop) • x

/-- Path length: the number of fundamental connectors times their common
length. -/
def length (p : PowerAxisSegment h x) : ℝ :=
  ((p.stop - p.start : ℤ) : ℝ) * dist x (h • x)

/-- Arclength coordinate of the initial power vertex. -/
def initialCoordinate (p : PowerAxisSegment h x) : ℝ :=
  (p.start : ℝ) * dist x (h • x)

/-- Arclength coordinate of the terminal power vertex. -/
def terminalCoordinate (p : PowerAxisSegment h x) : ℝ :=
  (p.stop : ℝ) * dist x (h • x)

/-- The conjugate whose axis is the translated axis carrying the segment. -/
def conjugate (p : PowerAxisSegment h x) : G :=
  p.translate * h * p.translate⁻¹

/-- Number of fundamental connectors in a power-vertex segment. -/
def steps (p : PowerAxisSegment h x) : ℕ :=
  (p.stop - p.start).toNat

omit [Group G] [PseudoMetricSpace X] [MulAction G X] in
/-- The natural step count represents the oriented integer difference. -/
theorem steps_cast (p : PowerAxisSegment h x) :
    (p.steps : ℤ) = p.stop - p.start := by
  exact Int.toNat_of_nonneg (sub_nonneg.mpr p.start_le_stop)

omit [PseudoMetricSpace X] in
/-- The terminal vertex is obtained from the initial vertex by the positive
natural power of the conjugate recorded by the segment. -/
theorem terminal_eq_pow_smul_initial (p : PowerAxisSegment h x) :
    p.terminal = (p.conjugate ^ p.steps) • p.initial := by
  have hpow : p.conjugate ^ p.steps =
      p.conjugate ^ (p.stop - p.start : ℤ) := by
    calc
      p.conjugate ^ p.steps = p.conjugate ^ (p.steps : ℤ) := by
        rw [zpow_natCast]
      _ = p.conjugate ^ (p.stop - p.start : ℤ) := by rw [p.steps_cast]
  rw [hpow]
  dsimp [terminal, initial, conjugate]
  rw [← mul_smul]
  congr 1
  rw [conj_zpow]
  group

/-- Path length is the natural step count times the connector length. -/
theorem length_eq_steps_mul (p : PowerAxisSegment h x) :
    p.length = (p.steps : ℝ) * dist x (h • x) := by
  have hcast : (p.steps : ℝ) = ((p.stop - p.start : ℤ) : ℝ) := by
    exact_mod_cast p.steps_cast
  rw [length, hcast]

/-- The path length of an oriented power-axis segment is nonnegative. -/
theorem length_nonneg (p : PowerAxisSegment h x) : 0 ≤ p.length := by
  exact mul_nonneg (by exact_mod_cast sub_nonneg.mpr p.start_le_stop) dist_nonneg

/-- A quasi-geodesic lower bound on the axis gives the corresponding metric
displacement lower bound for every translated power-vertex segment. -/
theorem length_div_sub_le_dist
    (hiso : IsIsometricAction G X) {f : ℝ → X}
    (hf : IsAxisConnector h x f) {lam c : ℝ}
    (hq : IsQuasiGeodesicAxis lam c h x f)
    (p : PowerAxisSegment h x) :
    p.length / lam - c ≤ dist p.initial p.terminal := by
  let a : AxisPoint h x f :=
    { index := p.start
      parameter := 0
      parameter_mem := ⟨le_rfl, dist_nonneg⟩ }
  let b : AxisPoint h x f :=
    { index := p.stop
      parameter := 0
      parameter_mem := ⟨le_rfl, dist_nonneg⟩ }
  have hab := (hq a b).1
  have hcoord : |a.coordinate - b.coordinate| = p.length := by
    dsimp [a, b, AxisPoint.coordinate, length]
    push_cast
    rw [abs_of_nonpos]
    · ring
    · have hsub : (p.start : ℝ) - (p.stop : ℝ) ≤ 0 := by
        exact_mod_cast sub_nonpos.mpr p.start_le_stop
      simpa only [add_zero, sub_mul] using
        mul_nonpos_of_nonpos_of_nonneg hsub
          (dist_nonneg : 0 ≤ dist x (h • x))
  have hvalue : dist p.initial p.terminal = dist a.value b.value := by
    dsimp [initial, terminal, a, b, AxisPoint.value]
    rw [hf.2.1]
    simpa only [mul_smul] using
      hiso p.translate ((h ^ p.start) • x) ((h ^ p.stop) • x)
  rwa [hcoord, ← hvalue] at hab

/-! ## From oriented power cores to WPD fellow travel -/

/-- DGO's oriented endpoint-closeness condition for two power-vertex
subsegments. -/
def OrientedClose (B : ℝ) (p q : PowerAxisSegment h x) : Prop :=
  dist p.initial q.initial ≤ B ∧ dist p.terminal q.terminal ≤ B

/-- Two oriented-close power-axis segments determine forward geodesic chords
from the first initial endpoint whose terminal points are `2B`-close.  The WPD
long-fellow-travel argument therefore gives a common nonzero power of the two
axis conjugates once both metric displacements exceed a suitable threshold.

This is deliberately a nonzero-power statement.  The positive-power
conclusion of DGO Lemma 6.7 additionally uses the monotone sampling supplied
by the orientation of a quasi-axis. -/
theorem exists_common_zpow_of_long_orientedClose
    {δ B : ℝ} (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ)
    (hgeo : IsGeodesicSpace X) (hiso : IsIsometricAction G X)
    (hlox : IsLoxodromic h x) (hwpd : IsWPDAt h x) (hB : 0 ≤ B)
    (p q : PowerAxisSegment h x) :
    ∃ T : ℝ, 0 < T ∧
      (T ≤ dist p.initial p.terminal →
       T ≤ dist q.initial q.terminal →
       OrientedClose B p q →
       ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧
         p.conjugate ^ a = q.conjugate ^ b) := by
  let z : X := p.initial
  let a : G := p.conjugate
  let b : G := q.conjugate
  have hh_z : IsLoxodromic h z :=
    isLoxodromic_of_isLoxodromic hiso hlox
  have ha : IsLoxodromic a z := by
    dsimp [a]
    exact isLoxodromic_conj hiso hh_z
  have hb : IsLoxodromic b z := by
    dsimp [b]
    exact isLoxodromic_conj hiso hh_z
  let u : G := p.translate * h ^ p.start
  have huPoint : u • x = z := by
    rfl
  have huConj : u * h * u⁻¹ = a := by
    dsimp [u, a, conjugate]
    group
  have haWPD : IsWPDAt a z := by
    have hw := hwpd.conj hiso u
    rwa [huConj, huPoint] at hw
  let C : ℝ := 2 * (2 * B + 6 * δ)
  have hC : 0 ≤ C := by
    dsimp [C]
    linarith
  obtain ⟨T, hT, hlong⟩ :=
    ElementaryMorse.exists_common_zpow_of_forward_fellow_travel_of_wpd_bound
      hδ hδ0 hgeo hiso hC ha hb haWPD
  let M : ℝ := T + 2 * B
  have hM : 0 < M := by
    dsimp [M]
    linarith
  refine ⟨M, hM, ?_⟩
  intro hpLong hqLong hclose
  rcases hclose with ⟨hclose0, hclose1⟩
  obtain ⟨gp, hgp, hgp0, hgp1⟩ := hgeo z ((a ^ p.steps) • z)
  obtain ⟨gq, hgq, hgq0, hgq1⟩ := hgeo z ((b ^ q.steps) • z)
  have hpTerminal : (a ^ p.steps) • z = p.terminal := by
    dsimp [a, z]
    exact p.terminal_eq_pow_smul_initial.symm
  have hqTerminal : (b ^ q.steps) • q.initial = q.terminal := by
    dsimp [b]
    exact q.terminal_eq_pow_smul_initial.symm
  have hqShift : dist ((b ^ q.steps) • z) q.terminal ≤ B := by
    rw [← hqTerminal, hiso]
    exact hclose0
  have hend : dist ((a ^ p.steps) • z) ((b ^ q.steps) • z) ≤ 2 * B := by
    rw [hpTerminal]
    have htri := dist_triangle p.terminal q.terminal ((b ^ q.steps) • z)
    have hshift : dist q.terminal ((b ^ q.steps) • z) ≤ B := by
      rwa [dist_comm]
    linarith
  have hpMetric : T ≤ dist z ((a ^ p.steps) • z) := by
    rw [hpTerminal]
    dsimp [M] at hpLong
    linarith
  have hqMetric : T ≤ dist z ((b ^ q.steps) • z) := by
    have hstart : dist q.initial z ≤ B := by
      dsimp [z]
      rwa [dist_comm]
    have hchain := dist_triangle4 q.initial z ((b ^ q.steps) • z) q.terminal
    dsimp [M] at hqLong
    linarith
  apply hlong p.steps q.steps gp gq hgp hgp0 hgp1 hgq hgq0 hgq1
    hpMetric hqMetric
  intro t ht0 htT
  have hendGeodesic :
      dist (gp (dist z ((a ^ p.steps) • z)))
        (gq (dist z ((b ^ q.steps) • z))) ≤ 2 * B := by
    rw [hgp1, hgq1]
    exact hend
  apply dist_same_parameter_le_of_geodesic_close_endpoints
    hδ hδ0 hgeo (E := 2 * B) (by linarith) hgp dist_nonneg hgq dist_nonneg
    (by rw [hgp0, hgq0]) hendGeodesic
  · exact ⟨ht0, htT.trans hpMetric⟩
  · exact ⟨ht0, htT.trans hqMetric⟩

/-- The initial endpoint lies on the corresponding translated DGO axis. -/
theorem initial_mem_translated_quasiAxis {f : ℝ → X}
    (hf : IsAxisConnector h x f) (p : PowerAxisSegment h x) :
    p.initial ∈ (fun y : X => p.translate • y) '' quasiAxis h x f := by
  refine ⟨(h ^ p.start) • x, zpow_smul_mem_quasiAxis hf p.start, ?_⟩
  rw [initial, mul_smul]

/-- The terminal endpoint lies on the corresponding translated DGO axis. -/
theorem terminal_mem_translated_quasiAxis {f : ℝ → X}
    (hf : IsAxisConnector h x f) (p : PowerAxisSegment h x) :
    p.terminal ∈ (fun y : X => p.translate • y) '' quasiAxis h x f := by
  refine ⟨(h ^ p.stop) • x, zpow_smul_mem_quasiAxis hf p.stop, ?_⟩
  rw [terminal, mul_smul]

/-- Oriented closeness is symmetric in the two segments. -/
theorem orientedClose_comm {B : ℝ} (p q : PowerAxisSegment h x) :
    OrientedClose B p q ↔ OrientedClose B q p := by
  simp only [OrientedClose, dist_comm]

/-- The exact conclusion of DGO Lemma 6.7 for the conjugates corresponding to
two translated axis segments. -/
def ConjugatesHaveEqualPositivePowers (p q : PowerAxisSegment h x) : Prop :=
  ∃ a b : ℤ, 0 < a ∧ 0 < b ∧ p.conjugate ^ a = q.conjugate ^ b

/-! ## Trimming arbitrary segments to power vertices -/

/-- Deleting at most one fundamental connector at each end of an arbitrary
axis segment leaves a power-vertex subsegment.  If the original length is at
least `M + 2D`, where `D = d(x,hx)`, the retained core has length at least
`M`. -/
theorem exists_powerCore_of_add_two_step_le_length
    (hiso : IsIsometricAction G X) {f : ℝ → X}
    (hf : IsAxisConnector h x f) (hstep : 0 < dist x (h • x))
    {M : ℝ} (hM : 0 ≤ M)
    (p : AxisSegment h x f)
    (hlong : M + 2 * dist x (h • x) ≤ p.length) :
    ∃ q : PowerAxisSegment h x,
      q.translate = p.translate ∧
      p.initial.coordinate ≤ q.initialCoordinate ∧
      q.terminalCoordinate ≤ p.terminal.coordinate ∧
      dist p.initialValue q.initial ≤ dist x (h • x) ∧
      dist q.terminal p.terminalValue ≤ dist x (h • x) ∧
      M ≤ q.length := by
  let D : ℝ := dist x (h • x)
  let i : ℤ := p.initial.index
  let j : ℤ := p.terminal.index
  let s : ℝ := p.initial.parameter
  let t : ℝ := p.terminal.parameter
  have hs0 : 0 ≤ s := p.initial.parameter_mem.1
  have hsD : s ≤ D := p.initial.parameter_mem.2
  have ht0 : 0 ≤ t := p.terminal.parameter_mem.1
  have htD : t ≤ D := p.terminal.parameter_mem.2
  let coreLength : ℝ := (((j - (i + 1) : ℤ) : ℤ) : ℝ) * D
  have hlength : p.length = coreLength + (D + t - s) := by
    dsimp [AxisSegment.length, AxisPoint.coordinate, coreLength, D, i, j, s, t]
    push_cast
    ring
  have htrim : p.length ≤ coreLength + 2 * D := by
    rw [hlength]
    linarith
  have hMcore : M ≤ coreLength := by
    linarith
  have hcore0 : 0 ≤ coreLength := le_trans hM hMcore
  have hcoeff0 : 0 ≤ (((j - (i + 1) : ℤ) : ℤ) : ℝ) := by
    by_contra hneg
    push Not at hneg
    have : coreLength < 0 := by
      dsimp [coreLength]
      exact mul_neg_of_neg_of_pos hneg hstep
    linarith
  have hdiff : 0 ≤ j - (i + 1) := by exact_mod_cast hcoeff0
  have hij : i + 1 ≤ j := by omega
  let q : PowerAxisSegment h x :=
    { translate := p.translate
      start := i + 1
      stop := j
      start_le_stop := hij }
  have hsmetric : dist (f s) (h • x) = D - s := by
    have hdist := hf.1 s p.initial.parameter_mem D ⟨dist_nonneg, le_rfl⟩
    rw [hf.2.2, abs_of_nonpos (sub_nonpos.mpr hsD)] at hdist
    linarith
  have htmetric : dist x (f t) = t := by
    have hdist := hf.1 0 ⟨le_rfl, dist_nonneg⟩ t p.terminal.parameter_mem
    rw [hf.2.1, abs_of_nonpos (by linarith [ht0])] at hdist
    linarith
  have hpinitial : p.initialValue = (p.translate * h ^ i) • f s := by
    dsimp [AxisSegment.initialValue, AxisPoint.value, i, s]
    rw [mul_smul]
  have hqinitial : q.initial = (p.translate * h ^ i) • (h • x) := by
    dsimp [q, PowerAxisSegment.initial]
    rw [← mul_smul]
    congr 1
    group
  have hqterminal : q.terminal = (p.translate * h ^ j) • x := by
    rfl
  have hpterminal : p.terminalValue = (p.translate * h ^ j) • f t := by
    dsimp [AxisSegment.terminalValue, AxisPoint.value, j, t]
    rw [mul_smul]
  have hinitialDist : dist p.initialValue q.initial ≤ D := by
    rw [hpinitial, hqinitial, hiso, hsmetric]
    linarith
  have hterminalDist : dist q.terminal p.terminalValue ≤ D := by
    rw [hqterminal, hpterminal, hiso, htmetric]
    exact htD
  refine ⟨q, rfl, ?_, ?_, hinitialDist, hterminalDist, ?_⟩
  · dsimp [q, PowerAxisSegment.initialCoordinate, AxisPoint.coordinate, i, s, D]
    push_cast
    linarith
  · dsimp [q, PowerAxisSegment.terminalCoordinate, AxisPoint.coordinate, j, t, D]
    linarith
  · change M ≤ (((j - (i + 1) : ℤ) : ℝ) * D)
    exact hMcore

/-- Trimming both members of an oriented-close pair costs at most one
fundamental connector at each endpoint.  The retained power-vertex cores stay
oriented `(B + 2D)`-close and retain the requested length. -/
theorem exists_orientedClose_powerCores
    (hiso : IsIsometricAction G X) {f : ℝ → X}
    (hf : IsAxisConnector h x f) (hstep : 0 < dist x (h • x))
    {M B : ℝ} (hM : 0 ≤ M) (p q : AxisSegment h x f)
    (hpLen : M + 2 * dist x (h • x) ≤ p.length)
    (hqLen : M + 2 * dist x (h • x) ≤ q.length)
    (hclose : AxisSegment.OrientedClose B p q) :
    ∃ p' q' : PowerAxisSegment h x,
      M ≤ p'.length ∧ M ≤ q'.length ∧
      OrientedClose (B + 2 * dist x (h • x)) p' q' := by
  obtain ⟨p', -, -, -, hp0, hp1, hpLen'⟩ :=
    exists_powerCore_of_add_two_step_le_length hiso hf hstep hM p hpLen
  obtain ⟨q', -, -, -, hq0, hq1, hqLen'⟩ :=
    exists_powerCore_of_add_two_step_le_length hiso hf hstep hM q hqLen
  refine ⟨p', q', hpLen', hqLen', ?_⟩
  constructor
  · have htri := dist_triangle4 p'.initial p.initialValue q.initialValue q'.initial
    rw [dist_comm p'.initial p.initialValue] at htri
    linarith [hp0, hq0, hclose.1]
  · have htri := dist_triangle4 p'.terminal p.terminalValue q.terminalValue q'.terminal
    rw [dist_comm q.terminalValue q'.terminal] at htri
    linarith [hp1, hq1, hclose.2]

end PowerAxisSegment

end GGT
end GroupApproximation
