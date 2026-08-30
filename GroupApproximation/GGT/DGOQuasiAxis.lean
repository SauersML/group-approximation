import GroupApproximation.GGT.DGOLemma67Pigeonhole

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

/-- The path length of an oriented power-axis segment is nonnegative. -/
theorem length_nonneg (p : PowerAxisSegment h x) : 0 ≤ p.length := by
  exact mul_nonneg (by exact_mod_cast sub_nonneg.mpr p.start_le_stop) dist_nonneg

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

/-- DGO's oriented endpoint-closeness condition for two power-vertex
subsegments. -/
def OrientedClose (B : ℝ) (p q : PowerAxisSegment h x) : Prop :=
  dist p.initial q.initial ≤ B ∧ dist p.terminal q.terminal ≤ B

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
theorem AxisSegment.exists_powerCore_of_add_two_step_le_length
    {f : ℝ → X} (hstep : 0 < dist x (h • x)) {M : ℝ} (hM : 0 ≤ M)
    (p : AxisSegment h x f)
    (hlong : M + 2 * dist x (h • x) ≤ p.length) :
    ∃ q : PowerAxisSegment h x,
      q.translate = p.translate ∧
      p.initial.coordinate ≤ q.initialCoordinate ∧
      q.terminalCoordinate ≤ p.terminal.coordinate ∧
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
  refine ⟨q, rfl, ?_, ?_, ?_⟩
  · dsimp [q, PowerAxisSegment.initialCoordinate, AxisPoint.coordinate, i, s, D]
    push_cast
    linarith
  · dsimp [q, PowerAxisSegment.terminalCoordinate, AxisPoint.coordinate, j, t, D]
    linarith
  · change M ≤ (((j - (i + 1) : ℤ) : ℝ) * D)
    exact hMcore

end PowerAxisSegment

end GGT
end GroupApproximation
