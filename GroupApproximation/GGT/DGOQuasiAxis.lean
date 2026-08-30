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

end PowerAxisSegment

end GGT
end GroupApproximation
