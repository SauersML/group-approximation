import GroupApproximation.GGT.ElementaryIndependence
import Mathlib.Combinatorics.Pigeonhole

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

/-- A unit-speed geodesic parametrization of an axis on which `h` acts by
translation through the fundamental displacement `d(x,hx)`.  This is the
axial case treated explicitly in the proof of Bestvina--Fujiwara,
Proposition 6. -/
def IsParametrizedAxis (h : G) (x : X) (a : ℝ → X) : Prop :=
  a 0 = x ∧
    (∀ s t : ℝ, dist (a s) (a t) = |s - t|) ∧
    ∀ (n : ℤ) (t : ℝ),
      (h ^ n) • a t = a (t + (n : ℝ) * dist x (h • x))

/-- A global parametrized axis restricts to the fundamental connector used in
DGO Definition 6.3. -/
theorem IsParametrizedAxis.isAxisConnector {h : G} {x : X} {a : ℝ → X}
    (ha : IsParametrizedAxis h x a) : IsAxisConnector h x a := by
  refine ⟨?_, ha.1, ?_⟩
  · intro s hs t ht
    exact ha.2.1 s t
  · simpa [ha.1] using (ha.2.2 (1 : ℤ) 0).symm

/-- The concatenated-axis coordinates induced by a global parametrized axis
are a `(1,0)`-quasi-geodesic (in fact, an isometric embedding). -/
theorem IsParametrizedAxis.isQuasiGeodesicAxis {h : G} {x : X} {a : ℝ → X}
    (ha : IsParametrizedAxis h x a) : IsQuasiGeodesicAxis 1 0 h x a := by
  intro p q
  have hp : p.value = a p.coordinate := by
    dsimp [AxisPoint.value, AxisPoint.coordinate]
    rw [ha.2.2]
    congr 1
    ring
  have hq : q.value = a q.coordinate := by
    dsimp [AxisPoint.value, AxisPoint.coordinate]
    rw [ha.2.2]
    congr 1
    ring
  rw [hp, hq, ha.2.1]
  constructor <;> norm_num

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

/-- The conjugate corresponding to the translated axis carrying the segment. -/
def conjugate (p : AxisSegment h x f) : G :=
  p.translate * h * p.translate⁻¹

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

/-- A finite map into a nonempty set of colors has a constant increasing
subsequence of the requested size once the source has `colors × size`
elements.  The increasing enumeration is important for preserving the order
of the geometric samples. -/
theorem exists_constant_strictMono_subsequence
    (colors : Finset ℤ) (hcolors : colors.Nonempty) (N : ℕ)
    (φ : Fin (colors.card * (N + 1)) → ℤ)
    (hφ : ∀ r, φ r ∈ colors) :
    ∃ z ∈ colors, ∃ R : Fin (N + 1) → Fin (colors.card * (N + 1)),
      StrictMono R ∧ ∀ i, φ (R i) = z := by
  obtain ⟨z, hz, hfiber⟩ :=
    Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
      (s := Finset.univ) (t := colors) (f := φ)
      (fun r hr => hφ r) hcolors (n := N + 1) (by simp)
  let fiber : Finset (Fin (colors.card * (N + 1))) :=
    Finset.univ.filter fun r => φ r = z
  have hfiberCard : N + 1 ≤ fiber.card := by
    exact hfiber
  obtain ⟨chosen, hchosen, hchosenCard⟩ :=
    fiber.exists_subset_card_eq hfiberCard
  let R : Fin (N + 1) → Fin (colors.card * (N + 1)) :=
    fun i => (chosen.orderIsoOfFin hchosenCard i).1
  have hRmono : StrictMono R := by
    intro i j hij
    exact (chosen.orderIsoOfFin hchosenCard).strictMono hij
  refine ⟨z, hz, R, hRmono, ?_⟩
  intro i
  have hmemChosen : (chosen.orderIsoOfFin hchosenCard i).1 ∈ chosen :=
    (chosen.orderIsoOfFin hchosenCard i).2
  have hmemFiber := hchosen hmemChosen
  exact (Finset.mem_filter.mp hmemFiber).2

/-- The unit-speed path on a translated parametrized axis beginning at the
initial vertex of a power-axis segment. -/
def parametrizedPath (a : ℝ → X) (p : PowerAxisSegment h x) : ℝ → X :=
  fun t => p.translate • a ((p.start : ℝ) * dist x (h • x) + t)

/-- Power vertex on the translated axis at an arbitrary integer coordinate. -/
def vertex (p : PowerAxisSegment h x) (n : ℤ) : X :=
  (p.translate * h ^ n) • x

/-- The finite orbit-vertex chain carried by a power-axis segment. -/
def vertexChain (p : PowerAxisSegment h x) : ℕ → X :=
  fun n => p.vertex (p.start + (n : ℤ))

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

omit [PseudoMetricSpace X] in
/-- Powers of the translated-axis conjugate advance its integer vertex
coordinate by the same amount. -/
theorem conjugate_zpow_smul_vertex (p : PowerAxisSegment h x) (k n : ℤ) :
    (p.conjugate ^ k) • p.vertex n = p.vertex (n + k) := by
  dsimp [conjugate, vertex]
  rw [← mul_smul]
  congr 1
  rw [conj_zpow]
  group

omit [PseudoMetricSpace X] in
/-- The preceding translation identity based at the segment's initial
vertex. -/
theorem conjugate_zpow_smul_initial (p : PowerAxisSegment h x) (k : ℤ) :
    (p.conjugate ^ k) • p.initial = p.vertex (p.start + k) := by
  exact p.conjugate_zpow_smul_vertex k p.start

/-- Path length is the natural step count times the connector length. -/
theorem length_eq_steps_mul (p : PowerAxisSegment h x) :
    p.length = (p.steps : ℝ) * dist x (h • x) := by
  have hcast : (p.steps : ℝ) = ((p.stop - p.start : ℤ) : ℝ) := by
    exact_mod_cast p.steps_cast
  rw [length, hcast]

/-- The path length of an oriented power-axis segment is nonnegative. -/
theorem length_nonneg (p : PowerAxisSegment h x) : 0 ≤ p.length := by
  exact mul_nonneg (by exact_mod_cast sub_nonneg.mpr p.start_le_stop) dist_nonneg

omit [PseudoMetricSpace X] in
/-- The vertex chain begins at the initial power vertex. -/
theorem vertexChain_zero (p : PowerAxisSegment h x) :
    p.vertexChain 0 = p.initial := by
  simp [vertexChain, initial, vertex]

omit [PseudoMetricSpace X] in
/-- The last recorded vertex of the chain is the terminal power vertex. -/
theorem vertexChain_steps (p : PowerAxisSegment h x) :
    p.vertexChain p.steps = p.terminal := by
  have hindex : p.start + (p.steps : ℤ) = p.stop := by
    rw [p.steps_cast]
    omega
  simp only [vertexChain, hindex, terminal, vertex]

/-- A parametrized axis restricts to a geodesic path of the recorded segment
length on every translated power-axis segment. -/
theorem isGeodesicSegment_parametrizedPath
    (hiso : IsIsometricAction G X) {a : ℝ → X}
    (ha : IsParametrizedAxis h x a) (p : PowerAxisSegment h x) :
    IsGeodesicSegment (parametrizedPath a p) 0 p.length := by
  intro s hs t ht
  dsimp [parametrizedPath]
  rw [hiso, ha.2.1]
  congr 1
  ring

/-- Integer multiples of the fundamental displacement on a parametrized
segment are exactly its translated power vertices. -/
theorem parametrizedPath_eq_vertex
    {a : ℝ → X} (ha : IsParametrizedAxis h x a)
    (p : PowerAxisSegment h x) (n : ℤ) :
    parametrizedPath a p ((n : ℝ) * dist x (h • x)) =
      p.vertex (p.start + n) := by
  have haxis :
      a (((p.start + n : ℤ) : ℝ) * dist x (h • x)) =
        (h ^ (p.start + n)) • x := by
    simpa [ha.1] using (ha.2.2 (p.start + n) 0).symm
  dsimp [parametrizedPath]
  rw [show (p.start : ℝ) * dist x (h • x) +
      (n : ℝ) * dist x (h • x) =
      ((p.start + n : ℤ) : ℝ) * dist x (h • x) by
        push_cast
        ring]
  rw [haxis]
  rw [vertex, mul_smul]

/-- The translated parametrized path starts at the segment's initial vertex. -/
theorem parametrizedPath_zero
    {a : ℝ → X} (ha : IsParametrizedAxis h x a)
    (p : PowerAxisSegment h x) :
    parametrizedPath a p 0 = p.initial := by
  simpa [initial, vertex] using parametrizedPath_eq_vertex ha p 0

/-- The translated parametrized path ends at the segment's terminal vertex. -/
theorem parametrizedPath_length
    {a : ℝ → X} (ha : IsParametrizedAxis h x a)
    (p : PowerAxisSegment h x) :
    parametrizedPath a p p.length = p.terminal := by
  simpa [length, terminal, vertex] using
    parametrizedPath_eq_vertex ha p (p.stop - p.start)

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

/-- The quasi-geodesic inequalities on the carrier, transported to arbitrary
integer power vertices of any translated axis. -/
theorem vertex_dist_bounds
    (hiso : IsIsometricAction G X) {f : ℝ → X}
    (hf : IsAxisConnector h x f) {lam c : ℝ}
    (hq : IsQuasiGeodesicAxis lam c h x f)
    (p : PowerAxisSegment h x) (i j : ℤ) :
    |((i : ℝ) - (j : ℝ)) * dist x (h • x)| / lam - c ≤
        dist (p.vertex i) (p.vertex j) ∧
      dist (p.vertex i) (p.vertex j) ≤
        lam * |((i : ℝ) - (j : ℝ)) * dist x (h • x)| + c := by
  let a : AxisPoint h x f :=
    { index := i
      parameter := 0
      parameter_mem := ⟨le_rfl, dist_nonneg⟩ }
  let b : AxisPoint h x f :=
    { index := j
      parameter := 0
      parameter_mem := ⟨le_rfl, dist_nonneg⟩ }
  have hab := hq a b
  have hcoord : a.coordinate - b.coordinate =
      ((i : ℝ) - (j : ℝ)) * dist x (h • x) := by
    dsimp [a, b, AxisPoint.coordinate]
    ring
  have hvalue : dist (p.vertex i) (p.vertex j) = dist a.value b.value := by
    dsimp [vertex, a, b, AxisPoint.value]
    rw [hf.2.1]
    simpa only [mul_smul] using
      hiso p.translate ((h ^ i) • x) ((h ^ j) • x)
  rwa [hcoord, ← hvalue] at hab

/-- Successive vertices inherit the uniform upper bound from the
parametrized quasi-axis. -/
theorem vertexChain_edge_le
    (hiso : IsIsometricAction G X) {f : ℝ → X}
    (hf : IsAxisConnector h x f) {lam c : ℝ}
    (hq : IsQuasiGeodesicAxis lam c h x f)
    (p : PowerAxisSegment h x) (n : ℕ) :
    dist (p.vertexChain n) (p.vertexChain (n + 1)) ≤
      lam * dist x (h • x) + c := by
  have hupper := (vertex_dist_bounds hiso hf hq p
    (p.start + (n : ℤ)) (p.start + ((n + 1 : ℕ) : ℤ))).2
  have hcoord :
      |((((p.start + (n : ℤ) : ℤ) : ℝ) -
          ((p.start + ((n + 1 : ℕ) : ℤ) : ℤ) : ℝ)) *
        dist x (h • x))| = dist x (h • x) := by
    push_cast
    rw [show ((p.start : ℝ) + (n : ℝ) -
        ((p.start : ℝ) + ((n : ℝ) + 1))) * dist x (h • x) =
        -(dist x (h • x)) by ring, abs_neg, abs_of_nonneg dist_nonneg]
  rw [hcoord] at hupper
  simpa only [vertexChain] using hupper

/-- The quasi-axis lower bound gives uniform linear progress along every
finite vertex chain. -/
theorem vertexChain_progress
    (hiso : IsIsometricAction G X) {f : ℝ → X}
    (hf : IsAxisConnector h x f) {lam c : ℝ}
    (hq : IsQuasiGeodesicAxis lam c h x f)
    (p : PowerAxisSegment h x) {i j : ℕ} (hij : i ≤ j) :
    (dist x (h • x) / lam) * ((j - i : ℕ) : ℝ) - c ≤
      dist (p.vertexChain i) (p.vertexChain j) := by
  have hlower := (vertex_dist_bounds hiso hf hq p
    (p.start + (i : ℤ)) (p.start + (j : ℤ))).1
  have hcoord :
      |((((p.start + (i : ℤ) : ℤ) : ℝ) -
          ((p.start + (j : ℤ) : ℤ) : ℝ)) * dist x (h • x))| =
        ((j - i : ℕ) : ℝ) * dist x (h • x) := by
    have hcast : ((j - i : ℕ) : ℝ) = (j : ℝ) - (i : ℝ) := by
      rw [Nat.cast_sub hij]
    push_cast
    rw [show ((p.start : ℝ) + (i : ℝ) -
        ((p.start : ℝ) + (j : ℝ))) * dist x (h • x) =
        -(((j : ℝ) - (i : ℝ)) * dist x (h • x)) by ring,
      abs_neg, abs_of_nonneg (mul_nonneg (sub_nonneg.mpr (by exact_mod_cast hij))
        dist_nonneg), hcast]
  rw [hcoord] at hlower
  have hreorder :
      (dist x (h • x) / lam) * ((j - i : ℕ) : ℝ) =
        ((j - i : ℕ) : ℝ) * dist x (h • x) / lam := by ring
  rw [hreorder]
  simpa only [vertexChain] using hlower

/-- Endpoint-close finite quasi-geodesic chains coarsely match every vertex
that lies uniformly far from the terminal endpoint.  This is the chain-level
Morse comparison underlying both orientations of the quasi-axis overlap
argument. -/
theorem exists_uniform_chain_match
    {δ B D l c : ℝ} (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ)
    (hgeo : IsGeodesicSpace X) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hl : 0 < l) (hc : 0 ≤ c) :
    ∃ E C : ℝ, 0 ≤ E ∧ 0 ≤ C ∧
      ∀ (Psteps Qsteps : ℕ) (p q : ℕ → X),
        (∀ i, i < Psteps → dist (p i) (p (i + 1)) ≤ D) →
        (∀ i k, i ≤ k → k ≤ Psteps →
          l * ((k - i : ℕ) : ℝ) - c ≤ dist (p i) (p k)) →
        (∀ i, i < Qsteps → dist (q i) (q (i + 1)) ≤ D) →
        (∀ i k, i ≤ k → k ≤ Qsteps →
          l * ((k - i : ℕ) : ℝ) - c ≤ dist (q i) (q k)) →
        dist (p 0) (q 0) ≤ B → dist (p Psteps) (q Qsteps) ≤ B →
        ∀ j : ℕ, j ≤ Psteps →
          E ≤ l * ((Psteps - j : ℕ) : ℝ) →
          ∃ i : ℕ, i ≤ Qsteps ∧ dist (p j) (q i) ≤ C := by
  obtain ⟨K₁, hK₁, hchordNear⟩ :=
    ElementaryMorse.exists_bound_chord_near_chain
      hδ hδ0 hD hl hc
  obtain ⟨K₂, hK₂, hchainNear⟩ :=
    ElementaryMorse.exists_bound_chain_near_chord
      hδ hδ0 hD hl hc
  let E : ℝ := 2 * B + c + K₂
  let C : ℝ := K₂ + (3 * B + 12 * δ) + K₁
  have hE : 0 ≤ E := by
    dsimp [E]
    linarith
  have hC : 0 ≤ C := by
    dsimp [C]
    linarith
  refine ⟨E, C, hE, hC, ?_⟩
  intro Psteps Qsteps p q hpEdge hpProgress hqEdge hqProgress
    hclose0 hclose1 j hj hfar
  let Lp : ℝ := dist (p 0) (p Psteps)
  let Lq : ℝ := dist (q 0) (q Qsteps)
  obtain ⟨P, hP, hP0, hP1⟩ := hgeo (p 0) (p Psteps)
  obtain ⟨Q, hQ, hQ0, hQ1⟩ := hgeo (q 0) (q Qsteps)
  obtain ⟨t, ht, hpClose⟩ := hchainNear p Psteps hpEdge hpProgress
    Lp dist_nonneg P hP hP0 hP1 j hj
  have hlength : Lp ≤ Lq + 2 * B := by
    have htri := dist_triangle4 (p 0) (q 0) (q Qsteps) (p Psteps)
    rw [dist_comm (q Qsteps) (p Psteps)] at htri
    dsimp [Lp, Lq]
    linarith
  have hpTail := hpProgress j Psteps hj le_rfl
  have htailMetric : dist (p j) (p Psteps) ≤ K₂ + (Lp - t) := by
    have hparam : dist (P t) (P Lp) = Lp - t := by
      rw [hP.dist_eq ht ⟨dist_nonneg, le_rfl⟩,
        abs_of_nonpos (sub_nonpos.mpr ht.2)]
      ring
    calc
      dist (p j) (p Psteps) = dist (p j) (P Lp) := by rw [hP1]
      _ ≤ dist (p j) (P t) + dist (P t) (P Lp) := dist_triangle _ _ _
      _ = dist (p j) (P t) + (Lp - t) := by rw [hparam]
      _ ≤ K₂ + (Lp - t) := by
        simpa only [add_comm] using add_le_add_right hpClose (Lp - t)
  have htLq : t ≤ Lq := by
    dsimp [E] at hfar
    linarith
  have hgeodesicClose := dist_same_parameter_le_of_geodesic_endpoints_close
    hδ hδ0 hgeo hB hP dist_nonneg hQ dist_nonneg
    (by rw [hP0, hQ0]; exact hclose0)
    (by rw [hP1, hQ1]; exact hclose1)
    ht ⟨ht.1, htLq⟩
  obtain ⟨i, hi, hqClose⟩ := hchordNear q Qsteps hqEdge hqProgress
    Lq dist_nonneg Q hQ hQ0 hQ1 t ⟨ht.1, htLq⟩
  refine ⟨i, hi, ?_⟩
  have htri := dist_triangle4 (p j) (P t) (Q t) (q i)
  rw [dist_comm (Q t) (q i)] at htri
  dsimp [C]
  linarith

/-- Endpoint-close quasi-axis segments coarsely match their internal power
vertices.  The constants are chosen before the translated segments.  This is
the segment-Morse replacement for the geodesic-axis comparison in the
quasi-axis part of Bestvina--Fujiwara Proposition 6. -/
theorem exists_uniform_vertexChain_match
    {δ B lam c : ℝ} (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ)
    (hgeo : IsGeodesicSpace X) (hiso : IsIsometricAction G X)
    (hB : 0 ≤ B) (hlam : 0 < lam) (hc : 0 ≤ c)
    {f : ℝ → X} (hf : IsAxisConnector h x f)
    (hq : IsQuasiGeodesicAxis lam c h x f)
    (hstep : 0 < dist x (h • x)) :
    ∃ E C : ℝ, 0 ≤ E ∧ 0 ≤ C ∧
      ∀ (p q : PowerAxisSegment h x),
        dist p.initial q.initial ≤ B → dist p.terminal q.terminal ≤ B →
        ∀ j : ℕ, j ≤ p.steps →
          E ≤ (dist x (h • x) / lam) * ((p.steps - j : ℕ) : ℝ) →
          ∃ i : ℕ, i ≤ q.steps ∧
            dist (p.vertexChain j) (q.vertexChain i) ≤ C := by
  let D : ℝ := lam * dist x (h • x) + c
  let l : ℝ := dist x (h • x) / lam
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  have hl : 0 < l := by
    dsimp [l]
    positivity
  obtain ⟨K₁, hK₁, hchordNear⟩ :=
    ElementaryMorse.exists_bound_chord_near_chain
      hδ hδ0 hD hl hc
  obtain ⟨K₂, hK₂, hchainNear⟩ :=
    ElementaryMorse.exists_bound_chain_near_chord
      hδ hδ0 hD hl hc
  let E : ℝ := 2 * B + c + K₂
  let C : ℝ := K₂ + (3 * B + 12 * δ) + K₁
  have hE : 0 ≤ E := by
    dsimp [E]
    linarith
  have hC : 0 ≤ C := by
    dsimp [C]
    linarith
  refine ⟨E, C, hE, hC, ?_⟩
  intro p q hclose0 hclose1 j hj hfar
  let Lp : ℝ := dist p.initial p.terminal
  let Lq : ℝ := dist q.initial q.terminal
  obtain ⟨P, hP, hP0, hP1⟩ := hgeo p.initial p.terminal
  obtain ⟨Q, hQ, hQ0, hQ1⟩ := hgeo q.initial q.terminal
  have hpEdge : ∀ i, i < p.steps →
      dist (p.vertexChain i) (p.vertexChain (i + 1)) ≤ D := by
    intro i hi
    exact vertexChain_edge_le hiso hf hq p i
  have hpProgress : ∀ i k, i ≤ k → k ≤ p.steps →
      l * ((k - i : ℕ) : ℝ) - c ≤
        dist (p.vertexChain i) (p.vertexChain k) := by
    intro i k hik hk
    exact vertexChain_progress hiso hf hq p hik
  have hqEdge : ∀ i, i < q.steps →
      dist (q.vertexChain i) (q.vertexChain (i + 1)) ≤ D := by
    intro i hi
    exact vertexChain_edge_le hiso hf hq q i
  have hqProgress : ∀ i k, i ≤ k → k ≤ q.steps →
      l * ((k - i : ℕ) : ℝ) - c ≤
        dist (q.vertexChain i) (q.vertexChain k) := by
    intro i k hik hk
    exact vertexChain_progress hiso hf hq q hik
  have hP0' : P 0 = p.vertexChain 0 := by rw [hP0, p.vertexChain_zero]
  have hP1' : P Lp = p.vertexChain p.steps := by
    rw [hP1, p.vertexChain_steps]
  have hQ0' : Q 0 = q.vertexChain 0 := by rw [hQ0, q.vertexChain_zero]
  have hQ1' : Q Lq = q.vertexChain q.steps := by
    rw [hQ1, q.vertexChain_steps]
  obtain ⟨t, ht, hpClose⟩ := hchainNear p.vertexChain p.steps
    hpEdge hpProgress Lp dist_nonneg P hP hP0' hP1' j hj
  have hlength : Lp ≤ Lq + 2 * B := by
    have htri := dist_triangle4 p.initial q.initial q.terminal p.terminal
    rw [dist_comm q.terminal p.terminal] at htri
    dsimp [Lp, Lq]
    linarith [hclose0, hclose1]
  have hpTail := hpProgress j p.steps hj le_rfl
  have htailMetric :
      dist (p.vertexChain j) (p.vertexChain p.steps) ≤ K₂ + (Lp - t) := by
    have hparam : dist (P t) (P Lp) = Lp - t := by
      rw [hP.dist_eq ht ⟨dist_nonneg, le_rfl⟩,
        abs_of_nonpos (sub_nonpos.mpr ht.2)]
      ring
    calc
      dist (p.vertexChain j) (p.vertexChain p.steps) =
          dist (p.vertexChain j) (P Lp) := by rw [hP1']
      _ ≤ dist (p.vertexChain j) (P t) + dist (P t) (P Lp) :=
        dist_triangle _ _ _
      _ = dist (p.vertexChain j) (P t) + (Lp - t) := by rw [hparam]
      _ ≤ K₂ + (Lp - t) := by
        simpa only [add_comm] using add_le_add_right hpClose (Lp - t)
  have htLq : t ≤ Lq := by
    dsimp [E, l] at hfar
    linarith
  have hgeodesicClose := dist_same_parameter_le_of_geodesic_endpoints_close
    hδ hδ0 hgeo hB hP dist_nonneg hQ dist_nonneg
    (by rw [hP0, hQ0]; exact hclose0)
    (by rw [hP1, hQ1]; exact hclose1)
    ht ⟨ht.1, htLq⟩
  obtain ⟨i, hi, hqClose⟩ := hchordNear q.vertexChain q.steps
    hqEdge hqProgress Lq dist_nonneg Q hQ hQ0' hQ1' t ⟨ht.1, htLq⟩
  refine ⟨i, hi, ?_⟩
  have htri := dist_triangle4 (p.vertexChain j) (P t) (Q t) (q.vertexChain i)
  rw [dist_comm (Q t) (q.vertexChain i)] at htri
  dsimp [C]
  linarith

/-- A coarse match controls the two vertex indices in both directions.  This
quantitative order estimate is what turns Morse matches into increasing
families after sufficiently sparse sampling. -/
theorem vertexChain_match_index_bounds
    {B C lam c : ℝ} (hiso : IsIsometricAction G X)
    {f : ℝ → X} (hf : IsAxisConnector h x f)
    (hq : IsQuasiGeodesicAxis lam c h x f)
    (p q : PowerAxisSegment h x) {j i : ℕ}
    (hj : j ≤ p.steps) (hi : i ≤ q.steps)
    (h0 : dist p.initial q.initial ≤ B)
    (hmatch : dist (p.vertexChain j) (q.vertexChain i) ≤ C) :
    let D := lam * dist x (h • x) + c
    let l := dist x (h • x) / lam
    l * (i : ℝ) ≤ B + (j : ℝ) * D + C + c ∧
      l * (j : ℝ) ≤ B + (i : ℝ) * D + C + c := by
  let D : ℝ := lam * dist x (h • x) + c
  let l : ℝ := dist x (h • x) / lam
  have hpEdge : ∀ n, n < p.steps →
      dist (p.vertexChain n) (p.vertexChain (n + 1)) ≤ D := by
    intro n hn
    exact vertexChain_edge_le hiso hf hq p n
  have hqEdge : ∀ n, n < q.steps →
      dist (q.vertexChain n) (q.vertexChain (n + 1)) ≤ D := by
    intro n hn
    exact vertexChain_edge_le hiso hf hq q n
  have hpDist := dist_chain_le_nat_mul p.vertexChain hpEdge
    (N := p.steps) (a := 0) (n := j) (by simpa using hj)
  have hqDist := dist_chain_le_nat_mul q.vertexChain hqEdge
    (N := q.steps) (a := 0) (n := i) (by simpa using hi)
  simp only [zero_add, vertexChain_zero] at hpDist hqDist
  have hpProgress := vertexChain_progress hiso hf hq p (Nat.zero_le j)
  have hqProgress := vertexChain_progress hiso hf hq q (Nat.zero_le i)
  simp only [Nat.sub_zero, vertexChain_zero] at hpProgress hqProgress
  have hqi : dist q.initial (q.vertexChain i) ≤ B + (j : ℝ) * D + C := by
    have htri := dist_triangle4 q.initial p.initial
      (p.vertexChain j) (q.vertexChain i)
    rw [dist_comm q.initial p.initial] at htri
    linarith
  have hpj : dist p.initial (p.vertexChain j) ≤ B + (i : ℝ) * D + C := by
    have htri := dist_triangle4 p.initial q.initial
      (q.vertexChain i) (p.vertexChain j)
    rw [dist_comm (q.vertexChain i) (p.vertexChain j)] at htri
    linarith
  dsimp [l, D]
  constructor <;> linarith

/-- Coarse partners of sufficiently sparse increasing samples occur in the
same order on the second quasi-axis.  The explicit growth condition is kept
separate from the later finite recursive construction. -/
theorem vertexChain_partner_lt_of_sparse
    {B C lam c : ℝ} (hiso : IsIsometricAction G X)
    (hlam : 0 < lam) (hc : 0 ≤ c)
    {f : ℝ → X} (hf : IsAxisConnector h x f)
    (hqAxis : IsQuasiGeodesicAxis lam c h x f)
    (hstep : 0 < dist x (h • x))
    (p q : PowerAxisSegment h x) {j₁ j₂ i₁ i₂ : ℕ}
    (hj₁ : j₁ ≤ p.steps) (hj₂ : j₂ ≤ p.steps)
    (hi₁ : i₁ ≤ q.steps) (hi₂ : i₂ ≤ q.steps)
    (h0 : dist p.initial q.initial ≤ B)
    (hmatch₁ : dist (p.vertexChain j₁) (q.vertexChain i₁) ≤ C)
    (hmatch₂ : dist (p.vertexChain j₂) (q.vertexChain i₂) ≤ C)
    (hsparse :
      let D := lam * dist x (h • x) + c
      let l := dist x (h • x) / lam
      l * (B + C + c) + D * (B + (j₁ : ℝ) * D + C + c) <
        l * (l * (j₂ : ℝ))) :
    i₁ < i₂ := by
  let D : ℝ := lam * dist x (h • x) + c
  let l : ℝ := dist x (h • x) / lam
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  have hl : 0 < l := by
    dsimp [l]
    positivity
  have hb₁ := vertexChain_match_index_bounds hiso hf hqAxis p q
    hj₁ hi₁ h0 hmatch₁
  have hb₂ := vertexChain_match_index_bounds hiso hf hqAxis p q
    hj₂ hi₂ h0 hmatch₂
  dsimp only at hb₁ hb₂ hsparse
  by_contra hnot
  have hii : i₂ ≤ i₁ := Nat.le_of_not_gt hnot
  have hiiR : (i₂ : ℝ) ≤ (i₁ : ℝ) := by exact_mod_cast hii
  have hDi := mul_le_mul_of_nonneg_left hiiR hD
  have hl₂ := mul_le_mul_of_nonneg_left hb₂.2 hl.le
  have hD₁ := mul_le_mul_of_nonneg_left hb₁.1 hD
  nlinarith

/-- A recursively chosen sequence of natural indices sparse enough for the
coarse partner-order estimate.  The maximum also forces strict increase even
when the coarse constants are degenerate. -/
noncomputable def sparseSample (B C c D l : ℝ) : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
      Classical.choose (exists_nat_gt (max (sparseSample B C c D l n : ℝ)
        ((l * (B + C + c) +
          D * (B + (sparseSample B C c D l n : ℝ) * D + C + c)) /
            (l * l))))

/-- Each recursive sparse sample is larger than its predecessor and satisfies
the explicit growth inequality consumed by `vertexChain_partner_lt_of_sparse`. -/
theorem sparseSample_step {B C c D l : ℝ} (hl : 0 < l) (n : ℕ) :
    sparseSample B C c D l n < sparseSample B C c D l (n + 1) ∧
      l * (B + C + c) +
          D * (B + (sparseSample B C c D l n : ℝ) * D + C + c) <
        l * (l * (sparseSample B C c D l (n + 1) : ℝ)) := by
  have hchosen := Classical.choose_spec (exists_nat_gt
    (max (sparseSample B C c D l n : ℝ)
      ((l * (B + C + c) +
        D * (B + (sparseSample B C c D l n : ℝ) * D + C + c)) /
          (l * l))))
  have hsucc : sparseSample B C c D l (n + 1) =
      Classical.choose (exists_nat_gt
        (max (sparseSample B C c D l n : ℝ)
          ((l * (B + C + c) +
            D * (B + (sparseSample B C c D l n : ℝ) * D + C + c)) /
              (l * l)))) := by
    rw [sparseSample.eq_def]
  have hindex : (sparseSample B C c D l n : ℝ) <
      ((Classical.choose (exists_nat_gt
        (max (sparseSample B C c D l n : ℝ)
          ((l * (B + C + c) +
            D * (B + (sparseSample B C c D l n : ℝ) * D + C + c)) /
              (l * l)))) : ℕ) : ℝ) :=
    (le_max_left _ _).trans_lt hchosen
  have hgrowth :
      (l * (B + C + c) +
        D * (B + (sparseSample B C c D l n : ℝ) * D + C + c)) /
          (l * l) <
      ((Classical.choose (exists_nat_gt
        (max (sparseSample B C c D l n : ℝ)
          ((l * (B + C + c) +
            D * (B + (sparseSample B C c D l n : ℝ) * D + C + c)) /
              (l * l)))) : ℕ) : ℝ) :=
    (le_max_right _ _).trans_lt hchosen
  constructor
  · rw [hsucc]
    exact_mod_cast hindex
  · have hll : 0 < l * l := mul_pos hl hl
    rw [div_lt_iff₀ hll] at hgrowth
    rw [hsucc]
    nlinarith

/-- The recursively constructed sparse sample sequence is strictly
increasing. -/
theorem strictMono_sparseSample {B C c D l : ℝ} (hl : 0 < l) :
    StrictMono (sparseSample B C c D l) :=
  strictMono_nat_of_lt_succ fun n => (sparseSample_step hl n).1

/-- Uniformly long endpoint-close quasi-axis segments admit finite sparse
families of coarse matches, simultaneously before and after any prescribed
offset `M` on the first axis.  The phase differences of the two partner
families will be extracted by pigeonhole in the next step. -/
theorem exists_sparse_double_vertexChain_matches
    {δ B lam c : ℝ} (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ)
    (hgeo : IsGeodesicSpace X) (hiso : IsIsometricAction G X)
    (hB : 0 ≤ B) (hlam : 0 < lam) (hc : 0 ≤ c)
    {f : ℝ → X} (hf : IsAxisConnector h x f)
    (hq : IsQuasiGeodesicAxis lam c h x f)
    (hstep : 0 < dist x (h • x)) :
    ∃ E C : ℝ, 0 ≤ E ∧ 0 ≤ C ∧
      ∀ (M T : ℕ), ∃ S : ℕ, ∀ (p q : PowerAxisSegment h x),
        S ≤ p.steps → dist p.initial q.initial ≤ B →
        dist p.terminal q.terminal ≤ B →
        ∃ (A I J : Fin (T + 1) → ℕ),
          StrictMono A ∧ StrictMono I ∧ StrictMono J ∧
          (∀ r, A r + M ≤ p.steps) ∧
          (∀ r, I r ≤ q.steps ∧
            dist (p.vertexChain (A r)) (q.vertexChain (I r)) ≤ C) ∧
          (∀ r, J r ≤ q.steps ∧
            dist (p.vertexChain (A r + M)) (q.vertexChain (J r)) ≤ C) := by
  obtain ⟨E, C, hE, hC, hmatch⟩ := exists_uniform_vertexChain_match
    hδ hδ0 hgeo hiso hB hlam hc hf hq hstep
  refine ⟨E, C, hE, hC, ?_⟩
  intro M T
  let D : ℝ := lam * dist x (h • x) + c
  let l : ℝ := dist x (h • x) / lam
  let B' : ℝ := B + (M : ℝ) * D
  let a : ℕ → ℕ := sparseSample B' C c D l
  have hl : 0 < l := by
    dsimp [l]
    positivity
  have haMono : StrictMono a := strictMono_sparseSample hl
  obtain ⟨U, hU⟩ := exists_nat_gt (E / l)
  have hEU : E < l * (U : ℝ) := by
    rw [div_lt_iff₀ hl] at hU
    simpa only [mul_comm] using hU
  let S : ℕ := a T + M + U
  refine ⟨S, ?_⟩
  intro p q hpSteps hclose0 hclose1
  let A : Fin (T + 1) → ℕ := fun r => a r.val
  have hAmono : StrictMono A := fun r s hrs => haMono hrs
  have hinternal : ∀ r : Fin (T + 1),
      A r + M ≤ p.steps ∧
      E ≤ l * ((p.steps - (A r + M) : ℕ) : ℝ) := by
    intro r
    have hrT : r.val ≤ T := Nat.lt_succ_iff.mp r.isLt
    have har : a r.val ≤ a T := haMono.monotone hrT
    have hsum : A r + M + U ≤ p.steps := by
      dsimp [S, A] at hpSteps ⊢
      omega
    have hUsub : U ≤ p.steps - (A r + M) := by omega
    have hUsubR : (U : ℝ) ≤ ((p.steps - (A r + M) : ℕ) : ℝ) := by
      exact_mod_cast hUsub
    refine ⟨by omega, ?_⟩
    nlinarith
  have hmatch0 : ∀ r : Fin (T + 1),
      ∃ i : ℕ, i ≤ q.steps ∧
        dist (p.vertexChain (A r)) (q.vertexChain i) ≤ C := by
    intro r
    have hsub : p.steps - (A r + M) ≤ p.steps - A r :=
      Nat.sub_le_sub_left (Nat.le_add_right (A r) M) p.steps
    have hsubR : ((p.steps - (A r + M) : ℕ) : ℝ) ≤
        ((p.steps - A r : ℕ) : ℝ) := by exact_mod_cast hsub
    have hfar : E ≤ l * ((p.steps - A r : ℕ) : ℝ) := by
      have hlmul := mul_le_mul_of_nonneg_left hsubR hl.le
      exact (hinternal r).2.trans hlmul
    exact hmatch p q hclose0 hclose1 (A r)
      (le_trans (Nat.le_add_right (A r) M) (hinternal r).1) hfar
  have hmatchM : ∀ r : Fin (T + 1),
      ∃ j : ℕ, j ≤ q.steps ∧
        dist (p.vertexChain (A r + M)) (q.vertexChain j) ≤ C := by
    intro r
    exact hmatch p q hclose0 hclose1 (A r + M)
      (hinternal r).1 (hinternal r).2
  let I : Fin (T + 1) → ℕ := fun r => Classical.choose (hmatch0 r)
  let J : Fin (T + 1) → ℕ := fun r => Classical.choose (hmatchM r)
  have hIprop : ∀ r, I r ≤ q.steps ∧
      dist (p.vertexChain (A r)) (q.vertexChain (I r)) ≤ C := by
    intro r
    exact Classical.choose_spec (hmatch0 r)
  have hJprop : ∀ r, J r ≤ q.steps ∧
      dist (p.vertexChain (A r + M)) (q.vertexChain (J r)) ≤ C := by
    intro r
    exact Classical.choose_spec (hmatchM r)
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  have hIstrict : StrictMono I := by
    intro r s hrs
    have hrsNat : r.val < s.val := hrs
    have hnext : a (r.val + 1) ≤ a s.val :=
      haMono.monotone (Nat.succ_le_iff.mpr hrsNat)
    have hnextR : (a (r.val + 1) : ℝ) ≤ (a s.val : ℝ) := by
      exact_mod_cast hnext
    have hsparseStep := (sparseSample_step (B := B') (C := C)
      (c := c) (D := D) hl r.val).2
    have hsparse :
        l * (B + C + c) + D * (B + (A r : ℝ) * D + C + c) <
          l * (l * (A s : ℝ)) := by
      dsimp [A, a, B'] at hsparseStep ⊢
      have hMD : 0 ≤ (M : ℝ) * D := mul_nonneg (Nat.cast_nonneg M) hD
      have hlMD : 0 ≤ l * ((M : ℝ) * D) := mul_nonneg hl.le hMD
      have hDMD : 0 ≤ D * ((M : ℝ) * D) := mul_nonneg hD hMD
      have hleft :
          l * (B + C + c) +
              D * (B + (sparseSample (B + (M : ℝ) * D) C c D l r.val : ℝ) *
                D + C + c) ≤
            l * (B + (M : ℝ) * D + C + c) +
              D * (B + (M : ℝ) * D +
                (sparseSample (B + (M : ℝ) * D) C c D l r.val : ℝ) *
                  D + C + c) := by
        nlinarith
      have hright :
          l * (l * (sparseSample (B + (M : ℝ) * D) C c D l (r.val + 1) : ℝ)) ≤
            l * (l * (sparseSample (B + (M : ℝ) * D) C c D l s.val : ℝ)) := by
        have hll := mul_le_mul_of_nonneg_left hnextR (mul_nonneg hl.le hl.le)
        nlinarith
      exact hleft.trans_lt (hsparseStep.trans_le hright)
    exact vertexChain_partner_lt_of_sparse hiso hlam hc hf hq hstep p q
      (le_trans (Nat.le_add_right (A r) M) (hinternal r).1)
      (le_trans (Nat.le_add_right (A s) M) (hinternal s).1)
      (hIprop r).1 (hIprop s).1 hclose0
      (hIprop r).2 (hIprop s).2 hsparse
  have hJstrict : StrictMono J := by
    intro r s hrs
    have hrsNat : r.val < s.val := hrs
    have hnext : a (r.val + 1) ≤ a s.val :=
      haMono.monotone (Nat.succ_le_iff.mpr hrsNat)
    have hnextR : (a (r.val + 1) : ℝ) ≤ (a s.val : ℝ) := by
      exact_mod_cast hnext
    have hsparseStep := (sparseSample_step (B := B') (C := C)
      (c := c) (D := D) hl r.val).2
    have hsparse :
        l * (B + C + c) +
            D * (B + ((A r + M : ℕ) : ℝ) * D + C + c) <
          l * (l * ((A s + M : ℕ) : ℝ)) := by
      dsimp [A, a, B'] at hsparseStep ⊢
      push_cast
      have hMD : 0 ≤ (M : ℝ) * D := mul_nonneg (Nat.cast_nonneg M) hD
      have hlMD : 0 ≤ l * ((M : ℝ) * D) := mul_nonneg hl.le hMD
      have hleft :
          l * (B + C + c) +
              D * (B + ((sparseSample (B + (M : ℝ) * D) C c D l r.val : ℝ) +
                (M : ℝ)) * D + C + c) ≤
            l * (B + (M : ℝ) * D + C + c) +
              D * (B + (M : ℝ) * D +
                (sparseSample (B + (M : ℝ) * D) C c D l r.val : ℝ) *
                  D + C + c) := by
        ring_nf at ⊢
        nlinarith
      have hright :
          l * (l * (sparseSample (B + (M : ℝ) * D) C c D l (r.val + 1) : ℝ)) ≤
            l * (l * ((sparseSample (B + (M : ℝ) * D) C c D l s.val : ℝ) +
              (M : ℝ))) := by
        have hll := mul_le_mul_of_nonneg_left hnextR (mul_nonneg hl.le hl.le)
        nlinarith [mul_nonneg (mul_nonneg hl.le hl.le) (Nat.cast_nonneg M)]
      exact hleft.trans_lt (hsparseStep.trans_le hright)
    exact vertexChain_partner_lt_of_sparse hiso hlam hc hf hq hstep p q
      (hinternal r).1 (hinternal s).1
      (hJprop r).1 (hJprop s).1 hclose0
      (hJprop r).2 (hJprop s).2 hsparse
  exact ⟨A, I, J, hAmono, hIstrict, hJstrict,
    fun r => (hinternal r).1, hIprop, hJprop⟩

/-- If two matched pairs are `M` vertices apart on the first quasi-axis, the
difference of their partner indices is uniformly bounded.  Consequently only
finitely many phase differences can occur in the later pigeonhole extraction. -/
theorem vertexChain_match_phase_bound
    {C lam c : ℝ} (hiso : IsIsometricAction G X)
    {f : ℝ → X} (hf : IsAxisConnector h x f)
    (hq : IsQuasiGeodesicAxis lam c h x f)
    (p q : PowerAxisSegment h x) {j M i k : ℕ}
    (hjM : j + M ≤ p.steps)
    (hmatch0 : dist (p.vertexChain j) (q.vertexChain i) ≤ C)
    (hmatch1 : dist (p.vertexChain (j + M)) (q.vertexChain k) ≤ C) :
    let D := lam * dist x (h • x) + c
    let l := dist x (h • x) / lam
    l * |((k : ℤ) - (i : ℤ) : ℝ)| ≤ 2 * C + (M : ℝ) * D + c := by
  let D : ℝ := lam * dist x (h • x) + c
  let l : ℝ := dist x (h • x) / lam
  have hpEdge : ∀ n, n < p.steps →
      dist (p.vertexChain n) (p.vertexChain (n + 1)) ≤ D := by
    intro n hn
    exact vertexChain_edge_le hiso hf hq p n
  have hpDist := dist_chain_le_nat_mul p.vertexChain hpEdge
    (N := p.steps) (a := j) (n := M) hjM
  have hqUpper : dist (q.vertexChain i) (q.vertexChain k) ≤
      2 * C + (M : ℝ) * D := by
    have htri := dist_triangle4 (q.vertexChain i) (p.vertexChain j)
      (p.vertexChain (j + M)) (q.vertexChain k)
    rw [dist_comm (q.vertexChain i) (p.vertexChain j)] at htri
    linarith
  rcases le_total i k with hik | hki
  · have hprog := vertexChain_progress hiso hf hq q hik
    have hcast : |((k : ℤ) - (i : ℤ) : ℝ)| = ((k - i : ℕ) : ℝ) := by
      have hsub : (k : ℤ) - (i : ℤ) = ((k - i : ℕ) : ℤ) := by omega
      rw [← Int.cast_sub, hsub, Int.cast_natCast,
        abs_of_nonneg (Nat.cast_nonneg _)]
    rw [hcast]
    dsimp [l, D]
    linarith
  · have hprog := vertexChain_progress hiso hf hq q hki
    have hcast : |((k : ℤ) - (i : ℤ) : ℝ)| = ((i - k : ℕ) : ℝ) := by
      have hsub : (k : ℤ) - (i : ℤ) = -((i - k : ℕ) : ℤ) := by omega
      rw [← Int.cast_sub, hsub, Int.cast_neg, Int.cast_natCast, abs_neg,
        abs_of_nonneg (Nat.cast_nonneg _)]
    rw [hcast]
    rw [dist_comm (q.vertexChain k) (q.vertexChain i)] at hprog
    dsimp [l, D]
    linarith

/-- Among sufficiently many ordered double matches, a prescribed number have
the same integer phase difference on the second quasi-axis.  The selected
families remain strictly increasing and stay inside the two finite segments.
This is the finite pigeonhole extraction in Bestvina--Fujiwara's axial
argument. -/
theorem exists_constant_phase_vertexChain_matches
    {δ B lam c : ℝ} (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ)
    (hgeo : IsGeodesicSpace X) (hiso : IsIsometricAction G X)
    (hB : 0 ≤ B) (hlam : 0 < lam) (hc : 0 ≤ c)
    {f : ℝ → X} (hf : IsAxisConnector h x f)
    (hq : IsQuasiGeodesicAxis lam c h x f)
    (hstep : 0 < dist x (h • x)) :
    ∃ E C : ℝ, 0 ≤ E ∧ 0 ≤ C ∧
      ∀ (M N : ℕ), ∃ S : ℕ, ∀ (p q : PowerAxisSegment h x),
        S ≤ p.steps → dist p.initial q.initial ≤ B →
        dist p.terminal q.terminal ≤ B →
        ∃ (K : ℤ) (A I J : Fin (N + 1) → ℕ),
          StrictMono A ∧ StrictMono I ∧ StrictMono J ∧
          (∀ r, A r + M ≤ p.steps) ∧
          (∀ r, I r ≤ q.steps ∧
            dist (p.vertexChain (A r)) (q.vertexChain (I r)) ≤ C) ∧
          (∀ r, J r ≤ q.steps ∧
            dist (p.vertexChain (A r + M)) (q.vertexChain (J r)) ≤ C) ∧
          (∀ r, (J r : ℤ) - (I r : ℤ) = K) := by
  obtain ⟨E, C, hE, hC, hdouble⟩ :=
    exists_sparse_double_vertexChain_matches
      hδ hδ0 hgeo hiso hB hlam hc hf hq hstep
  refine ⟨E, C, hE, hC, ?_⟩
  intro M N
  let D : ℝ := lam * dist x (h • x) + c
  let l : ℝ := dist x (h • x) / lam
  have hl : 0 < l := by
    dsimp [l]
    positivity
  obtain ⟨Z, hZ⟩ := exists_nat_gt ((2 * C + (M : ℝ) * D + c) / l)
  let colors : Finset ℤ := Finset.Icc (-(Z : ℤ)) (Z : ℤ)
  have hcolors : colors.Nonempty := by
    refine ⟨0, ?_⟩
    simp [colors]
  obtain ⟨S, hS⟩ := hdouble M (colors.card * (N + 1))
  refine ⟨S, ?_⟩
  intro p q hpSteps hclose0 hclose1
  obtain ⟨A₀, I₀, J₀, hA₀, hI₀, hJ₀, hinside, hmatch0, hmatchM⟩ :=
    hS p q hpSteps hclose0 hclose1
  let φ : Fin (colors.card * (N + 1)) → ℤ := fun r =>
    (J₀ r.castSucc : ℤ) - (I₀ r.castSucc : ℤ)
  have hφ : ∀ r, φ r ∈ colors := by
    intro r
    have hphase := vertexChain_match_phase_bound hiso hf hq p q
      (hinside r.castSucc) (hmatch0 r.castSucc).2 (hmatchM r.castSucc).2
    have hcast : ((φ r : ℤ) : ℝ) =
        ((J₀ r.castSucc : ℤ) : ℝ) - ((I₀ r.castSucc : ℤ) : ℝ) := by
      simp only [φ, Int.cast_sub, Int.cast_natCast]
    have habsLe :
        |((φ r : ℤ) : ℝ)| ≤ (2 * C + (M : ℝ) * D + c) / l := by
      rw [hcast, le_div_iff₀ hl]
      dsimp [φ, l, D] at hphase ⊢
      simpa only [mul_comm] using hphase
    have habs : |((φ r : ℤ) : ℝ)| < (Z : ℝ) := habsLe.trans_lt hZ
    have hlowerR : (-(Z : ℤ) : ℝ) ≤ ((φ r : ℤ) : ℝ) := by
      push_cast
      exact le_of_lt (neg_lt_of_abs_lt habs)
    have hupperR : ((φ r : ℤ) : ℝ) ≤ ((Z : ℤ) : ℝ) := by
      exact le_of_lt (lt_of_abs_lt habs)
    have hlower : -(Z : ℤ) ≤ φ r := by exact_mod_cast hlowerR
    have hupper : φ r ≤ (Z : ℤ) := by exact_mod_cast hupperR
    exact Finset.mem_Icc.mpr ⟨hlower, hupper⟩
  obtain ⟨K, hKmem, R, hR, hphase⟩ :=
    exists_constant_strictMono_subsequence colors hcolors N φ hφ
  let select : Fin (N + 1) → Fin (colors.card * (N + 1) + 1) :=
    fun r => (R r).castSucc
  let A : Fin (N + 1) → ℕ := fun r => A₀ (select r)
  let I : Fin (N + 1) → ℕ := fun r => I₀ (select r)
  let J : Fin (N + 1) → ℕ := fun r => J₀ (select r)
  have hselect : StrictMono select := by
    intro r s hrs
    exact hR hrs
  have hA : StrictMono A := hA₀.comp hselect
  have hI : StrictMono I := hI₀.comp hselect
  have hJ : StrictMono J := hJ₀.comp hselect
  refine ⟨K, A, I, J, hA, hI, hJ, ?_, ?_, ?_, ?_⟩
  · intro r
    exact hinside (select r)
  · intro r
    exact hmatch0 (select r)
  · intro r
    exact hmatchM (select r)
  · intro r
    exact hphase r

/-- Integer power vertices whose arclength coordinates are sufficiently
separated are metrically separated.  This is the quantitative fact that makes
the partner exponents in the oriented sampling argument injective, and then
strictly monotone. -/
theorem le_dist_vertex_of_coordinate_gap
    (hiso : IsIsometricAction G X) {f : ℝ → X}
    (hf : IsAxisConnector h x f) {lam c R : ℝ} (hlam : 0 < lam)
    (hq : IsQuasiGeodesicAxis lam c h x f)
    (p : PowerAxisSegment h x) (i j : ℤ)
    (hgap : lam * (R + c) ≤
      |((i : ℝ) - (j : ℝ)) * dist x (h • x)|) :
    R ≤ dist (p.vertex i) (p.vertex j) := by
  have hlower := (vertex_dist_bounds hiso hf hq p i j).1
  have hdiv : R + c ≤
      |((i : ℝ) - (j : ℝ)) * dist x (h • x)| / lam := by
    rw [le_div_iff₀ hlam]
    simpa only [mul_comm] using hgap
  linarith

/-- The positive-power conclusion of DGO Lemma 6.7 from the monotone vertex
samples supplied by the oriented quasi-axis overlap.  The two base alignments
cost `C₀`, while corresponding sampled vertices cost `C`; hence WPD is applied
at error `C + C₀`.

This theorem isolates exactly the input imported by DGO from
Bestvina--Fujiwara, Proposition 6: the remaining geometric task is to construct
the two strictly increasing exponent families from sufficiently long oriented
close segments. -/
theorem dgoLemma67_of_monotone_vertex_samples
    {δ C₀ C : ℝ} (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ)
    (hgeo : IsGeodesicSpace X) (hiso : IsIsometricAction G X)
    (hlox : IsLoxodromic h x) (hwpd : IsWPDAt h x)
    (hC₀ : 0 ≤ C₀) (hC : 0 ≤ C) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∃ N : ℕ,
      ∀ (p q : PowerAxisSegment h x),
      dist p.initial q.initial ≤ C₀ →
      ∀ K : ℤ,
      dist (p.vertex (p.start + (M : ℤ)))
        (q.vertex (q.start + K)) ≤ C₀ →
      ∀ (A B : Fin (N + 1) → ℤ), StrictMono A → StrictMono B →
        (∀ i, dist (p.vertex (p.start + A i))
          (q.vertex (q.start + B i)) ≤ C) →
        (∀ i, dist (p.vertex (p.start + (M : ℤ) + A i))
          (q.vertex (q.start + K + B i)) ≤ C) →
        ∃ r s : ℤ, 0 < r ∧ 0 < s ∧
          p.conjugate ^ r = q.conjugate ^ s := by
  have hEventually : IsWPDAtEventually h x :=
    isWPDAtEventually_of_geodesic hδ hδ0 hgeo hiso hlox hwpd
  have herror : 0 ≤ C + C₀ := by linarith
  obtain ⟨M₀, hM₀⟩ :=
    isWPDAtEventually_common_positive_zpow_conj hiso hEventually herror
  refine ⟨M₀, ?_⟩
  intro M hM
  obtain ⟨N, hN⟩ := hM₀ M hM
  refine ⟨N, ?_⟩
  intro p q hbase0 K hbaseM A B hA hB hsamples0 hsamplesM
  let z : X := p.initial
  let a : G := p.conjugate
  let b : G := q.conjugate
  let u : G := p.translate * h ^ p.start
  have huPoint : u • x = z := by rfl
  have huConj : u * h * u⁻¹ = a := by
    dsimp [u, a, conjugate]
    group
  have hpairs : ∀ i,
      dist ((a ^ (A i)) • z) ((b ^ (B i)) • z) ≤ C + C₀ ∧
      dist ((a ^ (A i)) • ((a ^ M) • z))
        ((b ^ (B i)) • ((a ^ M) • z)) ≤ C + C₀ := by
    intro i
    have hpA : (a ^ (A i)) • z = p.vertex (p.start + A i) := by
      dsimp [a, z]
      exact p.conjugate_zpow_smul_initial (A i)
    have hqB : (b ^ (B i)) • q.initial = q.vertex (q.start + B i) := by
      dsimp [b]
      exact q.conjugate_zpow_smul_initial (B i)
    have hfirst : dist ((a ^ (A i)) • z) ((b ^ (B i)) • z) ≤ C + C₀ := by
      have hsample :
          dist ((a ^ (A i)) • z) ((b ^ (B i)) • q.initial) ≤ C := by
        rw [hpA, hqB]
        exact hsamples0 i
      have hshift :
          dist ((b ^ (B i)) • q.initial) ((b ^ (B i)) • z) =
            dist q.initial z := hiso _ _ _
      have htri := dist_triangle ((a ^ (A i)) • z)
        ((b ^ (B i)) • q.initial) ((b ^ (B i)) • z)
      have hbase0' : dist q.initial z ≤ C₀ := by
        dsimp [z]
        rwa [dist_comm]
      linarith
    have hpM : (a ^ M) • z = p.vertex (p.start + (M : ℤ)) := by
      rw [← zpow_natCast]
      dsimp [a, z]
      exact p.conjugate_zpow_smul_initial (M : ℤ)
    have hqK : (b ^ K) • q.initial = q.vertex (q.start + K) := by
      dsimp [b]
      exact q.conjugate_zpow_smul_initial K
    have hpMA : (a ^ (A i)) • ((a ^ M) • z) =
        p.vertex (p.start + (M : ℤ) + A i) := by
      rw [hpM]
      dsimp [a]
      exact p.conjugate_zpow_smul_vertex (A i) (p.start + (M : ℤ))
    have hqKB : (b ^ (B i)) • ((b ^ K) • q.initial) =
        q.vertex (q.start + K + B i) := by
      rw [hqK]
      dsimp [b]
      exact q.conjugate_zpow_smul_vertex (B i) (q.start + K)
    have hsecond :
        dist ((a ^ (A i)) • ((a ^ M) • z))
          ((b ^ (B i)) • ((a ^ M) • z)) ≤ C + C₀ := by
      have hsample :
          dist ((a ^ (A i)) • ((a ^ M) • z))
            ((b ^ (B i)) • ((b ^ K) • q.initial)) ≤ C := by
        rw [hpMA, hqKB]
        exact hsamplesM i
      have hshift :
          dist ((b ^ (B i)) • ((b ^ K) • q.initial))
            ((b ^ (B i)) • ((a ^ M) • z)) =
              dist ((b ^ K) • q.initial) ((a ^ M) • z) := hiso _ _ _
      have htri := dist_triangle ((a ^ (A i)) • ((a ^ M) • z))
        ((b ^ (B i)) • ((b ^ K) • q.initial))
        ((b ^ (B i)) • ((a ^ M) • z))
      have hbaseM' : dist ((b ^ K) • q.initial) ((a ^ M) • z) ≤ C₀ := by
        rw [hpM, hqK]
        rwa [dist_comm]
      linarith
    exact ⟨hfirst, hsecond⟩
  obtain ⟨r, s, hr, hs, hrs⟩ := hN u b A B hA hB (fun i => by
    rw [huConj, huPoint]
    exact hpairs i)
  refine ⟨r, s, hr, hs, ?_⟩
  dsimp [a, b] at huConj ⊢
  rwa [huConj] at hrs

/-- DGO's oriented endpoint-closeness condition for two power-vertex
subsegments. -/
def OrientedClose (B : ℝ) (p q : PowerAxisSegment h x) : Prop :=
  dist p.initial q.initial ≤ B ∧ dist p.terminal q.terminal ≤ B

/-- **DGO Lemma 6.7 for power-vertex segments on a periodic quasi-axis.**
The asynchronous ordered matches and their constant phase are constructed
from hyperbolicity, then rebased at the first selected match before applying
WPD.  Thus no global geodesic axis or abstract fellow-travelling hypothesis is
needed. -/
theorem exists_equal_positive_powers_of_long_powerSegments_of_quasiAxis
    {δ B lam c : ℝ} (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ)
    (hgeo : IsGeodesicSpace X) (hiso : IsIsometricAction G X)
    (hB : 0 ≤ B) (hlam : 0 < lam) (hc : 0 ≤ c)
    {f : ℝ → X} (hf : IsAxisConnector h x f)
    (hq : IsQuasiGeodesicAxis lam c h x f)
    (hstep : 0 < dist x (h • x))
    (hlox : IsLoxodromic h x) (hwpd : IsWPDAt h x) :
    ∃ L : ℝ, 0 < L ∧ ∀ (p q : PowerAxisSegment h x),
      L ≤ p.length → L ≤ q.length → OrientedClose B p q →
      ∃ r s : ℤ, 0 < r ∧ 0 < s ∧
        p.conjugate ^ r = q.conjugate ^ s := by
  obtain ⟨E, C, hE, hC, hphase⟩ :=
    exists_constant_phase_vertexChain_matches
      hδ hδ0 hgeo hiso hB hlam hc hf hq hstep
  obtain ⟨M₀, hM₀⟩ := dgoLemma67_of_monotone_vertex_samples
    hδ hδ0 hgeo hiso hlox hwpd hC hC
  obtain ⟨N, hN⟩ := hM₀ M₀ le_rfl
  obtain ⟨S, hS⟩ := hphase M₀ N
  let L : ℝ := ((S + 1 : ℕ) : ℝ) * dist x (h • x)
  have hL : 0 < L := by
    dsimp [L]
    positivity
  refine ⟨L, hL, ?_⟩
  intro p q hpLength _hqLength hclose
  have hpCast : ((S + 1 : ℕ) : ℝ) ≤ (p.steps : ℝ) := by
    rw [p.length_eq_steps_mul] at hpLength
    dsimp [L] at hpLength
    nlinarith
  have hpSucc : S + 1 ≤ p.steps := by exact_mod_cast hpCast
  have hpSteps : S ≤ p.steps := by omega
  obtain ⟨K, A, I, J, hA, hI, hJ, hinside, hmatch0, hmatchM, hphaseEq⟩ :=
    hS p q hpSteps hclose.1 hclose.2
  let r₀ : Fin (N + 1) := ⟨0, Nat.succ_pos N⟩
  have hA₀Steps : A r₀ ≤ p.steps :=
    le_trans (Nat.le_add_right (A r₀) M₀) (hinside r₀)
  have hI₀Steps : I r₀ ≤ q.steps := (hmatch0 r₀).1
  let p' : PowerAxisSegment h x :=
    { translate := p.translate
      start := p.start + (A r₀ : ℤ)
      stop := p.stop
      start_le_stop := by
        have hcast : (A r₀ : ℤ) ≤ (p.steps : ℤ) := by
          exact_mod_cast hA₀Steps
        rw [p.steps_cast] at hcast
        omega }
  let q' : PowerAxisSegment h x :=
    { translate := q.translate
      start := q.start + (I r₀ : ℤ)
      stop := q.stop
      start_le_stop := by
        have hcast : (I r₀ : ℤ) ≤ (q.steps : ℤ) := by
          exact_mod_cast hI₀Steps
        rw [q.steps_cast] at hcast
        omega }
  let A' : Fin (N + 1) → ℤ := fun r => (A r : ℤ) - (A r₀ : ℤ)
  let I' : Fin (N + 1) → ℤ := fun r => (I r : ℤ) - (I r₀ : ℤ)
  have hA' : StrictMono A' := by
    intro r s hrs
    dsimp [A']
    exact sub_lt_sub_right (by exact_mod_cast hA hrs) (A r₀ : ℤ)
  have hI' : StrictMono I' := by
    intro r s hrs
    dsimp [I']
    exact sub_lt_sub_right (by exact_mod_cast hI hrs) (I r₀ : ℤ)
  have hbase0 : dist p'.initial q'.initial ≤ C := by
    simpa only [p', q', vertexChain, initial, vertex] using (hmatch0 r₀).2
  have hbaseM :
      dist (p'.vertex (p'.start + (M₀ : ℤ)))
        (q'.vertex (q'.start + K)) ≤ C := by
    have hphase0 := hphaseEq r₀
    have hpIndex : p'.start + (M₀ : ℤ) =
        p.start + ((A r₀ + M₀ : ℕ) : ℤ) := by
      dsimp [p']
      omega
    have hqIndex : q'.start + K = q.start + (J r₀ : ℤ) := by
      dsimp [q']
      omega
    rw [hpIndex, hqIndex]
    exact (hmatchM r₀).2
  have hsamples0 : ∀ r,
      dist (p'.vertex (p'.start + A' r))
        (q'.vertex (q'.start + I' r)) ≤ C := by
    intro r
    have hpIndex : p'.start + A' r = p.start + (A r : ℤ) := by
      dsimp [p', A']
      omega
    have hqIndex : q'.start + I' r = q.start + (I r : ℤ) := by
      dsimp [q', I']
      omega
    rw [hpIndex, hqIndex]
    exact (hmatch0 r).2
  have hsamplesM : ∀ r,
      dist (p'.vertex (p'.start + (M₀ : ℤ) + A' r))
        (q'.vertex (q'.start + K + I' r)) ≤ C := by
    intro r
    have hphaseR := hphaseEq r
    have hpIndex : p'.start + (M₀ : ℤ) + A' r =
        p.start + ((A r + M₀ : ℕ) : ℤ) := by
      dsimp [p', A']
      omega
    have hqIndex : q'.start + K + I' r = q.start + (J r : ℤ) := by
      dsimp [q', I']
      omega
    rw [hpIndex, hqIndex]
    exact (hmatchM r).2
  obtain ⟨r, s, hr, hs, hrs⟩ :=
    hN p' q' hbase0 K hbaseM A' I' hA' hI' hsamples0 hsamplesM
  refine ⟨r, s, hr, hs, ?_⟩
  simpa only [p', q', conjugate] using hrs

/-! ## From oriented power cores to WPD fellow travel -/

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

/-- The preceding WPD bridge in DGO's path-length language.  A
`(lam,c)`-quasi-axis segment of length at least `lam * (T + c)` has metric
displacement at least `T`. -/
theorem exists_common_zpow_of_long_quasiAxis_segments
    {δ B lam c : ℝ} (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ)
    (hgeo : IsGeodesicSpace X) (hiso : IsIsometricAction G X)
    {f : ℝ → X} (hf : IsAxisConnector h x f)
    (hqAxis : IsQuasiGeodesicAxis lam c h x f)
    (hlam : 0 < lam) (hc : 0 ≤ c)
    (hlox : IsLoxodromic h x) (hwpd : IsWPDAt h x) (hB : 0 ≤ B)
    (p q : PowerAxisSegment h x) :
    ∃ L : ℝ, 0 < L ∧
      (L ≤ p.length → L ≤ q.length → OrientedClose B p q →
       ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧
         p.conjugate ^ a = q.conjugate ^ b) := by
  obtain ⟨T, hT, hbridge⟩ :=
    exists_common_zpow_of_long_orientedClose
      hδ hδ0 hgeo hiso hlox hwpd hB p q
  let L : ℝ := lam * (T + c)
  have hL : 0 < L := by
    dsimp [L]
    positivity
  refine ⟨L, hL, ?_⟩
  intro hpLen hqLen hclose
  have hpDiv : T + c ≤ p.length / lam := by
    rw [le_div_iff₀ hlam]
    dsimp [L] at hpLen
    simpa only [mul_comm] using hpLen
  have hqDiv : T + c ≤ q.length / lam := by
    rw [le_div_iff₀ hlam]
    dsimp [L] at hqLen
    simpa only [mul_comm] using hqLen
  have hpMetric := length_div_sub_le_dist hiso hf hqAxis p
  have hqMetric := length_div_sub_le_dist hiso hf hqAxis q
  apply hbridge
  · linarith
  · linarith
  · exact hclose

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

/-- The exact asynchronous monotone-sampling content used from
Bestvina--Fujiwara, Proposition 6, in DGO Lemma 6.7.  For the WPD offset `M`
and any required finite sample count, sufficiently long oriented-close
power-axis segments contain two increasing matched vertex families, both
before and after the offsets `M` and `K`. -/
def HasMonotoneVertexSampling (B : ℝ) (h : G) (x : X) : Prop :=
  ∃ C₀ C : ℝ, 0 ≤ C₀ ∧ 0 ≤ C ∧
    ∀ (M N : ℕ), ∃ L : ℝ, 0 < L ∧
      ∀ (p q : PowerAxisSegment h x),
        L ≤ p.length → L ≤ q.length → OrientedClose B p q →
        ∃ (K : ℤ) (A D : Fin (N + 1) → ℤ),
          StrictMono A ∧ StrictMono D ∧
          dist p.initial q.initial ≤ C₀ ∧
          dist (p.vertex (p.start + (M : ℤ)))
            (q.vertex (q.start + K)) ≤ C₀ ∧
          (∀ i, dist (p.vertex (p.start + A i))
            (q.vertex (q.start + D i)) ≤ C) ∧
          (∀ i, dist (p.vertex (p.start + (M : ℤ) + A i))
            (q.vertex (q.start + K + D i)) ≤ C)

/-- The geometric core of Bestvina--Fujiwara's proof: arbitrarily long
oriented-close axis segments contain a uniformly close synchronous block of
power vertices, after one integer offset on the second axis. -/
def HasUniformVertexBlockFellowTravel (B : ℝ) (h : G) (x : X) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℕ, ∃ L : ℝ, 0 < L ∧
    ∀ (p q : PowerAxisSegment h x),
      L ≤ p.length → L ≤ q.length → OrientedClose B p q →
      ∃ J : ℤ, ∀ n : ℕ, n ≤ R →
        dist (p.vertex (p.start + (n : ℤ)))
          (q.vertex (q.start + J + (n : ℤ))) ≤ C

/-- Bestvina--Fujiwara Proposition 6 in the axial case: oriented-close
geodesic-axis segments contain synchronous blocks of uniformly close power
vertices.  The endpoint fellow-travelling estimate is DGO Lemma 6.4's thin
quadrilateral argument. -/
theorem hasUniformVertexBlockFellowTravel_of_parametrizedAxis
    {δ B : ℝ} (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ)
    (hgeo : IsGeodesicSpace X) (hiso : IsIsometricAction G X)
    (hB : 0 ≤ B) {a : ℝ → X} (ha : IsParametrizedAxis h x a)
    (hstep : 0 < dist x (h • x)) :
    HasUniformVertexBlockFellowTravel B h x := by
  let C : ℝ := 3 * B + 12 * δ
  have hC : 0 ≤ C := by
    dsimp [C]
    linarith
  refine ⟨C, hC, ?_⟩
  intro R
  let L : ℝ := ((R : ℝ) + 1) * dist x (h • x)
  have hL : 0 < L := by
    dsimp [L]
    positivity
  refine ⟨L, hL, ?_⟩
  intro p q hpLength hqLength hclose
  let P : ℝ → X := parametrizedPath a p
  let Q : ℝ → X := parametrizedPath a q
  have hP : IsGeodesicSegment P 0 p.length := by
    exact isGeodesicSegment_parametrizedPath hiso ha p
  have hQ : IsGeodesicSegment Q 0 q.length := by
    exact isGeodesicSegment_parametrizedPath hiso ha q
  have h0 : dist (P 0) (Q 0) ≤ B := by
    rw [show P 0 = p.initial by exact parametrizedPath_zero ha p,
      show Q 0 = q.initial by exact parametrizedPath_zero ha q]
    exact hclose.1
  have h1 : dist (P p.length) (Q q.length) ≤ B := by
    rw [show P p.length = p.terminal by exact parametrizedPath_length ha p,
      show Q q.length = q.terminal by exact parametrizedPath_length ha q]
    exact hclose.2
  refine ⟨0, ?_⟩
  intro n hn
  have hnR : (n : ℝ) ≤ (R : ℝ) := by exact_mod_cast hn
  have hnL : (n : ℝ) * dist x (h • x) ≤ L := by
    have hmul := mul_le_mul_of_nonneg_right hnR hstep.le
    dsimp [L]
    nlinarith
  have hcloseAt := dist_same_parameter_le_of_geodesic_endpoints_close
    hδ hδ0 hgeo hB hP p.length_nonneg hQ q.length_nonneg h0 h1
    (t := (n : ℝ) * dist x (h • x))
    ⟨mul_nonneg (Nat.cast_nonneg n) hstep.le, hnL.trans hpLength⟩
    ⟨mul_nonneg (Nat.cast_nonneg n) hstep.le, hnL.trans hqLength⟩
  rw [show P ((n : ℝ) * dist x (h • x)) =
      p.vertex (p.start + (n : ℤ)) by
        exact parametrizedPath_eq_vertex ha p (n : ℤ),
    show Q ((n : ℝ) * dist x (h • x)) =
      q.vertex (q.start + (n : ℤ)) by
        exact parametrizedPath_eq_vertex ha q (n : ℤ)] at hcloseAt
  simpa only [zero_add, add_zero, add_assoc] using hcloseAt

/-- A uniform fellow-travelling vertex block supplies all asynchronous
monotone samples required by the WPD pigeonhole argument. -/
theorem hasMonotoneVertexSampling_of_uniformVertexBlockFellowTravel
    {B lam c : ℝ} (hB : 0 ≤ B) (hlam : 0 < lam) (hc : 0 ≤ c)
    {h : G} {x : X} (hiso : IsIsometricAction G X)
    {f : ℝ → X} (hf : IsAxisConnector h x f)
    (hqAxis : IsQuasiGeodesicAxis lam c h x f)
    (hblock : HasUniformVertexBlockFellowTravel B h x) :
    HasMonotoneVertexSampling B h x := by
  obtain ⟨C, hC, hblock⟩ := hblock
  let E : ℝ := lam * (lam * (B + C + c)) + c
  have hE : 0 ≤ E := by
    dsimp [E]
    positivity
  refine ⟨max B (C + E), C,
    hB.trans (le_max_left B (C + E)), hC, ?_⟩
  intro M N
  obtain ⟨L, hL, hblockL⟩ := hblock (M + N)
  refine ⟨L, hL, ?_⟩
  intro p q hpLen hqLen hclose
  obtain ⟨J, hK⟩ := hblockL p q hpLen hqLen hclose
  let A : Fin (N + 1) → ℤ := fun i => (i.val : ℤ)
  let D : Fin (N + 1) → ℤ := fun i => J + (i.val : ℤ)
  have hA : StrictMono A := by
    intro i j hij
    dsimp [A]
    exact_mod_cast hij
  have hD : StrictMono D := by
    intro i j hij
    dsimp [D]
    have hij' : (i.val : ℤ) < (j.val : ℤ) := by exact_mod_cast hij
    simpa only [add_comm] using add_lt_add_left hij' J
  have hblock0 := hK 0 (Nat.zero_le (M + N))
  simp only [Nat.cast_zero, add_zero] at hblock0
  have hq0J : dist (q.vertex q.start) (q.vertex (q.start + J)) ≤ B + C := by
    have htri := dist_triangle (q.vertex q.start) (p.vertex p.start)
      (q.vertex (q.start + J))
    have hstart : dist (q.vertex q.start) (p.vertex p.start) ≤ B := by
      simpa only [initial, vertex, dist_comm] using hclose.1
    linarith
  have hlower := (vertex_dist_bounds hiso hf hqAxis q q.start (q.start + J)).1
  have hcoordEq :
      |((q.start : ℝ) - ((q.start + J : ℤ) : ℝ)) * dist x (h • x)| =
        |(J : ℝ) * dist x (h • x)| := by
    push_cast
    rw [show ((q.start : ℝ) - ((q.start : ℝ) + (J : ℝ))) *
        dist x (h • x) = -((J : ℝ) * dist x (h • x)) by ring, abs_neg]
  rw [hcoordEq] at hlower
  have hcoordDiv : |(J : ℝ) * dist x (h • x)| / lam ≤ B + C + c := by
    linarith
  have hcoordBound : |(J : ℝ) * dist x (h • x)| ≤ lam * (B + C + c) := by
    rw [div_le_iff₀ hlam] at hcoordDiv
    simpa only [mul_comm] using hcoordDiv
  have hblockM := hK M (Nat.le_add_right M N)
  have hshiftUpper := (vertex_dist_bounds hiso hf hqAxis q
    (q.start + J + (M : ℤ)) (q.start + (M : ℤ))).2
  have hshiftCoord :
      |(((q.start + J + (M : ℤ) : ℤ) : ℝ) -
          ((q.start + (M : ℤ) : ℤ) : ℝ)) * dist x (h • x)| =
        |(J : ℝ) * dist x (h • x)| := by
    push_cast
    congr 1
    ring
  rw [hshiftCoord] at hshiftUpper
  have hmulBound := mul_le_mul_of_nonneg_left hcoordBound hlam.le
  have hshift : dist (q.vertex (q.start + J + (M : ℤ)))
      (q.vertex (q.start + (M : ℤ))) ≤ E := by
    dsimp [E]
    linarith
  have hbaseM : dist (p.vertex (p.start + (M : ℤ)))
      (q.vertex (q.start + (M : ℤ))) ≤ C + E := by
    exact (dist_triangle _ (q.vertex (q.start + J + (M : ℤ))) _).trans
      (add_le_add hblockM hshift)
  refine ⟨(M : ℤ), A, D, hA, hD,
    hclose.1.trans (le_max_left B (C + E)),
    hbaseM.trans (le_max_right B (C + E)), ?_, ?_⟩
  · intro i
    have hiN : i.val ≤ N := Nat.lt_succ_iff.mp i.isLt
    have hiMN : i.val ≤ M + N := hiN.trans (Nat.le_add_left N M)
    simpa only [A, D, add_assoc] using hK i.val hiMN
  · intro i
    have hiN : i.val ≤ N := Nat.lt_succ_iff.mp i.isLt
    have hMi : M + i.val ≤ M + N := Nat.add_le_add_left hiN M
    simpa only [A, D, Nat.cast_add, Int.ofNat_eq_natCast, add_assoc,
      add_left_comm, add_comm] using hK (M + i.val) hMi

/-- A global geodesic axis supplies the complete monotone-sampling input of
Bestvina--Fujiwara Proposition 6, with no additional geometric hypothesis. -/
theorem hasMonotoneVertexSampling_of_parametrizedAxis
    {δ B : ℝ} (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ)
    (hgeo : IsGeodesicSpace X) (hiso : IsIsometricAction G X)
    (hB : 0 ≤ B) {a : ℝ → X} (ha : IsParametrizedAxis h x a)
    (hstep : 0 < dist x (h • x)) :
    HasMonotoneVertexSampling B h x := by
  apply hasMonotoneVertexSampling_of_uniformVertexBlockFellowTravel
    hB (by norm_num : (0 : ℝ) < 1) le_rfl hiso
    ha.isAxisConnector ha.isQuasiGeodesicAxis
  exact hasUniformVertexBlockFellowTravel_of_parametrizedAxis
    hδ hδ0 hgeo hiso hB ha hstep

/-- **DGO Lemma 6.7 for power-vertex segments, reduced exactly to the cited
Bestvina--Fujiwara monotone-sampling proposition.**  The length threshold is
uniform over both translated axes. -/
theorem exists_equal_positive_powers_of_long_powerSegments
    {δ B : ℝ} (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ)
    (hgeo : IsGeodesicSpace X) (hiso : IsIsometricAction G X)
    (hlox : IsLoxodromic h x) (hwpd : IsWPDAt h x)
    (hsampling : HasMonotoneVertexSampling B h x) :
    ∃ L : ℝ, 0 < L ∧ ∀ (p q : PowerAxisSegment h x),
      L ≤ p.length → L ≤ q.length → OrientedClose B p q →
      ∃ r s : ℤ, 0 < r ∧ 0 < s ∧
        p.conjugate ^ r = q.conjugate ^ s := by
  obtain ⟨C₀, C, hC₀, hC, hsampling⟩ := hsampling
  obtain ⟨M₀, hM₀⟩ := dgoLemma67_of_monotone_vertex_samples
    hδ hδ0 hgeo hiso hlox hwpd hC₀ hC
  obtain ⟨N, hN⟩ := hM₀ M₀ le_rfl
  obtain ⟨L, hL, hsampleL⟩ := hsampling M₀ N
  refine ⟨L, hL, ?_⟩
  intro p q hpLen hqLen hclose
  obtain ⟨K, A, D, hA, hD, hbase0, hbaseM, hsamples0, hsamplesM⟩ :=
    hsampleL p q hpLen hqLen hclose
  exact hN p q hbase0 K hbaseM A D hA hD hsamples0 hsamplesM

/-- **DGO Lemma 6.7 for power-vertex segments in the axial case.**  This is
the explicit case proved in Bestvina--Fujiwara Proposition 6, including the
positive-power conclusion. -/
theorem exists_equal_positive_powers_of_long_powerSegments_of_parametrizedAxis
    {δ B : ℝ} (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ)
    (hgeo : IsGeodesicSpace X) (hiso : IsIsometricAction G X)
    (hB : 0 ≤ B) {a : ℝ → X} (ha : IsParametrizedAxis h x a)
    (hstep : 0 < dist x (h • x))
    (hlox : IsLoxodromic h x) (hwpd : IsWPDAt h x) :
    ∃ L : ℝ, 0 < L ∧ ∀ (p q : PowerAxisSegment h x),
      L ≤ p.length → L ≤ q.length → OrientedClose B p q →
      ∃ r s : ℤ, 0 < r ∧ 0 < s ∧
        p.conjugate ^ r = q.conjugate ^ s := by
  apply exists_equal_positive_powers_of_long_powerSegments
    hδ hδ0 hgeo hiso hlox hwpd
  exact hasMonotoneVertexSampling_of_parametrizedAxis
    hδ hδ0 hgeo hiso hB ha hstep

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
      p'.translate = p.translate ∧ q'.translate = q.translate ∧
      M ≤ p'.length ∧ M ≤ q'.length ∧
      OrientedClose (B + 2 * dist x (h • x)) p' q' := by
  obtain ⟨p', hpTranslate, -, -, hp0, hp1, hpLen'⟩ :=
    exists_powerCore_of_add_two_step_le_length hiso hf hstep hM p hpLen
  obtain ⟨q', hqTranslate, -, -, hq0, hq1, hqLen'⟩ :=
    exists_powerCore_of_add_two_step_le_length hiso hf hstep hM q hqLen
  refine ⟨p', q', hpTranslate, hqTranslate, hpLen', hqLen', ?_⟩
  constructor
  · have htri := dist_triangle4 p'.initial p.initialValue q.initialValue q'.initial
    rw [dist_comm p'.initial p.initialValue] at htri
    linarith [hp0, hq0, hclose.1]
  · have htri := dist_triangle4 p'.terminal p.terminalValue q.terminalValue q'.terminal
    rw [dist_comm q.terminalValue q'.terminal] at htri
    linarith [hp1, hq1, hclose.2]

/-- **DGO Lemma 6.7 for arbitrary concatenated-axis segments, reduced to the
exact Bestvina--Fujiwara monotone-sampling contract.**  Trimming costs one
fundamental connector at each end and preserves the conjugates attached to the
two translated axes. -/
theorem exists_equal_positive_powers_of_long_axisSegments
    {δ B : ℝ} (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ)
    (hgeo : IsGeodesicSpace X) (hiso : IsIsometricAction G X)
    {f : ℝ → X} (hf : IsAxisConnector h x f)
    (hstep : 0 < dist x (h • x))
    (hlox : IsLoxodromic h x) (hwpd : IsWPDAt h x)
    (hsampling : HasMonotoneVertexSampling
      (B + 2 * dist x (h • x)) h x) :
    ∃ L : ℝ, 0 < L ∧ ∀ (p q : AxisSegment h x f),
      L ≤ p.length → L ≤ q.length → AxisSegment.OrientedClose B p q →
      ∃ r s : ℤ, 0 < r ∧ 0 < s ∧
        p.conjugate ^ r = q.conjugate ^ s := by
  obtain ⟨M, hM, hpower⟩ :=
    exists_equal_positive_powers_of_long_powerSegments
      hδ hδ0 hgeo hiso hlox hwpd hsampling
  let L : ℝ := M + 2 * dist x (h • x)
  have hL : 0 < L := by
    dsimp [L]
    linarith [dist_nonneg (x := x) (y := h • x)]
  refine ⟨L, hL, ?_⟩
  intro p q hpLen hqLen hclose
  obtain ⟨p', q', hpTranslate, hqTranslate, hpLen', hqLen', hpqClose⟩ :=
    exists_orientedClose_powerCores hiso hf hstep hM.le p q hpLen hqLen hclose
  obtain ⟨r, s, hr, hs, hrs⟩ := hpower p' q' hpLen' hqLen' hpqClose
  refine ⟨r, s, hr, hs, ?_⟩
  dsimp [AxisSegment.conjugate, PowerAxisSegment.conjugate] at hrs ⊢
  rwa [hpTranslate, hqTranslate] at hrs

/-- **DGO Lemma 6.7 for arbitrary segments of a periodic quasi-axis.**
Trimming costs one connector at each end; the resulting power-vertex cores
are handled by the unconditional quasi-axis theorem above. -/
theorem exists_equal_positive_powers_of_long_axisSegments_of_quasiAxis
    {δ B lam c : ℝ} (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ)
    (hgeo : IsGeodesicSpace X) (hiso : IsIsometricAction G X)
    (hB : 0 ≤ B) (hlam : 0 < lam) (hc : 0 ≤ c)
    {f : ℝ → X} (hf : IsAxisConnector h x f)
    (hq : IsQuasiGeodesicAxis lam c h x f)
    (hstep : 0 < dist x (h • x))
    (hlox : IsLoxodromic h x) (hwpd : IsWPDAt h x) :
    ∃ L : ℝ, 0 < L ∧ ∀ (p q : AxisSegment h x f),
      L ≤ p.length → L ≤ q.length → AxisSegment.OrientedClose B p q →
      ∃ r s : ℤ, 0 < r ∧ 0 < s ∧
        p.conjugate ^ r = q.conjugate ^ s := by
  have hB' : 0 ≤ B + 2 * dist x (h • x) := by positivity
  obtain ⟨M, hM, hpower⟩ :=
    exists_equal_positive_powers_of_long_powerSegments_of_quasiAxis
      hδ hδ0 hgeo hiso hB' hlam hc hf hq hstep hlox hwpd
  let L : ℝ := M + 2 * dist x (h • x)
  have hL : 0 < L := by
    dsimp [L]
    linarith [dist_nonneg (x := x) (y := h • x)]
  refine ⟨L, hL, ?_⟩
  intro p q hpLen hqLen hclose
  obtain ⟨p', q', hpTranslate, hqTranslate, hpLen', hqLen', hpqClose⟩ :=
    exists_orientedClose_powerCores hiso hf hstep hM.le p q hpLen hqLen hclose
  obtain ⟨r, s, hr, hs, hrs⟩ := hpower p' q' hpLen' hqLen' hpqClose
  refine ⟨r, s, hr, hs, ?_⟩
  dsimp [AxisSegment.conjugate, PowerAxisSegment.conjugate] at hrs ⊢
  rwa [hpTranslate, hqTranslate] at hrs

/-- **DGO Lemma 6.7 for arbitrary segments of a global geodesic axis.**
Trimming arbitrary endpoints and the axial Bestvina--Fujiwara argument are
assembled here without the abstract monotone-sampling assumption. -/
theorem exists_equal_positive_powers_of_long_axisSegments_of_parametrizedAxis
    {δ B : ℝ} (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ)
    (hgeo : IsGeodesicSpace X) (hiso : IsIsometricAction G X)
    (hB : 0 ≤ B) {a : ℝ → X} (ha : IsParametrizedAxis h x a)
    (hstep : 0 < dist x (h • x))
    (hlox : IsLoxodromic h x) (hwpd : IsWPDAt h x) :
    ∃ L : ℝ, 0 < L ∧ ∀ (p q : AxisSegment h x a),
      L ≤ p.length → L ≤ q.length → AxisSegment.OrientedClose B p q →
      ∃ r s : ℤ, 0 < r ∧ 0 < s ∧
        p.conjugate ^ r = q.conjugate ^ s := by
  have hB' : 0 ≤ B + 2 * dist x (h • x) := by positivity
  apply exists_equal_positive_powers_of_long_axisSegments
    hδ hδ0 hgeo hiso ha.isAxisConnector hstep hlox hwpd
  exact hasMonotoneVertexSampling_of_parametrizedAxis
    hδ hδ0 hgeo hiso hB' ha hstep

end PowerAxisSegment

end GGT
end GroupApproximation
