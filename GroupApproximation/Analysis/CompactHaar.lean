import GroupApproximation.Analysis.PeterWeylProfinite
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Haar probability measure on a compact target

Stage one of discharging `PeterWeyl.SeparatesPoints`, the single classical input
still standing between `Sofic/FiveRadicalsCoincide.four_radicals_eq_and_bohr_bounds`
and the full six-way equality
`ker Φ = Rad_MF = Rad_fd = Rad_lin = Rad_Bohr = Res_fin`.

`Analysis/PeterWeylProfinite.CompactTarget` bundles a group with a compact
Hausdorff topology and nothing measure-theoretic, because the Bohr residual is
defined without any.  Every later stage -- the regular representation on `L²`,
the convolution operator, its compactness -- needs an invariant measure, so this
file installs one and records exactly the properties those stages consume.

The two instances are the whole content: the Borel σ-algebra makes a
`CompactTarget` a `BorelSpace`, and Mathlib's `haarMeasure` then applies with no
further hypotheses.  In particular **no second countability is required** --
`MeasureTheory/Measure/Haar/Basic` introduces `SecondCountableTopology` only well
after the construction -- which matters here because a `CompactTarget` is an
arbitrary compact group, not a metrizable one.

Normalisation is free rather than a rescaling: `PositiveCompacts` on a compact
nonempty space is inhabited by the whole space, and `haarMeasure_self` says the
measure of the chosen positive compact is `1`, so `haarMeasure default` is
already a probability measure.
-/

namespace GroupApproximation
namespace PeterWeyl

open MeasureTheory Measure TopologicalSpace

/-- The Borel σ-algebra of a compact target. -/
instance CompactTarget.instMeasurableSpace (C : CompactTarget) :
    MeasurableSpace C.carrier := borel _

/-- A compact target carries the Borel σ-algebra by construction. -/
instance CompactTarget.instBorelSpace (C : CompactTarget) : BorelSpace C.carrier :=
  ⟨rfl⟩

/-- A compact target is nonempty: it contains the identity. -/
instance CompactTarget.instNonempty (C : CompactTarget) : Nonempty C.carrier :=
  ⟨1⟩

/-- **Haar measure on a compact target.**  The whole space is a positive compact,
so the canonical `PositiveCompacts` normalisation already gives total mass one. -/
noncomputable def CompactTarget.haar (C : CompactTarget) : Measure C.carrier :=
  haarMeasure default

instance CompactTarget.instIsHaarMeasure (C : CompactTarget) :
    IsHaarMeasure C.haar :=
  isHaarMeasure_haarMeasure _

instance CompactTarget.instIsMulLeftInvariant (C : CompactTarget) :
    C.haar.IsMulLeftInvariant :=
  isMulLeftInvariant_haarMeasure _

/-- The Haar measure of a compact target is a probability measure. -/
instance CompactTarget.instIsProbabilityMeasure (C : CompactTarget) :
    IsProbabilityMeasure C.haar := by
  constructor
  have h : C.haar (default : PositiveCompacts C.carrier) = 1 := haarMeasure_self
  have huniv : ((default : PositiveCompacts C.carrier) : Set C.carrier) = Set.univ :=
    rfl
  rwa [huniv] at h

/-- The Haar measure of a compact target is finite. -/
instance CompactTarget.instIsFiniteMeasure (C : CompactTarget) :
    IsFiniteMeasure C.haar := inferInstance

/-- Haar measure on a compact target is nonzero: the whole space has mass one. -/
theorem CompactTarget.haar_univ (C : CompactTarget) :
    C.haar Set.univ = 1 := measure_univ


/-! ## Separating a nonidentity element by a positive-measure set

The regular representation of a compact target on its `L²` space is faithful,
and this is the geometric input: a nonidentity element moves some neighbourhood
of the identity off itself, and Haar measure gives that neighbourhood positive
mass.  Stage three consumes it to know that `λ c = 1` forces `c = 1`, which is
what turns "every finite-dimensional invariant subspace sees `c` trivially" into
"`c` is trivial".
-/

/-- **A nonidentity element translates some identity neighbourhood off itself.**
Hausdorffness makes `{c}ᶜ` a neighbourhood of `1`, splitting it gives a
symmetric `U` with `U * U ⊆ {c}ᶜ`, and `c * u₁ = u₂` would exhibit `c` inside
`U * U`. -/
theorem CompactTarget.exists_open_nhds_one_disjoint_smul (C : CompactTarget)
    {c : C.carrier} (hc : c ≠ 1) :
    ∃ U : Set C.carrier, IsOpen U ∧ (1 : C.carrier) ∈ U ∧
      Disjoint ((fun x => c * x) '' U) U := by
  have hmem : ({c}ᶜ : Set C.carrier) ∈ nhds (1 : C.carrier) :=
    isClosed_singleton.isOpen_compl.mem_nhds (by simpa using (Ne.symm hc))
  obtain ⟨V, hV, hVsub⟩ := exists_nhds_one_split hmem
  have hVinv : V⁻¹ ∈ nhds (1 : C.carrier) := by
    simpa using inv_mem_nhds_one (G := C.carrier) hV
  have hinter : V ∩ V⁻¹ ∈ nhds (1 : C.carrier) := Filter.inter_mem hV hVinv
  refine ⟨interior (V ∩ V⁻¹), isOpen_interior,
    mem_interior_iff_mem_nhds.mpr hinter, ?_⟩
  rw [Set.disjoint_left]
  rintro x ⟨u, hu, rfl⟩ hx
  have huV : u ∈ V ∩ V⁻¹ := interior_subset hu
  have hxV : c * u ∈ V ∩ V⁻¹ := interior_subset hx
  have hcmem : (c * u) * u⁻¹ ∈ ({c}ᶜ : Set C.carrier) :=
    hVsub _ hxV.1 _ (by simpa using huV.2)
  rw [mul_inv_cancel_right] at hcmem
  exact hcmem rfl

/-- **The separating set has positive Haar measure.**  Combining the previous
lemma with positivity of Haar on nonempty open sets. -/
theorem CompactTarget.exists_pos_measure_disjoint_smul (C : CompactTarget)
    {c : C.carrier} (hc : c ≠ 1) :
    ∃ U : Set C.carrier, IsOpen U ∧ 0 < C.haar U ∧
      Disjoint ((fun x => c * x) '' U) U := by
  obtain ⟨U, hUopen, hU1, hUdisj⟩ := C.exists_open_nhds_one_disjoint_smul hc
  exact ⟨U, hUopen, hUopen.measure_pos _ ⟨1, hU1⟩, hUdisj⟩

end PeterWeyl
end GroupApproximation
