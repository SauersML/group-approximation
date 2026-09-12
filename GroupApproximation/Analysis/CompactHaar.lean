import GroupApproximation.Analysis.PeterWeylProfinite
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Function.L2Space

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

## The route to `SeparatesPoints`, and what it does *not* need

An earlier plan for this discharge went through Haar convolution on a nonabelian
compact group, `L²` continuity of translation, and compactness of the
convolution operator by Arzelà--Ascoli.  Mathlib has none of the first two --
`Analysis/Convolution` is written for `NormedAddCommGroup`, and there is no
Hilbert--Schmidt theory anywhere in the tree -- so that plan needed a large body
of new API.  **It is avoidable.**  The route below assembles pieces Mathlib
already has.

1. *Integral operators, not convolutions.*  For continuous `k : C × C → ℂ` put
   `T_k f x = ∫ k x y * f y`.  Haar is a probability measure, so
   `‖T_k f‖₂ ≤ ‖k‖_∞ ‖f‖₂` by Cauchy--Schwarz and `k ↦ T_k` is bounded.
2. *Compactness by Stone--Weierstrass, not Arzelà--Ascoli.*  For an elementary
   kernel `k x y = f₀ x * g₀ y` the operator has rank one.  Finite sums of such
   form a star-subalgebra of `C(C × C)` separating points, so
   `ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints`
   makes every continuous `k` a uniform limit of them; `T` is bounded, and
   `isCompactOperator_of_tendsto` closes the set of compact operators under norm
   limits.  No equicontinuity argument and no `L²` translation continuity.
3. *Convolution type only for the symmetry.*  Taking `k x y = φ (x⁻¹ * y)` with
   `φ (x⁻¹) = conj (φ x)` makes `T_k` self-adjoint and translation-equivariant.
4. *Spanning without an approximate identity.*  If `f` is orthogonal to every
   nonzero-eigenvalue eigenspace of every such `T_φ` then `T_φ f = 0` for all
   `φ`; `T_φ f` is continuous and Haar has full support, so it vanishes at `1`,
   giving `∫ φ * f = 0` for every continuous `φ`, whence `f = 0` because
   continuous functions are dense in `L²` for a finite measure
   (`BoundedContinuousFunction.toLp_denseRange`).  This replaces the usual
   approximate-identity step, which is what forced `L²` translation continuity.
5. *Extraction.*  `Analysis/InnerProductSpace/Spectrum` -- outside its
   `FiniteDimensional` section -- gives `finite_dimensional_eigenspace` for a
   nonzero eigenvalue and `orthogonalComplement_iSup_eigenspaces_eq_bot` for a
   compact symmetric operator.  Each nonzero eigenspace is finite dimensional and
   translation invariant, so it carries a finite-dimensional representation; if
   `c` acted trivially on all of them it would act trivially on `L²`, which
   `exists_lp_translate_ne` below forbids.

Stages 1--3 are in this file.  Steps 1--2 and 5 are what remains.
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


/-! ## The regular representation is faithful

Stage three.  Left translation preserves Haar measure, so it acts on `L²` by
linear isometries.  That action is *faithful*: a nonidentity `c` moves the
indicator of the separating set of stage two off itself, because the two sets
are disjoint and the first has positive measure.

This is what stage five needs.  Once the finite-dimensional invariant subspaces
are known to span, "`c` acts trivially on every one of them" gives "`c` acts
trivially on `L²`", and faithfulness turns that into `c = 1` -- which is the
contrapositive of `SeparatesPoints`.
-/

/-- Left translation by `g` preserves the Haar measure of a compact target. -/
theorem CompactTarget.measurePreserving_mul_left (C : CompactTarget)
    (g : C.carrier) :
    MeasurePreserving (fun x => g * x) C.haar C.haar :=
  MeasureTheory.measurePreserving_mul_left C.haar g

/-- **The regular representation is faithful.**  For `c ≠ 1` the translation
action on `L²` moves the indicator of the stage-two separating set. -/
theorem CompactTarget.exists_lp_translate_ne (C : CompactTarget)
    {c : C.carrier} (hc : c ≠ 1) :
    ∃ f : Lp ℂ 2 C.haar,
      Lp.compMeasurePreserving (fun x => c * x)
        (C.measurePreserving_mul_left c) f ≠ f := by
  obtain ⟨U, hUopen, hUpos, hUdisj⟩ :=
    C.exists_pos_measure_disjoint_smul (c := c⁻¹) (by simpa using hc)
  have hUmeas : MeasurableSet U := hUopen.measurableSet
  have hUtop : C.haar U ≠ ⊤ := measure_ne_top _ _
  refine ⟨indicatorConstLp 2 hUmeas hUtop (1 : ℂ), ?_⟩
  intro hEq
  -- both sides are a.e. indicators; compare them on `U`
  have h1 : (Lp.compMeasurePreserving (fun x => c * x)
      (C.measurePreserving_mul_left c) (indicatorConstLp 2 hUmeas hUtop (1 : ℂ)))
      =ᵐ[C.haar] fun x => Set.indicator U (fun _ => (1 : ℂ)) (c * x) := by
    refine (Lp.coeFn_compMeasurePreserving _ _).trans ?_
    exact (indicatorConstLp_coeFn (hs := hUmeas) (hμs := hUtop)).comp_tendsto
      (C.measurePreserving_mul_left c).quasiMeasurePreserving.tendsto_ae
  have h2 : (indicatorConstLp 2 hUmeas hUtop (1 : ℂ) : C.carrier → ℂ)
      =ᵐ[C.haar] Set.indicator U (fun _ => (1 : ℂ)) :=
    indicatorConstLp_coeFn
  have hcomb : (fun x => Set.indicator U (fun _ => (1 : ℂ)) (c * x))
      =ᵐ[C.haar] Set.indicator U (fun _ => (1 : ℂ)) := by
    refine h1.symm.trans ?_
    rw [hEq]
    exact h2
  -- on `U` the left side vanishes by disjointness, so `U` is null
  have hnull : C.haar U = 0 := by
    have hpt : ∀ᵐ x ∂C.haar, x ∈ U → (0 : ℂ) = 1 := by
      filter_upwards [hcomb] with x hx hxU
      have hleft : Set.indicator U (fun _ => (1 : ℂ)) (c * x) = 0 := by
        refine Set.indicator_of_notMem ?_ _
        intro hmem
        exact (Set.disjoint_left.mp hUdisj) ⟨c * x, hmem, by group⟩ hxU
      have hright : Set.indicator U (fun _ => (1 : ℂ)) x = 1 :=
        Set.indicator_of_mem hxU _
      rw [hleft, hright] at hx
      exact hx
    have hae : ∀ᵐ x ∂C.haar, x ∉ U := by
      filter_upwards [hpt] with x hx hxU
      exact zero_ne_one (hx hxU)
    simpa [Set.setOf_mem_eq] using (MeasureTheory.ae_iff.mp hae)
  exact absurd hnull hUpos.ne'

end PeterWeyl
end GroupApproximation
