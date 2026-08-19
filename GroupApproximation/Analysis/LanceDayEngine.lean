import GroupApproximation.Algebra.AmenableMean
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Day's argument: approximate means give an invariant mean

Toward proof-ledger row `RE.05` (the Lance debt).  The compression argument
produces, for every finite set `F` and every `ε > 0`, a finitely additive
normalized positive functional on bounded functions that is `ε`-invariant
under `F` (the hypertrace restricted to multiplication operators).  Day's
classical argument turns such a family into an honest invariant mean: index
the approximants by pairs `(F, n)`, pick an ultrafilter refining the order
filter, and take limits along it.  Additivity, positivity and normalization
pass to the limit verbatim; for a fixed `g` the invariance defect is
eventually below `ε · C`, so the limit is exactly invariant.

`Amenability.ApproxMean` packages the approximants;
`Amenability.hasInvariantMean_of_approxMeans` is the engine.  The
ultrafilter-limit existence step is compactness of `[-C, C]`.

The mean engine in `Analysis/LanceReiterMean.lean` is specific to Reiter
indices; this one consumes bare functionals and is what the compression
composite produces.

## Manuscript status

Infrastructure for the Lance lane; certifies no manuscript step on its own.
`RE.05` remains conditional until the full compression statement lands.
-/

namespace GroupApproximation
namespace Amenability

open Filter Topology

/-- An `ε`-approximately invariant mean: finitely additive, positive and
normalized on bounded functions, and almost invariant under a finite set. -/
structure ApproxMean (G : Type*) [Group G] (F : Finset G) (ε : ℝ) where
  /-- The value of the approximate mean on a function. -/
  eval : (G → ℝ) → ℝ
  eval_add : ∀ f g : G → ℝ, IsBddFun f → IsBddFun g →
    eval (f + g) = eval f + eval g
  eval_nonneg : ∀ f : G → ℝ, IsBddFun f → (∀ x, 0 ≤ f x) → 0 ≤ eval f
  eval_const : ∀ c : ℝ, eval (fun _ ↦ c) = c
  eval_almost_invariant : ∀ g ∈ F, ∀ (f : G → ℝ) (C : ℝ),
    (∀ x, |f x| ≤ C) →
    |eval (fun x ↦ f (g * x)) - eval f| ≤ ε * C

namespace ApproxMean

variable {G : Type*} [Group G] {F : Finset G} {ε : ℝ}
  (m : ApproxMean G F ε)

/-- The approximate mean is monotone on bounded functions.  Verbatim the
`FunctionMean` argument: only additivity, positivity and normalization are
used. -/
theorem eval_mono {f g : G → ℝ} (hf : IsBddFun f) (hg : IsBddFun g)
    (h : ∀ x, f x ≤ g x) : m.eval f ≤ m.eval g := by
  have hd : IsBddFun (g + fun x ↦ -f x) := by
    refine hg.add ?_
    obtain ⟨C, hC⟩ := hf
    exact ⟨C, fun x ↦ by simpa using hC x⟩
  have hnn : 0 ≤ m.eval (g + fun x ↦ -f x) := by
    refine m.eval_nonneg _ hd fun x ↦ ?_
    have := h x
    simp only [Pi.add_apply]
    linarith
  have hneg : m.eval (fun x ↦ -f x) = - m.eval f := by
    have hsum : m.eval (f + fun x ↦ -f x)
        = m.eval f + m.eval (fun x ↦ -f x) := by
      refine m.eval_add _ _ hf ?_
      obtain ⟨C, hC⟩ := hf
      exact ⟨C, fun x ↦ by simpa using hC x⟩
    have hzero : (f + fun x ↦ -f x) = fun _ : G ↦ (0 : ℝ) := by
      funext x
      simp
    rw [hzero, m.eval_const] at hsum
    linarith
  have hadd : m.eval (g + fun x ↦ -f x)
      = m.eval g + m.eval (fun x ↦ -f x) := by
    refine m.eval_add _ _ hg ?_
    obtain ⟨C, hC⟩ := hf
    exact ⟨C, fun x ↦ by simpa using hC x⟩
  rw [hadd, hneg] at hnn
  linarith

/-- The approximate mean is bounded by any uniform bound of its argument. -/
theorem abs_eval_le {f : G → ℝ} {C : ℝ} (hf : IsBddFun f)
    (hC : ∀ x, |f x| ≤ C) : |m.eval f| ≤ C := by
  have hup : m.eval f ≤ C := by
    have := m.eval_mono (f := f) (g := fun _ ↦ C) hf (IsBddFun.const C)
      (fun x ↦ (abs_le.mp (hC x)).2)
    rwa [m.eval_const] at this
  have hlow : -C ≤ m.eval f := by
    have := m.eval_mono (f := fun _ ↦ -C) (g := f) (IsBddFun.const (-C)) hf
      (fun x ↦ (abs_le.mp (hC x)).1)
    rwa [m.eval_const] at this
  exact abs_le.mpr ⟨hlow, hup⟩

end ApproxMean

/-- A bounded real family has a limit along any ultrafilter: compactness
of `[-C, C]`. -/
theorem exists_tendsto_of_bounded {ι : Type*} (U : Ultrafilter ι)
    (x : ι → ℝ) (C : ℝ) (hx : ∀ i, |x i| ≤ C) :
    ∃ L, Filter.Tendsto x ↑U (𝓝 L) := by
  have hmem : Set.Icc (-C) C ∈ Filter.map x ↑U :=
    Filter.mem_map.mpr (Filter.Eventually.of_forall fun i ↦
      ⟨(abs_le.mp (hx i)).1, (abs_le.mp (hx i)).2⟩)
  have hle : ↑(Ultrafilter.map x U) ≤ Filter.principal (Set.Icc (-C) C) := by
    rw [Ultrafilter.coe_map]
    exact Filter.le_principal_iff.mpr hmem
  obtain ⟨L, -, hL⟩ := isCompact_iff_ultrafilter_le_nhds.mp isCompact_Icc
    (Ultrafilter.map x U) hle
  refine ⟨L, ?_⟩
  show Filter.map x ↑U ≤ 𝓝 L
  rw [← Ultrafilter.coe_map]
  exact hL

/-- **Day's argument.**  A family of `ε`-approximately invariant means, one
for every finite set and tolerance, limits along an ultrafilter to an honest
invariant mean. -/
theorem hasInvariantMean_of_approxMeans (G : Type*) [Group G]
    (h : ∀ (F : Finset G) (ε : ℝ), 0 < ε → Nonempty (ApproxMean G F ε)) :
    HasInvariantMean G := by
  classical
  haveI hne : Filter.NeBot (Filter.atTop : Filter (Finset G × ℕ)) :=
    Filter.atTop_neBot
  set U : Ultrafilter (Finset G × ℕ) := Ultrafilter.of Filter.atTop with hU
  have hUle : ↑U ≤ (Filter.atTop : Filter (Finset G × ℕ)) :=
    Ultrafilter.of_le _
  have hεpos : ∀ i : Finset G × ℕ, 0 < (1 : ℝ) / (i.2 + 1) := by
    intro i
    positivity
  let mm : ∀ i : Finset G × ℕ, ApproxMean G i.1 ((1 : ℝ) / (i.2 + 1)) :=
    fun i ↦ (h i.1 ((1 : ℝ) / (i.2 + 1)) (hεpos i)).some
  -- the tolerances vanish along the order filter
  have hsnd : Filter.Tendsto (fun i : Finset G × ℕ ↦ i.2)
      Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop.mpr fun n ↦
      Filter.eventually_atTop.mpr ⟨(∅, n), fun p hp ↦ hp.2⟩
  have hε0 : Filter.Tendsto (fun i : Finset G × ℕ ↦ (1 : ℝ) / (i.2 + 1))
      ↑U (𝓝 0) :=
    ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      hsnd).mono_left hUle
  -- ultrafilter limits of the approximate values
  have hex : ∀ f : G → ℝ, IsBddFun f →
      ∃ L, Filter.Tendsto (fun i ↦ (mm i).eval f) ↑U (𝓝 L) := by
    intro f hf
    obtain ⟨C, hC⟩ := hf
    exact exists_tendsto_of_bounded U _ C
      fun i ↦ (mm i).abs_eval_le ⟨C, hC⟩ hC
  let ev : (G → ℝ) → ℝ := fun f ↦
    if hf : IsBddFun f then (hex f hf).choose else 0
  have hev : ∀ (f : G → ℝ) (hf : IsBddFun f),
      Filter.Tendsto (fun i ↦ (mm i).eval f) ↑U (𝓝 (ev f)) := by
    intro f hf
    have hev1 : ev f = (hex f hf).choose := dif_pos hf
    rw [hev1]
    exact (hex f hf).choose_spec
  refine ⟨⟨ev, ?_, ?_, ?_, ?_⟩⟩
  · -- additivity
    intro f g hf hg
    have h3 := hev (f + g) (hf.add hg)
    have h4 : Filter.Tendsto (fun i ↦ (mm i).eval (f + g)) ↑U
        (𝓝 (ev f + ev g)) := by
      have heq : (fun i ↦ (mm i).eval (f + g))
          = fun i ↦ (mm i).eval f + (mm i).eval g :=
        funext fun i ↦ (mm i).eval_add f g hf hg
      rw [heq]
      exact (hev f hf).add (hev g hg)
    exact tendsto_nhds_unique h3 h4
  · -- positivity
    intro f hf hpos
    exact ge_of_tendsto (hev f hf)
      (Filter.Eventually.of_forall fun i ↦ (mm i).eval_nonneg f hf hpos)
  · -- normalization
    intro c
    have hb : IsBddFun (fun _ : G ↦ c) := IsBddFun.const c
    have h1 := hev _ hb
    have h2 : Filter.Tendsto (fun i ↦ (mm i).eval (fun _ ↦ c)) ↑U
        (𝓝 c) := by
      have heq : (fun i ↦ (mm i).eval (fun _ ↦ c)) = fun _ ↦ c :=
        funext fun i ↦ (mm i).eval_const c
      rw [heq]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique h1 h2
  · -- invariance
    intro g f hf
    obtain ⟨C, hC⟩ := hf
    have hshift : IsBddFun (fun x ↦ f (g * x)) := ⟨C, fun x ↦ hC (g * x)⟩
    have h1 := hev _ hshift
    have h2 := hev f ⟨C, hC⟩
    have habs : Filter.Tendsto
        (fun i ↦ |(mm i).eval (fun x ↦ f (g * x)) - (mm i).eval f|) ↑U
        (𝓝 |ev (fun x ↦ f (g * x)) - ev f|) := (h1.sub h2).abs
    have hbound : ∀ᶠ i in (↑U : Filter (Finset G × ℕ)),
        |(mm i).eval (fun x ↦ f (g * x)) - (mm i).eval f|
          ≤ (1 : ℝ) / (i.2 + 1) * C := by
      have hmem : ∀ᶠ i in (Filter.atTop : Filter (Finset G × ℕ)),
          g ∈ i.1 :=
        Filter.eventually_atTop.mpr ⟨({g}, 0), fun p hp ↦
          Finset.singleton_subset_iff.mp hp.1⟩
      exact (hmem.filter_mono hUle).mono fun i hi ↦
        (mm i).eval_almost_invariant g hi f C hC
    have hε0C : Filter.Tendsto
        (fun i : Finset G × ℕ ↦ (1 : ℝ) / (i.2 + 1) * C) ↑U (𝓝 0) := by
      have := hε0.mul_const C
      simpa using this
    have hle0 : |ev (fun x ↦ f (g * x)) - ev f| ≤ 0 :=
      le_of_tendsto_of_tendsto habs hε0C hbound
    have hzero : ev (fun x ↦ f (g * x)) - ev f = 0 :=
      abs_eq_zero.mp (le_antisymm hle0 (abs_nonneg _))
    exact sub_eq_zero.mp hzero

end Amenability
end GroupApproximation
