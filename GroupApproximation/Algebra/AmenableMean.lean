import GroupApproximation.Algebra.Amenable

/-!
# Invariant means on functions, and amenability of extensions

`Algebra.Amenable` defines amenability by a finitely additive invariant
measure on subsets.  That formulation is enough for finiteness, subgroups
and directed unions, but *not* for extensions: the extension argument
integrates, for each coset, the measure of a slice as the coset varies,
and a slice measure is not the indicator of anything.  What it needs is a
mean on bounded functions.

This file supplies that formulation and proves the extension theorem with
it: if a normal subgroup and the quotient both carry invariant means, so
does the group.  The proof is the classical iterated mean --- average over
the normal subgroup first, then over the quotient --- and its only
delicate point is that the inner average does not depend on which coset
representative is chosen, which is exactly left invariance of the inner
mean.

Restricting the mean to indicator functions recovers an invariant measure,
so this formulation dominates the other one.
-/

namespace GroupApproximation
namespace Amenability

/-- Boundedness of a real-valued function, stated without topology. -/
def IsBddFun {G : Type*} (f : G → ℝ) : Prop := ∃ C : ℝ, ∀ x, |f x| ≤ C

theorem IsBddFun.const {G : Type*} (c : ℝ) : IsBddFun (fun _ : G ↦ c) :=
  ⟨|c|, fun _ ↦ le_rfl⟩

theorem IsBddFun.add {G : Type*} {f g : G → ℝ} (hf : IsBddFun f)
    (hg : IsBddFun g) : IsBddFun (f + g) := by
  obtain ⟨C, hC⟩ := hf
  obtain ⟨D, hD⟩ := hg
  refine ⟨C + D, fun x ↦ ?_⟩
  have h1 := hC x
  have h2 := hD x
  rw [abs_le] at h1 h2 ⊢
  simp only [Pi.add_apply]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- A left-invariant mean on the bounded real functions of a group. -/
structure FunctionMean (G : Type*) [Group G] where
  /-- The value of the mean on a function. -/
  eval : (G → ℝ) → ℝ
  eval_add : ∀ f g : G → ℝ, IsBddFun f → IsBddFun g →
    eval (f + g) = eval f + eval g
  eval_nonneg : ∀ f : G → ℝ, IsBddFun f → (∀ x, 0 ≤ f x) → 0 ≤ eval f
  eval_const : ∀ c : ℝ, eval (fun _ ↦ c) = c
  eval_invariant : ∀ (g : G) (f : G → ℝ), IsBddFun f →
    eval (fun x ↦ f (g * x)) = eval f

namespace FunctionMean

variable {G : Type*} [Group G] (m : FunctionMean G)

/-- The mean is monotone on bounded functions. -/
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
    have hsum : m.eval (f + fun x ↦ -f x) = m.eval f + m.eval (fun x ↦ -f x) := by
      refine m.eval_add _ _ hf ?_
      obtain ⟨C, hC⟩ := hf
      exact ⟨C, fun x ↦ by simpa using hC x⟩
    have hzero : (f + fun x ↦ -f x) = fun _ : G ↦ (0 : ℝ) := by
      funext x
      simp
    rw [hzero, m.eval_const] at hsum
    linarith
  have hadd : m.eval (g + fun x ↦ -f x) = m.eval g + m.eval (fun x ↦ -f x) := by
    refine m.eval_add _ _ hg ?_
    obtain ⟨C, hC⟩ := hf
    exact ⟨C, fun x ↦ by simpa using hC x⟩
  rw [hadd, hneg] at hnn
  linarith

/-- A mean is bounded by any uniform bound of its argument. -/
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

end FunctionMean

/-- A group is amenable in the mean sense when it carries an invariant
mean on bounded functions. -/
def HasInvariantMean (G : Type*) [Group G] : Prop := Nonempty (FunctionMean G)

/-! ## Finite groups -/

/-- Averaging over a finite group is an invariant mean. -/
noncomputable def finiteFunctionMean (G : Type*) [Group G] [Fintype G] :
    FunctionMean G where
  eval f := (∑ x : G, f x) / (Fintype.card G : ℝ)
  eval_add f g _ _ := by
    simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib, add_div]
  eval_nonneg f _ hf := by
    have hs : 0 ≤ ∑ x : G, f x := Finset.sum_nonneg fun x _ ↦ hf x
    positivity
  eval_const c := by
    have hpos : (0 : ℝ) < (Fintype.card G : ℝ) := by
      have : 0 < Fintype.card G := Fintype.card_pos
      exact_mod_cast this
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  eval_invariant g f _ := by
    congr 1
    exact Fintype.sum_bijective (fun x ↦ g * x) (Group.mulLeft_bijective g) _ _
      (fun _ ↦ rfl)

/-! ## The mean dominates the measure -/

theorem indicator_bdd {G : Type*} (A : Set G) :
    IsBddFun (A.indicator (fun _ ↦ (1 : ℝ))) := by
  refine ⟨1, fun x ↦ ?_⟩
  by_cases hx : x ∈ A
  · simp [hx]
  · simp [hx]

/-- Restricting a mean to indicator functions gives an invariant measure,
so the mean formulation implies the measure formulation. -/
noncomputable def FunctionMean.toInvariantMean {G : Type*} [Group G]
    (m : FunctionMean G) : InvariantMean G where
  measure A := m.eval (A.indicator (fun _ ↦ (1 : ℝ)))
  nonneg A :=
    m.eval_nonneg _ (indicator_bdd A)
      (fun x ↦ Set.indicator_nonneg (fun _ _ ↦ zero_le_one) x)
  measure_univ := by
    have h : (Set.univ : Set G).indicator (fun _ ↦ (1 : ℝ)) = fun _ ↦ (1 : ℝ) := by
      funext x
      simp
    rw [h, m.eval_const]
  additive A B hAB := by
    have h : (A ∪ B).indicator (fun _ ↦ (1 : ℝ)) =
        A.indicator (fun _ ↦ (1 : ℝ)) + B.indicator (fun _ ↦ (1 : ℝ)) := by
      funext x
      by_cases hxA : x ∈ A
      · have hxB : x ∉ B := fun hxB ↦ (Set.disjoint_left.mp hAB) hxA hxB
        simp [hxA, hxB, Set.mem_union]
      · by_cases hxB : x ∈ B <;>
          simp [hxA, hxB, Set.mem_union]
    rw [h]
    exact m.eval_add _ _ (indicator_bdd A) (indicator_bdd B)
  invariant g A := by
    have h : (fun x ↦ ((fun y ↦ g * y) '' A).indicator (fun _ ↦ (1 : ℝ)) (g * x)) =
        A.indicator (fun _ ↦ (1 : ℝ)) := by
      funext x
      by_cases hx : x ∈ A
      · have : g * x ∈ (fun y ↦ g * y) '' A := ⟨x, hx, rfl⟩
        simp [hx]
      · have : g * x ∉ (fun y ↦ g * y) '' A := by
          rintro ⟨a, ha, hga⟩
          exact hx (by simpa using mul_left_cancel hga ▸ ha)
        simp [hx]
    rw [← m.eval_invariant g _ (indicator_bdd _), h]

/-- Amenability in the mean sense implies amenability in the measure
sense. -/
theorem isAmenable_of_hasInvariantMean {G : Type*} [Group G]
    (h : HasInvariantMean G) : IsAmenable G := by
  obtain ⟨m⟩ := h
  exact ⟨m.toInvariantMean⟩

/-! ## Extensions -/

section Extension

variable {G : Type*} [Group G] (N : Subgroup G) [N.Normal]

/-- The inner average of a function along one coset. -/
noncomputable def cosetAverage (mN : FunctionMean N) (f : G → ℝ)
    (x : G ⧸ N) : ℝ :=
  mN.eval fun n : N ↦ f (Quotient.out x * (n : G))

omit [N.Normal] in
theorem cosetAverage_bdd (mN : FunctionMean N) {f : G → ℝ} {C : ℝ}
    (hC : ∀ y, |f y| ≤ C) : ∀ x, |cosetAverage N mN f x| ≤ C := by
  intro x
  refine mN.abs_eval_le ⟨C, fun n ↦ hC _⟩ ?_
  intro n
  exact hC _

/-- **Amenability is closed under extensions.**  If a normal subgroup and
the quotient both carry invariant means, so does the group: average over
the subgroup first, then over the quotient.  Independence of the coset
representative is exactly left invariance of the inner mean. -/
theorem hasInvariantMean_of_extension (hN : HasInvariantMean N)
    (hQ : HasInvariantMean (G ⧸ N)) : HasInvariantMean G := by
  classical
  obtain ⟨mN⟩ := hN
  obtain ⟨mQ⟩ := hQ
  refine ⟨{ eval := fun f ↦ mQ.eval (cosetAverage N mN f)
            eval_add := ?_
            eval_nonneg := ?_
            eval_const := ?_
            eval_invariant := ?_ }⟩
  · -- additivity
    intro f g hf hg
    obtain ⟨C, hC⟩ := hf
    obtain ⟨D, hD⟩ := hg
    have hsplit : cosetAverage N mN (f + g) =
        cosetAverage N mN f + cosetAverage N mN g := by
      funext x
      simp only [cosetAverage, Pi.add_apply]
      exact mN.eval_add _ _ ⟨C, fun n ↦ hC _⟩ ⟨D, fun n ↦ hD _⟩
    rw [hsplit]
    exact mQ.eval_add _ _ ⟨C, cosetAverage_bdd N mN hC⟩
      ⟨D, cosetAverage_bdd N mN hD⟩
  · -- positivity
    intro f hf hpos
    obtain ⟨C, hC⟩ := hf
    refine mQ.eval_nonneg _ ⟨C, cosetAverage_bdd N mN hC⟩ fun x ↦ ?_
    exact mN.eval_nonneg _ ⟨C, fun n ↦ hC _⟩ fun n ↦ hpos _
  · -- constants
    intro c
    have hconst : cosetAverage N mN (fun _ ↦ c) = fun _ ↦ c := by
      funext x
      simp only [cosetAverage]
      exact mN.eval_const c
    rw [hconst, mQ.eval_const]
  · -- invariance
    intro g f hf
    obtain ⟨C, hC⟩ := hf
    have hshift : cosetAverage N mN (fun y ↦ f (g * y)) =
        fun x ↦ cosetAverage N mN f ((QuotientGroup.mk g : G ⧸ N) * x) := by
      funext x
      have hcoset : (Quotient.out ((QuotientGroup.mk g : G ⧸ N) * x))⁻¹ *
          (g * Quotient.out x) ∈ N := by
        have hq : (QuotientGroup.mk (Quotient.out ((QuotientGroup.mk g : G ⧸ N) * x)) :
            G ⧸ N) = (QuotientGroup.mk g : G ⧸ N) * x := QuotientGroup.out_eq' _
        have hq2 : (QuotientGroup.mk (g * Quotient.out x) : G ⧸ N) =
            (QuotientGroup.mk g : G ⧸ N) * x := by
          rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
        exact QuotientGroup.eq.mp (hq.trans hq2.symm)
      set k : N := ⟨_, hcoset⟩ with hk
      have hrewrite : ∀ n : N,
          f (g * (Quotient.out x * (n : G))) =
            f (Quotient.out ((QuotientGroup.mk g : G ⧸ N) * x) * ((k * n : N) : G)) := by
        intro n
        congr 1
        have hkv : ((k * n : N) : G) =
            (Quotient.out ((QuotientGroup.mk g : G ⧸ N) * x))⁻¹ *
              (g * (Quotient.out x * (n : G))) := by
          show ((k : G) * (n : G)) = _
          rw [hk]
          show ((Quotient.out ((QuotientGroup.mk g : G ⧸ N) * x))⁻¹ *
            (g * Quotient.out x)) * (n : G) = _
          rw [mul_assoc, mul_assoc]
        rw [hkv, mul_inv_cancel_left]
      simp only [cosetAverage]
      rw [show (fun n : N ↦ f (g * (Quotient.out x * (n : G)))) =
        (fun n : N ↦ f (Quotient.out ((QuotientGroup.mk g : G ⧸ N) * x) *
          ((k * n : N) : G))) from funext hrewrite]
      exact mN.eval_invariant k
        (fun n : N ↦ f (Quotient.out ((QuotientGroup.mk g : G ⧸ N) * x) * (n : G)))
        ⟨C, fun n ↦ hC _⟩
    rw [hshift]
    exact mQ.eval_invariant _ _ ⟨C, cosetAverage_bdd N mN hC⟩

end Extension

/-! ## Directed unions, in the mean formulation -/

section DirectedMean

open Filter Topology

variable {ι : Type*} [Nonempty ι] [SemilatticeSup ι] {G : Type*} [Group G]
  (K : ι → Subgroup G) (m : ∀ i, FunctionMean (K i))

omit [Nonempty ι] in
/-- The averages of the restrictions stay in a fixed interval, so they
converge along the ultrafilter. -/
theorem directedExists (hι : Nonempty ι) {f : G → ℝ} (h : IsBddFun f) :
    ∃ L ∈ Set.Icc (-Classical.choose h) (Classical.choose h),
      Tendsto (fun i ↦ (m i).eval fun x : K i ↦ f (x : G))
        (indexUltrafilter ι hι) (nhds L) :=
  exists_ultrafilter_tendsto_Icc _ _ fun i ↦
    Set.mem_Icc.mpr (abs_le.mp
      ((m i).abs_eval_le ⟨Classical.choose h, fun _ ↦ Classical.choose_spec h _⟩
        fun _ ↦ Classical.choose_spec h _))

/-- The mean of the restrictions, along the fixed ultrafilter. -/
noncomputable def directedEvalOf (hι : Nonempty ι) {f : G → ℝ}
    (h : IsBddFun f) : ℝ :=
  (directedExists K m hι h).choose

omit [Nonempty ι] in
theorem directedEvalOf_tendsto (hι : Nonempty ι) {f : G → ℝ}
    (h : IsBddFun f) :
    Tendsto (fun i ↦ (m i).eval fun x : K i ↦ f (x : G))
      (indexUltrafilter ι hι) (nhds (directedEvalOf K m hι h)) :=
  (directedExists K m hι h).choose_spec.2

open Classical in
/-- Extended by zero to unbounded functions. -/
noncomputable def directedEval (hι : Nonempty ι) (f : G → ℝ) : ℝ :=
  if h : IsBddFun f then directedEvalOf K m hι h else 0

omit [Nonempty ι] in
theorem directedEval_tendsto (hι : Nonempty ι) {f : G → ℝ}
    (hf : IsBddFun f) :
    Tendsto (fun i ↦ (m i).eval fun x : K i ↦ f (x : G))
      (indexUltrafilter ι hι) (nhds (directedEval K m hι f)) := by
  classical
  simp only [directedEval, dif_pos hf]
  exact directedEvalOf_tendsto K m hι hf

omit [Nonempty ι] in
include m in
/-- **Directed unions in the mean formulation.** -/
theorem hasInvariantMean_of_directed (hι : Nonempty ι) (hmono : Monotone K)
    (hcover : ∀ g : G, ∃ i, g ∈ K i) : HasInvariantMean G := by
  classical
  refine ⟨{ eval := directedEval K m hι
            eval_add := ?_
            eval_nonneg := ?_
            eval_const := ?_
            eval_invariant := ?_ }⟩
  · intro f g hf hg
    refine tendsto_nhds_unique (directedEval_tendsto K m hι (hf.add hg)) ?_
    have hsplit : (fun i ↦ (m i).eval fun x : K i ↦ (f + g) (x : G)) =
        fun i ↦ ((m i).eval fun x : K i ↦ f (x : G)) +
          ((m i).eval fun x : K i ↦ g (x : G)) := by
      funext i
      obtain ⟨C, hC⟩ := hf
      obtain ⟨D, hD⟩ := hg
      exact (m i).eval_add _ _ ⟨C, fun x ↦ hC _⟩ ⟨D, fun x ↦ hD _⟩
    rw [hsplit]
    exact (directedEval_tendsto K m hι hf).add (directedEval_tendsto K m hι hg)
  · intro f hf hpos
    refine ge_of_tendsto (directedEval_tendsto K m hι hf)
      (Filter.Eventually.of_forall fun i ↦ ?_)
    obtain ⟨C, hC⟩ := hf
    exact (m i).eval_nonneg _ ⟨C, fun x ↦ hC _⟩ fun x ↦ hpos _
  · intro c
    refine tendsto_nhds_unique
      (directedEval_tendsto K m hι (IsBddFun.const c)) ?_
    have hconst : (fun i ↦ (m i).eval fun _ : K i ↦ c) = fun _ ↦ c := by
      funext i
      exact (m i).eval_const c
    rw [hconst]
    exact tendsto_const_nhds
  · intro g f hf
    obtain ⟨C, hC⟩ := hf
    refine tendsto_nhds_unique
      (directedEval_tendsto K m hι ⟨C, fun x ↦ hC _⟩) ?_
    obtain ⟨i₀, hi₀⟩ := hcover g
    have heq : ∀ i, i₀ ≤ i →
        ((m i).eval fun x : K i ↦ f (g * (x : G))) =
          ((m i).eval fun x : K i ↦ f (x : G)) := by
      intro i hi
      have hgi : g ∈ K i := hmono hi hi₀
      have := (m i).eval_invariant (⟨g, hgi⟩ : K i)
        (fun x : K i ↦ f (x : G)) ⟨C, fun x ↦ hC _⟩
      simpa using this
    have hev : (fun i ↦ (m i).eval fun x : K i ↦ f (g * (x : G))) =ᶠ[
        (indexUltrafilter ι hι : Filter ι)]
        fun i ↦ (m i).eval fun x : K i ↦ f (x : G) := by
      refine Filter.mem_of_superset
        (indexUltrafilter_le hι (Filter.eventually_ge_atTop i₀)) ?_
      intro i hi
      exact heq i hi
    exact (directedEval_tendsto K m hι ⟨C, fun x ↦ hC _⟩).congr' hev.symm

end DirectedMean

/-- **Locally finite groups carry invariant means.** -/
theorem hasInvariantMean_of_locallyFinite {G : Type*} [Group G]
    (h : ∀ S : Finset G, Finite (Subgroup.closure (S : Set G))) :
    HasInvariantMean G := by
  classical
  refine hasInvariantMean_of_directed
    (K := fun S : Finset G ↦ Subgroup.closure (S : Set G))
    (fun S ↦ ?_) ⟨∅⟩ ?_ ?_
  · haveI := h S
    haveI : Fintype (Subgroup.closure (S : Set G)) := Fintype.ofFinite _
    exact finiteFunctionMean _
  · intro S T hST
    exact Subgroup.closure_mono (Finset.coe_subset.mpr hST)
  · intro g
    exact ⟨{g}, Subgroup.subset_closure (by simp)⟩

end Amenability
end GroupApproximation
