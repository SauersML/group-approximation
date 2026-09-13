import Mathlib.Logic.Relation
import Mathlib.Logic.Function.Conjugate
import Mathlib.Algebra.Group.End
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.UniformSpace.Compact
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import GroupApproximation.Meta.AxiomGuard

/-!
# Chain recurrence

The chain-recurrent set `CR(T)` of sec:chain-core, with the basic facts the chain-recurrent
core (lem:chain-core-models) uses:

* the printed metric definition agrees with the entourage definition, so on a compact space
  it does not depend on the compatible metric;
* `CR(T)` is closed, and invariant under a homeomorphism;
* for `T(P) ⊆ P` the defect `P \ T(P)` is wandering;
* chain recurrence passes to factors.
-/

open scoped Uniformity

namespace GroupApproximation.Dynamics

section Chains

variable {X Y : Type*}

/-- One step of an entourage chain: `T a` is `V`-close to `b`. -/
def ChainStep (T : X → X) (V : Set (X × X)) (a b : X) : Prop := (T a, b) ∈ V

theorem ChainStep.mono {T : X → X} {V W : Set (X × X)} (h : V ⊆ W) :
    ChainStep T V ≤ ChainStep T W := fun _ _ hab => h hab

/-- A chain of positive length is a sequence `x_0, x_1, …, x_r` with `r ≥ 1`. -/
theorem transGen_iff_exists_seq {R : X → X → Prop} {a b : X} :
    Relation.TransGen R a b ↔
      ∃ r ≥ 1, ∃ xs : ℕ → X, xs 0 = a ∧ xs r = b ∧ ∀ i < r, R (xs i) (xs (i + 1)) := by
  constructor
  · intro h
    induction h using Relation.TransGen.head_induction_on with
    | @single a hab =>
      refine ⟨1, le_rfl, (fun i => match i with | 0 => a | _ + 1 => b), rfl, rfl, ?_⟩
      intro i hi
      obtain rfl : i = 0 := by omega
      exact hab
    | @head a c hac _ ih =>
      obtain ⟨r, -, xs, h0, hr', hxs⟩ := ih
      refine ⟨r + 1, by omega, (fun i => match i with | 0 => a | j + 1 => xs j), rfl, hr', ?_⟩
      intro i hi
      cases i with
      | zero =>
        show R a (xs 0)
        rw [h0]
        exact hac
      | succ j => exact hxs j (by omega)
  · rintro ⟨r, hr, xs, rfl, rfl, hxs⟩
    obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
    clear hr
    induction k with
    | zero => exact Relation.TransGen.single (hxs 0 (by omega))
    | succ k ih => exact (ih fun i hi => hxs i (by omega)).tail (hxs (k + 1) (by omega))

/-- Chains transport along a map carrying steps to steps. -/
theorem transGen_chainStep_map {T : X → X} {S : Y → Y} {U : Set (X × X)} {V : Set (Y × Y)}
    (f : X → Y) (hf : ∀ a b, ChainStep T U a b → ChainStep S V (f a) (f b)) {a b : X}
    (h : Relation.TransGen (ChainStep T U) a b) :
    Relation.TransGen (ChainStep S V) (f a) (f b) := by
  induction h with
  | single hab => exact Relation.TransGen.single (hf _ _ hab)
  | tail _ hbc ih => exact ih.tail (hf _ _ hbc)

end Chains

section Uniform

variable {X Y : Type*} [UniformSpace X]

/-- Chain recurrence for a uniform structure: for every entourage `V` there is a chain of
positive length from `x` back to `x` whose steps are `V`-close. For a metric this is the
printed notion `IsMetricChainRecurrent`, by `isChainRecurrent_iff_metric`. -/
def IsChainRecurrent (T : X → X) (x : X) : Prop :=
  ∀ V ∈ 𝓤 X, Relation.TransGen (ChainStep T V) x x

/-- Printed (sec:chain-core): "Write $Y=\operatorname{CR}(T)$ for the chain-recurrent set." -/
def chainRecurrentSet (T : X → X) : Set X := {x | IsChainRecurrent T x}

theorem mem_chainRecurrentSet {T : X → X} {x : X} :
    x ∈ chainRecurrentSet T ↔ IsChainRecurrent T x := Iff.rfl

/-- Printed (lem:chain-core-models, the closed part): "The set $Y$ is nonempty, closed and
invariant, and $R_Y$ is LEF." -/
theorem isClosed_chainRecurrentSet [CompactSpace X] {T : X → X} (hT : Continuous T) :
    IsClosed (chainRecurrentSet T) := by
  have hTu : UniformContinuous T := CompactSpace.uniformContinuous_of_continuous hT
  refine isClosed_of_closure_subset fun x hx => ?_
  intro V hV
  obtain ⟨W₁, hW₁, hW₁V⟩ := comp_mem_uniformity_sets hV
  obtain ⟨W, hW, hWW₁⟩ := comp_mem_uniformity_sets hW₁
  have hsub : W ⊆ W₁ := (subset_comp_self_of_mem_uniformity hW).trans hWW₁
  have hsub₁ : W₁ ⊆ V := (subset_comp_self_of_mem_uniformity hW₁).trans hW₁V
  have hU := Filter.inter_mem (Filter.mem_map.1 (hTu hW))
    (Filter.mem_map.1 (symm_le_uniformity hW))
  obtain ⟨y, hyU, hy⟩ := mem_closure_iff_nhds.1 hx _ (UniformSpace.ball_mem_nhds x hU)
  obtain ⟨hxy, hyx⟩ : (T x, T y) ∈ W ∧ (y, x) ∈ W := hyU
  obtain ⟨b, hyb, hby⟩ := Relation.TransGen.head'_iff.1 (hy W hW)
  have hxb : ChainStep T W₁ x b := hWW₁ (SetRel.prodMk_mem_comp hxy hyb)
  have hxy' : Relation.TransGen (ChainStep T W₁) x y :=
    Relation.TransGen.head' hxb (Relation.ReflTransGen.mono (ChainStep.mono hsub) _ _ hby)
  obtain ⟨c, hxc, hcy⟩ := Relation.TransGen.tail'_iff.1 hxy'
  exact Relation.TransGen.tail' (Relation.ReflTransGen.mono (ChainStep.mono hsub₁) _ _ hxc)
    (hW₁V (SetRel.prodMk_mem_comp hcy (hsub hyx)))

/-- Printed (lem:chain-core-models, the invariant part): "The set $Y$ is nonempty, closed and
invariant, and $R_Y$ is LEF." -/
theorem apply_mem_chainRecurrentSet_iff [CompactSpace X] (T : X ≃ₜ X) {x : X} :
    T x ∈ chainRecurrentSet T ↔ x ∈ chainRecurrentSet T := by
  have hT : UniformContinuous T := CompactSpace.uniformContinuous_of_continuous T.continuous
  have hS : UniformContinuous T.symm :=
    CompactSpace.uniformContinuous_of_continuous T.continuous_symm
  constructor
  · intro hx V hV
    have h : Relation.TransGen (ChainStep T V) (T.symm (T x)) (T.symm (T x)) :=
      transGen_chainStep_map T.symm (fun a b hab => by
        have hab' : (T.symm (T a), T.symm b) ∈ V := hab
        change (T (T.symm a), T.symm b) ∈ V
        rw [T.apply_symm_apply]
        rwa [T.symm_apply_apply] at hab') (hx _ (Filter.mem_map.1 (hS hV)))
    rwa [T.symm_apply_apply] at h
  · intro hx V hV
    exact transGen_chainStep_map T (fun a b hab => by exact hab)
      (hx _ (Filter.mem_map.1 (hT hV)))

/-- `CR(T)` is invariant: `T(CR(T)) = CR(T)`. -/
theorem image_chainRecurrentSet [CompactSpace X] (T : X ≃ₜ X) :
    T '' chainRecurrentSet T = chainRecurrentSet T := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (apply_mem_chainRecurrentSet_iff T).2 hx
  · intro hy
    refine ⟨T.symm y, (apply_mem_chainRecurrentSet_iff T).1 ?_, T.apply_symm_apply y⟩
    rwa [T.apply_symm_apply]

/-- Printed (proof of lem:chain-core-models): "Chain recurrence passes to factors, so
$Y\subseteq Y_*$." -/
theorem mapsTo_chainRecurrentSet [CompactSpace X] [UniformSpace Y] {T : X → X} {S : Y → Y}
    {π : X → Y} (hπ : Continuous π) (h : Function.Semiconj π T S) :
    Set.MapsTo π (chainRecurrentSet T) (chainRecurrentSet S) := by
  have hu : UniformContinuous π := CompactSpace.uniformContinuous_of_continuous hπ
  intro x hx V hV
  exact transGen_chainStep_map π (fun a b hab => by
    change (S (π a), π b) ∈ V
    rw [← h a]
    exact hab) (hx _ (Filter.mem_map.1 (hu hV)))

end Uniform

section Metric

variable {X : Type*}

/-- Printed (sec:chain-core): "For a compatible metric on $X$, a point $x$ is
\emph{chain recurrent} if, for every $\varepsilon>0$, there are $r\ge1$ and
$x=x_0,x_1,\dots,x_r=x$ with $d(Tx_i,x_{i+1})<\varepsilon$." -/
def IsMetricChainRecurrent [PseudoMetricSpace X] (T : X → X) (x : X) : Prop :=
  ∀ ε > (0 : ℝ), ∃ r ≥ 1, ∃ xs : ℕ → X,
    xs 0 = x ∧ xs r = x ∧ ∀ i < r, dist (T (xs i)) (xs (i + 1)) < ε

theorem isChainRecurrent_iff_metric [PseudoMetricSpace X] {T : X → X} {x : X} :
    IsChainRecurrent T x ↔ IsMetricChainRecurrent T x := by
  constructor
  · intro h ε hε
    exact transGen_iff_exists_seq.1 (h _ (Metric.dist_mem_uniformity hε))
  · intro h V hV
    obtain ⟨ε, hε, hεV⟩ := Metric.mem_uniformity_dist.1 hV
    obtain ⟨r, hr, xs, h0, hr', hxs⟩ := h ε hε
    refine transGen_iff_exists_seq.2 ⟨r, hr, xs, h0, hr', fun i hi => ?_⟩
    exact hεV (hxs i hi)

/-- On a compact space all compatible uniform structures coincide, so `CR(T)` does not depend
on the choice. -/
theorem chainRecurrentSet_eq_of_compact [t : TopologicalSpace X] [CompactSpace X]
    {u₁ u₂ : UniformSpace X} (h₁ : u₁.toTopologicalSpace = t)
    (h₂ : u₂.toTopologicalSpace = t) (T : X → X) :
    @chainRecurrentSet X u₁ T = @chainRecurrentSet X u₂ T := by
  rw [unique_uniformity_of_compact h₁ h₂]

/-- Printed (sec:chain-core): "For a compatible metric on $X$, …". Two compatible metrics on a
compact space give the same chain-recurrent points. -/
theorem isMetricChainRecurrent_iff_of_compact [t : TopologicalSpace X] [CompactSpace X]
    {d₁ d₂ : PseudoMetricSpace X} (h₁ : d₁.toUniformSpace.toTopologicalSpace = t)
    (h₂ : d₂.toUniformSpace.toTopologicalSpace = t) {T : X → X} {x : X} :
    @IsMetricChainRecurrent X d₁ T x ↔ @IsMetricChainRecurrent X d₂ T x := by
  rw [← @isChainRecurrent_iff_metric X d₁, ← @isChainRecurrent_iff_metric X d₂,
    unique_uniformity_of_compact h₁ h₂]

end Metric

section Wandering

variable {X : Type*}

/-- Printed (lem:chain-core-models): "Each of these sets is wandering: its distinct integer
translates are pairwise disjoint." -/
def IsWandering (T : Equiv.Perm X) (W : Set X) : Prop :=
  Pairwise fun m n : ℤ => Disjoint (⇑(T ^ m) '' W) (⇑(T ^ n) '' W)

theorem image_pow_succ_subset {T : Equiv.Perm X} {P : Set X} (hP : T '' P ⊆ P) :
    ∀ k : ℕ, ⇑(T ^ (k + 1)) '' P ⊆ T '' P
  | 0 => fun _ hy => by rwa [zero_add, pow_one] at hy
  | k + 1 => by
    rw [pow_succ', Equiv.Perm.coe_mul, Set.image_comp]
    exact Set.image_mono ((image_pow_succ_subset hP k).trans hP)

/-- Printed (lem:chain-core-models and its proof): "Each of these sets is wandering: its
distinct integer translates are pairwise disjoint." and "These defects are wandering by
nesting of the translates of $P$." -/
theorem isWandering_diff_image {T : Equiv.Perm X} {P : Set X} (hP : T '' P ⊆ P) :
    IsWandering T (P \ T '' P) := by
  have key : ∀ m n : ℤ, m < n →
      Disjoint (⇑(T ^ m) '' (P \ T '' P)) (⇑(T ^ n) '' (P \ T '' P)) := by
    intro m n hmn
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = m + ((k + 1 : ℕ) : ℤ) := ⟨(n - m - 1).toNat, by omega⟩
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    rw [zpow_add, Equiv.Perm.mul_apply] at hab
    have hba : ⇑(T ^ (k + 1)) b = a := by
      rw [← zpow_natCast]
      exact (T ^ m).injective hab
    exact ha.2 (image_pow_succ_subset hP k ⟨b, hb.1, hba⟩)
  intro m n hmn
  rcases lt_or_gt_of_ne hmn with h | h
  · exact key m n h
  · exact (key n m h).symm

end Wandering

end GroupApproximation.Dynamics

#audit_axioms GroupApproximation.Dynamics.transGen_iff_exists_seq
#audit_axioms GroupApproximation.Dynamics.transGen_chainStep_map
#audit_axioms GroupApproximation.Dynamics.isClosed_chainRecurrentSet
#audit_axioms GroupApproximation.Dynamics.apply_mem_chainRecurrentSet_iff
#audit_axioms GroupApproximation.Dynamics.image_chainRecurrentSet
#audit_axioms GroupApproximation.Dynamics.mapsTo_chainRecurrentSet
#audit_axioms GroupApproximation.Dynamics.isChainRecurrent_iff_metric
#audit_axioms GroupApproximation.Dynamics.chainRecurrentSet_eq_of_compact
#audit_axioms GroupApproximation.Dynamics.isMetricChainRecurrent_iff_of_compact
#audit_axioms GroupApproximation.Dynamics.isWandering_diff_image
