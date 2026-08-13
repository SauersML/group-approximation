import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Topology.Constructions

/-!
# Fixed-rank marked groups and the finite-cylinder topology

A `k`-marked group is represented by the normal subgroup of relations in the
free group on `k` generators.  This file equips those normal subgroups with
the usual marked-group topology: embed them in the Cantor cube

`FreeGroup (Fin k) → Bool`

by their relation indicators and use the induced product topology.

The basic clopen cylinders prescribe membership for finitely many words.  We
prove both standard convergence criteria: pointwise eventual agreement on
each word and eventual agreement on every finite set of words.
-/

namespace GroupApproximation

open Filter Set Topology

universe u

/-- The space of `k`-marked groups, represented by normal subgroups of the
free group on the fixed ordered generating set `Fin k`. -/
structure MarkedGroupSpace (k : ℕ) where
  /-- The normal subgroup of words representing the identity. -/
  relations : Subgroup (FreeGroup (Fin k))
  /-- Relation subgroups are normal. -/
  normal_relations : relations.Normal

namespace MarkedGroupSpace

variable {k : ℕ}

instance (M : MarkedGroupSpace k) : M.relations.Normal := M.normal_relations

@[ext]
theorem ext {M N : MarkedGroupSpace k} (h : M.relations = N.relations) : M = N := by
  cases M
  cases N
  cases h
  rfl

/-- The quotient group represented by a marked group. -/
abbrev Quotient (M : MarkedGroupSpace k) : Type :=
  FreeGroup (Fin k) ⧸ M.relations

instance (M : MarkedGroupSpace k) : Group M.Quotient :=
  inferInstanceAs (Group (FreeGroup (Fin k) ⧸ M.relations))

/-- Boolean characteristic function of the relation subgroup. -/
noncomputable def relationCode (M : MarkedGroupSpace k) :
    FreeGroup (Fin k) → Bool := fun w =>
  @decide (w ∈ M.relations) (Classical.propDecidable _)

@[simp]
theorem relationCode_eq_true_iff (M : MarkedGroupSpace k)
    (w : FreeGroup (Fin k)) :
    M.relationCode w = true ↔ w ∈ M.relations := by
  classical
  simp [relationCode]

@[simp]
theorem relationCode_eq_false_iff (M : MarkedGroupSpace k)
    (w : FreeGroup (Fin k)) :
    M.relationCode w = false ↔ w ∉ M.relations := by
  classical
  simp [relationCode]

theorem relationCode_apply_eq_iff (M N : MarkedGroupSpace k)
    (w : FreeGroup (Fin k)) :
    M.relationCode w = N.relationCode w ↔
      (w ∈ M.relations ↔ w ∈ N.relations) := by
  classical
  simp [relationCode]

theorem relationCode_injective :
    Function.Injective (relationCode : MarkedGroupSpace k →
      FreeGroup (Fin k) → Bool) := by
  intro M N h
  apply ext
  ext w
  exact (relationCode_apply_eq_iff M N w).mp
    (congrFun h w)

/-- The marked-group topology is the topology induced by relation indicators
inside the product of discrete two-point spaces. -/
noncomputable instance instTopologicalSpace : TopologicalSpace (MarkedGroupSpace k) :=
  TopologicalSpace.induced relationCode inferInstance

/-- Relation indicators are continuous by construction. -/
theorem continuous_relationCode :
    Continuous (relationCode : MarkedGroupSpace k →
      FreeGroup (Fin k) → Bool) :=
  continuous_induced_dom

/-- Agreement with `M` on a finite set of words.  These are the standard
finite cylinders in marked-group space. -/
noncomputable def cylinder (M : MarkedGroupSpace k)
    (F : Finset (FreeGroup (Fin k))) : Set (MarkedGroupSpace k) :=
  ⋂ w ∈ F, {N | N.relationCode w = M.relationCode w}

@[simp]
theorem mem_cylinder_iff (M N : MarkedGroupSpace k)
    (F : Finset (FreeGroup (Fin k))) :
    N ∈ cylinder M F ↔
      ∀ w ∈ F, (w ∈ N.relations ↔ w ∈ M.relations) := by
  classical
  simp only [cylinder, Set.mem_iInter, Set.mem_setOf_eq]
  constructor
  · intro h w hw
    exact (relationCode_apply_eq_iff N M w).mp (h w hw)
  · intro h w hw
    exact (relationCode_apply_eq_iff N M w).mpr (h w hw)

@[simp]
theorem mem_cylinder_self (M : MarkedGroupSpace k)
    (F : Finset (FreeGroup (Fin k))) :
    M ∈ cylinder M F := by
  simp

/-- Every finite relation cylinder is open. -/
theorem isOpen_cylinder (M : MarkedGroupSpace k)
    (F : Finset (FreeGroup (Fin k))) :
    IsOpen (cylinder M F) := by
  unfold cylinder
  apply isOpen_biInter_finset
  intro w hw
  exact (isOpen_discrete {M.relationCode w}).preimage
    ((continuous_apply w).comp continuous_relationCode)

/-- Every finite relation cylinder is closed. -/
theorem isClosed_cylinder (M : MarkedGroupSpace k)
    (F : Finset (FreeGroup (Fin k))) :
    IsClosed (cylinder M F) := by
  unfold cylinder
  apply isClosed_biInter
  intro w hw
  exact (isClosed_discrete {M.relationCode w}).preimage
    ((continuous_apply w).comp continuous_relationCode)

/-- Thus every finite relation cylinder is clopen. -/
theorem isClopen_cylinder (M : MarkedGroupSpace k)
    (F : Finset (FreeGroup (Fin k))) :
    IsClopen (cylinder M F) :=
  ⟨isClosed_cylinder M F, isOpen_cylinder M F⟩

/-- A cylinder centered at `M` is a neighborhood of `M`. -/
theorem cylinder_mem_nhds (M : MarkedGroupSpace k)
    (F : Finset (FreeGroup (Fin k))) :
    cylinder M F ∈ 𝓝 M :=
  (isOpen_cylinder M F).mem_nhds (mem_cylinder_self M F)

/-- The finite cylinders centered at `M` form a neighborhood basis. -/
theorem mem_nhds_iff_exists_cylinder_subset (M : MarkedGroupSpace k)
    (U : Set (MarkedGroupSpace k)) :
    U ∈ 𝓝 M ↔
      ∃ F : Finset (FreeGroup (Fin k)), cylinder M F ⊆ U := by
  constructor
  · intro hU
    change U ∈ @nhds (MarkedGroupSpace k)
      (TopologicalSpace.induced relationCode inferInstance) M at hU
    rw [nhds_induced, Filter.mem_comap] at hU
    obtain ⟨V, hV, hVU⟩ := hU
    rw [nhds_pi, Filter.mem_pi'] at hV
    obtain ⟨F, t, ht, htV⟩ := hV
    refine ⟨F, fun N hN => hVU (htV ?_)⟩
    intro w hw
    have hcenter : M.relationCode w ∈ t w := by
      have htw := ht w
      rw [nhds_discrete] at htw
      exact htw
    have hcode : N.relationCode w = M.relationCode w :=
      (relationCode_apply_eq_iff N M w).mpr
        ((mem_cylinder_iff M N F).mp hN w hw)
    rwa [hcode]
  · rintro ⟨F, hFU⟩
    exact mem_of_superset (cylinder_mem_nhds M F) hFU

/-- Filter-basis packaging of `mem_nhds_iff_exists_cylinder_subset`. -/
theorem nhds_hasBasis_cylinder (M : MarkedGroupSpace k) :
    (𝓝 M).HasBasis (fun _ : Finset (FreeGroup (Fin k)) => True)
      (cylinder M) := by
  rw [Filter.hasBasis_iff]
  intro U
  simpa using mem_nhds_iff_exists_cylinder_subset M U

/-- Convergence in marked-group space is exactly eventual agreement on each
individual relation word.  This is stated for an arbitrary source filter. -/
theorem tendsto_iff_eventually_relation
    {α : Type u} {l : Filter α} {f : α → MarkedGroupSpace k}
    {M : MarkedGroupSpace k} :
    Tendsto f l (𝓝 M) ↔
      ∀ w : FreeGroup (Fin k),
        ∀ᶠ i in l, (w ∈ (f i).relations ↔ w ∈ M.relations) := by
  change Tendsto f l
      (@nhds (MarkedGroupSpace k)
        (TopologicalSpace.induced relationCode inferInstance) M) ↔ _
  rw [nhds_induced, tendsto_comap_iff, tendsto_pi_nhds]
  constructor
  · intro h w
    have hw := h w
    rw [nhds_discrete, tendsto_pure] at hw
    exact hw.mono fun i hi =>
      (relationCode_apply_eq_iff (f i) M w).mp hi
  · intro h w
    rw [nhds_discrete, tendsto_pure]
    exact (h w).mono fun i hi =>
      (relationCode_apply_eq_iff (f i) M w).mpr hi

/-- Equivalent finite-cylinder convergence criterion. -/
theorem tendsto_iff_eventually_cylinder
    {α : Type u} {l : Filter α} {f : α → MarkedGroupSpace k}
    {M : MarkedGroupSpace k} :
    Tendsto f l (𝓝 M) ↔
      ∀ F : Finset (FreeGroup (Fin k)),
        ∀ᶠ i in l, f i ∈ cylinder M F := by
  rw [tendsto_iff_eventually_relation]
  constructor
  · intro h F
    refine ((F.eventually_all).2 fun w hw => h w).mono fun i hi => ?_
    exact (mem_cylinder_iff M (f i) F).mpr hi
  · intro h w
    have hw := h {w}
    simpa using hw

/-- Sequential marked convergence: every word has eventually constant truth
value as a relation. -/
theorem tendsto_sequence_iff_eventually_relation
    {f : ℕ → MarkedGroupSpace k} {M : MarkedGroupSpace k} :
    Tendsto f atTop (𝓝 M) ↔
      ∀ w : FreeGroup (Fin k),
        ∀ᶠ n in atTop, (w ∈ (f n).relations ↔ w ∈ M.relations) :=
  tendsto_iff_eventually_relation

/-- Sequential finite-ball form of marked convergence. -/
theorem tendsto_sequence_iff_eventually_cylinder
    {f : ℕ → MarkedGroupSpace k} {M : MarkedGroupSpace k} :
    Tendsto f atTop (𝓝 M) ↔
      ∀ F : Finset (FreeGroup (Fin k)),
        ∀ᶠ n in atTop, f n ∈ cylinder M F :=
  tendsto_iff_eventually_cylinder

end MarkedGroupSpace

end GroupApproximation
