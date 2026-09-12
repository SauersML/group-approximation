import Mathlib.Topology.Constructions
import Mathlib.Algebra.Group.Defs
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Full shifts and surjunctivity

The shift convention uses left precomposition. Cellular rules consequently
read right translates of a fixed finite memory set.
-/

namespace GroupApproximation.Surjunctivity

universe u v

variable {G : Type u} [Group G] {B : Type v}

/-- Left precomposition on a full shift. -/
def shift (k : G) (x : G → B) : G → B := fun g => x (k * g)

@[simp] theorem shift_apply (k : G) (x : G → B) (g : G) :
    shift k x g = x (k * g) := rfl

@[simp] theorem shift_one (x : G → B) : shift 1 x = x := by
  funext g
  simp [shift]

/-- A map on the full shift commutes with left precomposition. -/
def IsEquivariant (τ : (G → B) → (G → B)) : Prop :=
  ∀ k x, τ (shift k x) = shift k (τ x)

/-- The same finite right-translation memory works at every coordinate. -/
def HasMemory (τ : (G → B) → (G → B)) (M : Finset G) : Prop :=
  ∀ x y g, (∀ m ∈ M, x (g * m) = y (g * m)) → τ x g = τ y g

/-- Uniform finite dependence, without imposing equivariance on local rules. -/
def IsFiniteMemory (τ : (G → B) → (G → B)) : Prop :=
  ∃ M : Finset G, HasMemory τ M

/-- The cellular map defined by a finite memory set and a local rule. -/
def localMap (M : Finset G) (μ : (M → B) → B) : (G → B) → (G → B) :=
  fun x g => μ (fun m => x (g * m))

theorem localMap_hasMemory (M : Finset G) (μ : (M → B) → B) :
    HasMemory (localMap M μ) M := by
  intro x y g h
  apply congrArg μ
  funext m
  exact h m m.property

theorem localMap_isEquivariant (M : Finset G) (μ : (M → B) → B) :
    IsEquivariant (localMap M μ) := by
  intro k x
  funext g
  simp only [localMap, shift, mul_assoc]

theorem continuous_localMap [TopologicalSpace B] [DiscreteTopology B]
    (M : Finset G) (μ : (M → B) → B) : Continuous (localMap M μ) := by
  apply continuous_pi
  intro g
  exact continuous_of_discreteTopology.comp
    (continuous_pi fun m : M => continuous_apply (g * m))

/-- Uniform finite dependence implies continuity, even for varying local rules. -/
theorem HasMemory.continuous [TopologicalSpace B] [DiscreteTopology B]
    {τ : (G → B) → (G → B)} {M : Finset G} (hτ : HasMemory τ M) :
    Continuous τ := by
  classical
  cases isEmpty_or_nonempty B with
  | inl hB =>
    letI := hB
    exact continuous_of_discreteTopology
  | inr hB =>
    let b : B := Classical.choice hB
    let μ : G → (M → B) → B := fun g v =>
      τ (fun h => if hm : g⁻¹ * h ∈ M then v ⟨g⁻¹ * h, hm⟩ else b) g
    have heq : τ = fun x g => μ g (fun m => x (g * m)) := by
      funext x g
      apply hτ x _ g
      intro m hm
      simp [hm]
    rw [heq]
    apply continuous_pi
    intro g
    change Continuous ((μ g) ∘ fun (x : G → B) (m : M) => x (g * m))
    exact (continuous_of_discreteTopology : Continuous (μ g)).comp
      (continuous_pi fun m : M => continuous_apply (g * m))

theorem IsFiniteMemory.continuous [TopologicalSpace B] [DiscreteTopology B]
    {τ : (G → B) → (G → B)} (hτ : IsFiniteMemory τ) : Continuous τ := by
  obtain ⟨M, hM⟩ := hτ
  exact hM.continuous

omit [Group G] in
/-- A continuous discrete-valued observable on a compact full shift depends
on finitely many coordinates. -/
theorem exists_finset_of_continuous [TopologicalSpace B] [CompactSpace B] [DiscreteTopology B]
    {C : Type*} [TopologicalSpace C] [DiscreteTopology C]
    (f : (G → B) → C) (hf : Continuous f) :
    ∃ M : Finset G, ∀ x y, (∀ m ∈ M, x m = y m) → f x = f y := by
  classical
  have hlocal (x : G → B) :
      ∃ M : Finset G, ∀ y, (∀ m ∈ M, y m = x m) → f y = f x := by
    have hopen : IsOpen {y | f y = f x} :=
      (isOpen_discrete ({f x} : Set C)).preimage hf
    obtain ⟨M, U, hU, hsub⟩ := isOpen_pi_iff.mp hopen x rfl
    refine ⟨M, fun y hy => hsub ?_⟩
    intro m hm
    rw [hy m hm]
    exact (hU m hm).2
  choose M hM using hlocal
  let cylinder (x : G → B) : Set (G → B) :=
    (M x : Set G).pi fun m => {x m}
  have hopen (x : G → B) : IsOpen (cylinder x) :=
    isOpen_set_pi (M x).finite_toSet fun _ _ => isOpen_discrete _
  have hcover : (Set.univ : Set (G → B)) ⊆ ⋃ x, cylinder x := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, fun _ _ => rfl⟩
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover cylinder hopen hcover
  refine ⟨T.biUnion M, ?_⟩
  intro x y hxy
  obtain ⟨z, hz⟩ := Set.mem_iUnion.mp (hT (Set.mem_univ x))
  obtain ⟨hzt, hxz⟩ := Set.mem_iUnion.mp hz
  have hyz : ∀ m ∈ M z, y m = z m := by
    intro m hm
    exact (hxy m (Finset.mem_biUnion.mpr ⟨z, hzt, hm⟩)).symm.trans (hxz m hm)
  exact (hM z x hxz).trans (hM z y hyz).symm

/-- Curtis--Hedlund--Lyndon in uniform finite-dependence form. -/
theorem isFiniteMemory_of_continuous_equivariant
    [TopologicalSpace B] [CompactSpace B] [DiscreteTopology B]
    {τ : (G → B) → (G → B)} (hc : Continuous τ) (he : IsEquivariant τ) :
    IsFiniteMemory τ := by
  obtain ⟨M, hM⟩ := exists_finset_of_continuous (fun x => τ x 1)
    ((continuous_apply 1).comp hc)
  refine ⟨M, ?_⟩
  intro x y g hxy
  have h := hM (shift g x) (shift g y) hxy
  simpa only [he g x, he g y, shift, mul_one] using h

/-- Continuity and subgroup symmetry give uniform finite memory when all
nonidentity behavior lies in finitely many right cosets of that subgroup. -/
theorem isFiniteMemory_of_continuous_coset_support
    [TopologicalSpace B] [CompactSpace B] [DiscreteTopology B]
    (K : Subgroup G) (S : Finset G) {τ : (G → B) → (G → B)}
    (hc : Continuous τ)
    (he : ∀ (k : K) x g, τ (shift (k : G) x) g = τ x ((k : G) * g))
    (hs : ∀ x g, (∀ s ∈ S, g * s⁻¹ ∉ K) → τ x g = x g) :
    IsFiniteMemory τ := by
  classical
  have hlocal (s : G) := exists_finset_of_continuous (fun x => τ x s)
    ((continuous_apply s).comp hc)
  choose D hD using hlocal
  refine ⟨insert 1 (S.biUnion fun s => (D s).image fun d => s⁻¹ * d), ?_⟩
  intro x y g hxy
  by_cases hg : ∀ s ∈ S, g * s⁻¹ ∉ K
  · rw [hs x g hg, hs y g hg]
    simpa only [mul_one] using hxy 1 (Finset.mem_insert_self _ _)
  · push Not at hg
    obtain ⟨s, hsS, hgs⟩ := hg
    let k : K := ⟨g * s⁻¹, hgs⟩
    have hks : (k : G) * s = g := by simp [k, mul_assoc]
    have h := hD s (shift (k : G) x) (shift (k : G) y) (by
      intro d hd
      have hdM : s⁻¹ * d ∈ insert 1
          (S.biUnion fun s => (D s).image fun d => s⁻¹ * d) :=
        Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
          ⟨s, hsS, Finset.mem_image.mpr ⟨d, hd, rfl⟩⟩)
      simpa only [shift, k, mul_assoc] using hxy (s⁻¹ * d) hdM)
    simpa only [he k x s, he k y s, hks] using h

theorem IsEquivariant.comp {σ τ : (G → B) → (G → B)}
    (hσ : IsEquivariant σ) (hτ : IsEquivariant τ) : IsEquivariant (σ ∘ τ) := by
  intro k x
  simp only [Function.comp_apply, hτ k x, hσ k (τ x)]

theorem isEquivariant_id : IsEquivariant (id : (G → B) → (G → B)) := by
  intro k x
  rfl

theorem IsEquivariant.symm (e : (G → B) ≃ (G → B))
    (he : IsEquivariant e) : IsEquivariant e.symm := by
  intro k x
  apply e.injective
  rw [e.apply_symm_apply, he, e.apply_symm_apply]

omit [Group G] in
/-- A continuous bijection of a finite-alphabet full shift has continuous inverse. -/
theorem continuous_equiv_symm [Fintype B] [TopologicalSpace B] [DiscreteTopology B]
    (e : (G → B) ≃ (G → B)) (he : Continuous e) : Continuous e.symm :=
  he.continuous_symm_of_equiv_compact_to_t2

/-- The inverse of a bijective cellular automaton again has uniform finite memory. -/
theorem isFiniteMemory_equiv_symm [Fintype B] [TopologicalSpace B] [DiscreteTopology B]
    (e : (G → B) ≃ (G → B)) (hc : Continuous e) (he : IsEquivariant e) :
    IsFiniteMemory e.symm :=
  isFiniteMemory_of_continuous_equivariant (continuous_equiv_symm e hc)
    (IsEquivariant.symm e he)

/-- Surjunctivity for finite discrete alphabets. -/
def IsSurjunctive (G : Type u) [Group G] : Prop :=
  ∀ (B : Type) [Fintype B] [TopologicalSpace B] [DiscreteTopology B],
    ∀ τ : (G → B) → (G → B),
      Continuous τ → IsEquivariant τ → Function.Injective τ → Function.Surjective τ

/-- Finite alphabets in any universe reduce to finite natural-number intervals. -/
theorem IsSurjunctive.surjective [Fintype B] [TopologicalSpace B] [DiscreteTopology B]
    (hG : IsSurjunctive G) (τ : (G → B) → (G → B)) (hc : Continuous τ)
    (he : IsEquivariant τ) (hi : Function.Injective τ) : Function.Surjective τ := by
  classical
  let e : B ≃ Fin (Fintype.card B) := Fintype.equivFin B
  letI : TopologicalSpace (Fin (Fintype.card B)) := ⊥
  letI : DiscreteTopology (Fin (Fintype.card B)) := ⟨rfl⟩
  let E : (G → B) ≃ (G → Fin (Fintype.card B)) := Equiv.piCongrRight fun _ => e
  have hEc : Continuous E :=
    continuous_pi fun g => continuous_of_discreteTopology.comp (continuous_apply g)
  have hEic : Continuous E.symm :=
    continuous_pi fun g => continuous_of_discreteTopology.comp (continuous_apply g)
  let σ := E ∘ τ ∘ E.symm
  have hσe : IsEquivariant σ := by
    intro k x
    change E (τ (shift k (E.symm x))) = shift k (E (τ (E.symm x)))
    rw [he]
    rfl
  have hσi : Function.Injective σ := E.injective.comp (hi.comp E.symm.injective)
  have hσs := hG (Fin (Fintype.card B)) σ (hEc.comp (hc.comp hEic)) hσe hσi
  intro y
  obtain ⟨x, hx⟩ := hσs (E y)
  refine ⟨E.symm x, E.injective ?_⟩
  exact hx

/-- An injective cellular automaton on a surjunctive group has a finite-memory inverse. -/
theorem IsSurjunctive.exists_inverse [Fintype B] [TopologicalSpace B] [DiscreteTopology B]
    (hG : IsSurjunctive G) (τ : (G → B) → (G → B)) (hc : Continuous τ)
    (he : IsEquivariant τ) (hi : Function.Injective τ) :
    ∃ σ : (G → B) → (G → B), IsFiniteMemory σ ∧ IsEquivariant σ ∧
      Function.LeftInverse σ τ ∧ Function.RightInverse σ τ := by
  let e : (G → B) ≃ (G → B) := Equiv.ofBijective τ ⟨hi, hG.surjective τ hc he hi⟩
  exact ⟨e.symm, isFiniteMemory_equiv_symm e hc he, IsEquivariant.symm e he,
    e.symm_apply_apply, e.apply_symm_apply⟩

theorem IsSurjunctive.surjective_localMap {G : Type u} [Group G]
    (hG : IsSurjunctive G) {B : Type} [Fintype B] [TopologicalSpace B]
    [DiscreteTopology B] (M : Finset G) (μ : (M → B) → B)
    (hτ : Function.Injective (localMap M μ)) :
    Function.Surjective (localMap M μ) :=
  hG B (localMap M μ) (continuous_localMap M μ) (localMap_isEquivariant M μ) hτ

end GroupApproximation.Surjunctivity
