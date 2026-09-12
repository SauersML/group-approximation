import GroupApproximation.Dynamics.Surjunctivity
import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Surjunctivity passes to subgroups

An equivariant configuration map on a subgroup extends over every left
coset by the same formula. Restriction to any coset intertwines the two
maps, so continuity and injectivity pass to the extension, and surjectivity
of the extension implies surjectivity of the original map. Consequently
every subgroup of a surjunctive group is surjunctive.
-/

namespace GroupApproximation.Surjunctivity

universe u v

variable {G : Type u} [Group G] {B : Type v}

/-- Restrict a configuration to the left coset based at `g`. -/
def subgroupSlice (H : Subgroup G) (g : G) (y : G → B) : H → B :=
  fun h ↦ y (g * h)

/-- Apply the subgroup configuration map on each left coset. -/
def subgroupExtension (H : Subgroup G) (τ : (H → B) → (H → B))
    (y : G → B) : G → B := fun g ↦ τ (subgroupSlice H g y) 1

theorem subgroupSlice_mul (H : Subgroup G) (g : G) (h : H) (y : G → B) :
    subgroupSlice H (g * h) y = shift h (subgroupSlice H g y) := by
  funext k
  simp only [subgroupSlice, shift, Subgroup.coe_mul, mul_assoc]

/-- Coset restriction intertwines the extended map and the original map. -/
theorem subgroupSlice_extension (H : Subgroup G)
    {τ : (H → B) → (H → B)} (hτ : IsEquivariant τ) (g : G) (y : G → B) :
    subgroupSlice H g (subgroupExtension H τ y) = τ (subgroupSlice H g y) := by
  funext h
  change τ (subgroupSlice H (g * h) y) 1 = _
  rw [subgroupSlice_mul, hτ]
  simp only [shift, mul_one]

theorem subgroupExtension_isEquivariant (H : Subgroup G)
    (τ : (H → B) → (H → B)) : IsEquivariant (subgroupExtension H τ) := by
  intro k y
  funext g
  change τ (subgroupSlice H g (shift k y)) 1 = τ (subgroupSlice H (k * g) y) 1
  congr 1
  funext h
  simp only [subgroupSlice, shift, mul_assoc]

theorem continuous_subgroupExtension [TopologicalSpace B] (H : Subgroup G)
    {τ : (H → B) → (H → B)} (hτ : Continuous τ) :
    Continuous (subgroupExtension H τ) := by
  apply continuous_pi
  intro g
  exact (continuous_apply (1 : H)).comp
    (hτ.comp (continuous_pi fun h : H ↦ continuous_apply (g * h)))

/-- Injectivity is detected by restricting the output to each coset. -/
theorem subgroupExtension_injective (H : Subgroup G)
    {τ : (H → B) → (H → B)} (heq : IsEquivariant τ) (hinj : Function.Injective τ) :
    Function.Injective (subgroupExtension H τ) := by
  intro y z hyz
  funext g
  have hs : subgroupSlice H g y = subgroupSlice H g z := by
    apply hinj
    rw [← subgroupSlice_extension H heq, ← subgroupSlice_extension H heq, hyz]
  have h := congrFun hs (1 : H)
  simpa only [subgroupSlice, Subgroup.coe_one, mul_one] using h

/-- Extend an arbitrary subgroup configuration, using its value at one elsewhere. -/
noncomputable def extendSubgroupConfig (H : Subgroup G) (y : H → B) : G → B :=
  Function.extend H.subtype y (fun _ ↦ y 1)

@[simp] theorem subgroupSlice_one_extend (H : Subgroup G) (y : H → B) :
    subgroupSlice H 1 (extendSubgroupConfig H y) = y := by
  funext h
  change Function.extend H.subtype y (fun _ ↦ y 1) (1 * (h : G)) = y h
  rw [one_mul]
  exact H.subtype_injective.extend_apply y (fun _ ↦ y 1) h

/-- Surjectivity of the extension supplies preimages on the subgroup coset. -/
theorem surjective_of_subgroupExtension (H : Subgroup G)
    {τ : (H → B) → (H → B)} (heq : IsEquivariant τ)
    (honto : Function.Surjective (subgroupExtension H τ)) : Function.Surjective τ := by
  intro y
  obtain ⟨z, hz⟩ := honto (extendSubgroupConfig H y)
  refine ⟨subgroupSlice H 1 z, ?_⟩
  rw [← subgroupSlice_extension H heq, hz, subgroupSlice_one_extend]

/-- Every subgroup of a surjunctive group is surjunctive. -/
theorem IsSurjunctive.subgroup (hG : IsSurjunctive G) (H : Subgroup G) :
    IsSurjunctive H := by
  intro B _ _ _ τ hcont heq hinj
  apply surjective_of_subgroupExtension H heq
  exact hG B (subgroupExtension H τ) (continuous_subgroupExtension H hcont)
    (subgroupExtension_isEquivariant H τ) (subgroupExtension_injective H heq hinj)

end GroupApproximation.Surjunctivity
