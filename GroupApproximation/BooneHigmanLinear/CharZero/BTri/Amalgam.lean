import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Algebra.Group.Subgroup.Pointwise
import GroupApproximation.Meta.AxiomGuard

/-!
# The amalgam of a family of subgroups (Z1-base, piece Z.5, part 1)

For a group `G` and a family of subgroups `P : ι → Subgroup G`, `Am P` is the group presented by
one letter `⟨i, a⟩` for each `a ∈ P i`. Its relations are:
* the multiplication table of each `P i`;
* the identification of `⟨i, a⟩` with `⟨j, b⟩` whenever `a = b` in `G`.

So `Am P` is the colimit of the diagram of the `P i` and their pairwise intersections. It maps
to `G` (`amEval`) and to any group `H` receiving compatible homomorphisms `φ i : P i →* H`
(`amLift`). The simply connected building (piece Z.5, `BTri/Develop.lean`) shows that `amEval`
is bijective. So compatible homomorphisms on the vertex stabilizers extend to `G`.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace BTri

section Amalgam

variable {G : Type*} [Group G] {ι : Type*} (P : ι → Subgroup G)

/-- One letter for each element of each `P i`. -/
abbrev AmGen : Type _ :=
  Σ i : ι, P i

/-- The relations of the amalgam. -/
inductive AmRel : FreeGroup (AmGen P) → Prop
  /-- The multiplication table of `P i`. -/
  | mul (i : ι) (a b : P i) :
      AmRel (FreeGroup.of ⟨i, a⟩ * FreeGroup.of ⟨i, b⟩ * (FreeGroup.of ⟨i, a * b⟩)⁻¹)
  /-- Equal elements of `P i` and `P j` are identified. -/
  | glue (i j : ι) (a : P i) (b : P j) (h : (a : G) = b) :
      AmRel (FreeGroup.of ⟨i, a⟩ * (FreeGroup.of ⟨j, b⟩)⁻¹)

/-- **The amalgam** of the family `P`. -/
abbrev Am : Type _ :=
  PresentedGroup {w | AmRel P w}

/-- The letter of `a ∈ P i`. -/
def amLetter (i : ι) (a : P i) : Am P :=
  PresentedGroup.of ⟨i, a⟩

theorem amLetter_mul (i : ι) (a b : P i) :
    amLetter P i a * amLetter P i b = amLetter P i (a * b) := by
  have h : FreeGroup.of (⟨i, a⟩ : AmGen P) * FreeGroup.of ⟨i, b⟩ * (FreeGroup.of ⟨i, a * b⟩)⁻¹ ∈
      {w | AmRel P w} := AmRel.mul i a b
  exact PresentedGroup.mk_eq_mk_of_mul_inv_mem h

#audit_axioms amLetter_mul

theorem amLetter_glue {i j : ι} {a : P i} {b : P j} (h : (a : G) = b) :
    amLetter P i a = amLetter P j b := by
  have h' : FreeGroup.of (⟨i, a⟩ : AmGen P) * (FreeGroup.of ⟨j, b⟩)⁻¹ ∈ {w | AmRel P w} :=
    AmRel.glue i j a b h
  exact PresentedGroup.mk_eq_mk_of_mul_inv_mem h'

#audit_axioms amLetter_glue

/-- The inclusion `P i →* Am P`. -/
def amOf (i : ι) : P i →* Am P where
  toFun := amLetter P i
  map_one' := mul_left_cancel (a := amLetter P i 1) (by simp only [amLetter_mul, mul_one])
  map_mul' a b := (amLetter_mul P i a b).symm

@[simp] theorem amOf_apply (i : ι) (a : P i) : amOf P i a = amLetter P i a :=
  rfl

theorem amOf_glue {i j : ι} {a : P i} {b : P j} (h : (a : G) = b) : amOf P i a = amOf P j b :=
  amLetter_glue P h

#audit_axioms amOf_glue

theorem amEval_kills (w : FreeGroup (AmGen P)) (hw : w ∈ {w | AmRel P w}) :
    FreeGroup.lift (fun g : AmGen P => (g.2 : G)) w = 1 := by
  change AmRel P w at hw
  cases hw with
  | mul i a b => simp
  | glue i j a b h => simp [h]

#audit_axioms amEval_kills

/-- **Evaluation** `Am P →* G`. -/
def amEval : Am P →* G :=
  PresentedGroup.toGroup (f := fun g : AmGen P => (g.2 : G)) (amEval_kills P)

@[simp] theorem amEval_amOf (i : ι) (a : P i) : amEval P (amOf P i a) = a :=
  PresentedGroup.toGroup.of _

variable {P}

/-- The letters generate the amalgam, as a right-multiplication induction principle. -/
theorem am_induction {C : Am P → Prop} (h1 : C 1)
    (hmul : ∀ (x : Am P) (i : ι) (a : P i), C x → C (x * amOf P i a)) (x : Am P) : C x := by
  have hx : x ∈ Subgroup.closure (Set.range (PresentedGroup.of : AmGen P → Am P)) := by
    rw [PresentedGroup.closure_range_of]
    exact Subgroup.mem_top x
  induction hx using Subgroup.closure_induction_right with
  | one => exact h1
  | mul_right y _ z hz hy =>
      obtain ⟨⟨i, a⟩, rfl⟩ := hz
      exact hmul y i a hy
  | mul_inv_cancel y _ z hz hy =>
      obtain ⟨⟨i, a⟩, rfl⟩ := hz
      have h := hmul y i a⁻¹ hy
      rwa [map_inv] at h

#audit_axioms am_induction

section Lift

variable {H : Type*} [Group H] (φ : ∀ i, P i →* H)
  (hφ : ∀ (i j : ι) (a : P i) (b : P j), (a : G) = b → φ i a = φ j b)

include hφ in
theorem amLift_kills (w : FreeGroup (AmGen P)) (hw : w ∈ {w | AmRel P w}) :
    FreeGroup.lift (fun g : AmGen P => φ g.1 g.2) w = 1 := by
  change AmRel P w at hw
  cases hw with
  | mul i a b => simp
  | glue i j a b h => simp [hφ i j a b h]

#audit_axioms amLift_kills

include hφ in
/-- **The universal property**: compatible homomorphisms on the `P i` induce `Am P →* H`. -/
def amLift : Am P →* H :=
  PresentedGroup.toGroup (f := fun g : AmGen P => φ g.1 g.2) (amLift_kills φ hφ)

@[simp] theorem amLift_amOf (i : ι) (a : P i) : amLift φ hφ (amOf P i a) = φ i a :=
  PresentedGroup.toGroup.of _

end Lift

end Amalgam

end BTri
end BooneHigmanLinear
end GroupApproximation
