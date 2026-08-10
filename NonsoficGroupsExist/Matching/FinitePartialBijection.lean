import NonsoficGroupsExist.Sofic.Sofic
import Mathlib.Logic.Equiv.Fintype

/-!
# Partial bijections of finite models

Cluster arrows are almost equivariant partial bijections between expander
components.  This file provides their concrete finite carrier, inverse,
graph, extension, and defect sets.  No quotient or asymptotic premise is
involved here.
-/

namespace NonsoficGroupsExist

/-- A bijection between two explicitly specified finite subsets. -/
structure FinitePartialBijection (Y Z : FiniteModel) where
  source : Finset Y
  target : Finset Z
  equiv : source ≃ target

namespace FinitePartialBijection

variable {Y Z W : FiniteModel}

/-- Value of a partial bijection at a point with a source-membership proof. -/
def apply (b : FinitePartialBijection Y Z) (y : Y) (hy : y ∈ b.source) : Z :=
  (b.equiv ⟨y, hy⟩).1

theorem apply_mem_target (b : FinitePartialBijection Y Z)
    (y : Y) (hy : y ∈ b.source) : b.apply y hy ∈ b.target :=
  (b.equiv ⟨y, hy⟩).2

theorem apply_injective (b : FinitePartialBijection Y Z)
    {x y : Y} (hx : x ∈ b.source) (hy : y ∈ b.source)
    (hxy : b.apply x hx = b.apply y hy) : x = y := by
  have hsub : (⟨x, hx⟩ : b.source) = ⟨y, hy⟩ := by
    apply b.equiv.injective
    exact Subtype.ext hxy
  exact congrArg Subtype.val hsub

/-- The full identity partial bijection. -/
def refl (Y : FiniteModel) : FinitePartialBijection Y Y where
  source := Finset.univ
  target := Finset.univ
  equiv :=
    { toFun := fun y ↦ ⟨y.1, Finset.mem_univ _⟩
      invFun := fun y ↦ ⟨y.1, Finset.mem_univ _⟩
      left_inv := fun y ↦ by cases y; rfl
      right_inv := fun y ↦ by cases y; rfl }

@[simp] theorem refl_apply (y : Y) (hy : y ∈ (refl Y).source) :
    (refl Y).apply y hy = y := rfl

/-- Reverse a finite partial bijection. -/
def symm (b : FinitePartialBijection Y Z) : FinitePartialBijection Z Y where
  source := b.target
  target := b.source
  equiv := b.equiv.symm

@[simp] theorem symm_source (b : FinitePartialBijection Y Z) :
    b.symm.source = b.target := rfl

@[simp] theorem symm_target (b : FinitePartialBijection Y Z) :
    b.symm.target = b.source := rfl

@[simp] theorem symm_symm (b : FinitePartialBijection Y Z) : b.symm.symm = b := by
  cases b
  rfl

@[simp] theorem symm_apply_apply (b : FinitePartialBijection Y Z)
    (y : Y) (hy : y ∈ b.source) :
    b.symm.apply (b.apply y hy) (b.apply_mem_target y hy) = y := by
  exact congrArg Subtype.val (b.equiv.symm_apply_apply ⟨y, hy⟩)

@[simp] theorem apply_symm_apply (b : FinitePartialBijection Y Z)
    (z : Z) (hz : z ∈ b.target) :
    b.apply (b.symm.apply z hz) (b.symm.apply_mem_target z hz) = z := by
  exact congrArg Subtype.val (b.equiv.apply_symm_apply ⟨z, hz⟩)

/-- A source point at which `b` may be followed by `c`. -/
def ComposableAt (b : FinitePartialBijection Y Z)
    (c : FinitePartialBijection Z W) (y : Y) : Prop :=
  ∃ hy : y ∈ b.source, b.apply y hy ∈ c.source

/-- A target point having a preimage through both `b` and `c`. -/
def BackComposableAt (b : FinitePartialBijection Y Z)
    (c : FinitePartialBijection Z W) (w : W) : Prop :=
  ∃ hw : w ∈ c.target, c.symm.apply w hw ∈ b.target

/-- Composition of partial bijections, restricted to the points at which the
first map lands in the source of the second. -/
noncomputable def trans (b : FinitePartialBijection Y Z)
    (c : FinitePartialBijection Z W) : FinitePartialBijection Y W := by
  classical
  exact
   { source := b.source.filter (ComposableAt b c)
     target := c.target.filter (BackComposableAt b c)
     equiv :=
    { toFun := fun y ↦ by
        have hyb : y.1 ∈ b.source := (Finset.mem_filter.mp y.2).1
        have hyc : b.apply y.1 hyb ∈ c.source := by
          obtain ⟨hyb', hyc⟩ := (Finset.mem_filter.mp y.2).2
          simpa only [proof_irrel_heq] using hyc
        refine ⟨c.apply (b.apply y.1 hyb) hyc, ?_⟩
        rw [Finset.mem_filter]
        refine ⟨c.apply_mem_target _ _, ?_⟩
        refine ⟨c.apply_mem_target _ _, ?_⟩
        simpa only [symm_apply_apply] using b.apply_mem_target y.1 hyb
      invFun := fun w ↦ by
        have hwc : w.1 ∈ c.target := (Finset.mem_filter.mp w.2).1
        have hwb : c.symm.apply w.1 hwc ∈ b.target := by
          obtain ⟨hwc', hwb⟩ := (Finset.mem_filter.mp w.2).2
          simpa only [proof_irrel_heq] using hwb
        refine ⟨b.symm.apply (c.symm.apply w.1 hwc) hwb, ?_⟩
        rw [Finset.mem_filter]
        refine ⟨b.symm.apply_mem_target _ _, ?_⟩
        refine ⟨b.symm.apply_mem_target _ _, ?_⟩
        simpa only [symm_target, apply_symm_apply] using
          c.symm.apply_mem_target w.1 hwc
      left_inv := fun y ↦ by
        apply Subtype.ext
        simp
      right_inv := fun w ↦ by
        apply Subtype.ext
        simp } }

/-- Graph of the partial bijection. -/
noncomputable def graph (b : FinitePartialBijection Y Z) : Finset (Y × Z) :=
  b.source.attach.map
    ⟨fun y ↦ (y.1, b.apply y.1 y.2), by
      intro x y h
      exact Subtype.ext (congrArg Prod.fst h)⟩

@[simp] theorem mem_graph (b : FinitePartialBijection Y Z) (y : Y) (z : Z) :
    (y, z) ∈ b.graph ↔ ∃ hy : y ∈ b.source, b.apply y hy = z := by
  classical
  constructor
  · intro h
    rw [graph, Finset.mem_map] at h
    obtain ⟨x, hx, hval⟩ := h
    have hxy : x.1 = y := congrArg Prod.fst hval
    subst y
    refine ⟨x.2, ?_⟩
    exact congrArg Prod.snd hval
  · rintro ⟨hy, rfl⟩
    rw [graph, Finset.mem_map]
    exact ⟨⟨y, hy⟩, Finset.mem_attach _ _, rfl⟩

@[simp] theorem card_graph (b : FinitePartialBijection Y Z) :
    b.graph.card = b.source.card := by
  simp [graph]

theorem card_source_eq_card_target (b : FinitePartialBijection Y Z) :
    b.source.card = b.target.card := by
  simpa using Fintype.card_congr b.equiv

/-- Every partial permutation of one finite model extends to a permutation of
the whole model. -/
theorem exists_extension (b : FinitePartialBijection Y Y) :
    ∃ p : Equiv.Perm Y, ∀ y (hy : y ∈ b.source), p y = b.apply y hy := by
  let inclusion : b.source → Y := Subtype.val
  let target : b.source → Y := fun y ↦ b.apply y.1 y.2
  have hi : Function.Injective inclusion := Subtype.val_injective
  have ht : Function.Injective target := by
    intro x y h
    apply Subtype.ext
    exact b.apply_injective x.2 y.2 h
  obtain ⟨p, hp⟩ := Equiv.Perm.exists_extending_pair inclusion target hi ht
  exact ⟨p, fun y hy ↦ hp ⟨y, hy⟩⟩

/-- Missing source mass. -/
def sourceDefect (b : FinitePartialBijection Y Z) : ℕ :=
  Fintype.card Y - b.source.card

/-- Missing range mass. -/
def targetDefect (b : FinitePartialBijection Y Z) : ℕ :=
  Fintype.card Z - b.target.card

/-- Source points at which two partial maps cannot be compared or disagree. -/
noncomputable def disagreement (b c : FinitePartialBijection Y Z) : Finset Y :=
  Finset.univ.filter fun y ↦
    ∀ hb : y ∈ b.source, ∀ hc : y ∈ c.source,
      b.apply y hb ≠ c.apply y hc

/-- Failures of equivariance, counting a missing source endpoint as a
failure, for a finite family of labels. -/
noncomputable def equivarianceDefect {L : Type*} [Fintype L]
    (b : FinitePartialBijection Y Z)
    (actY : L → Equiv.Perm Y) (actZ : L → Equiv.Perm Z) : Finset (L × Y) :=
  Finset.univ.filter fun p ↦
    ∀ hx : p.2 ∈ b.source, ∀ hsx : actY p.1 p.2 ∈ b.source,
      b.apply (actY p.1 p.2) hsx ≠ actZ p.1 (b.apply p.2 hx)

end FinitePartialBijection
end NonsoficGroupsExist
