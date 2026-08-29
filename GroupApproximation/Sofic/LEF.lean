import Mathlib.Data.Fintype.Perm
import Mathlib.Data.ZMod.Basic

/-!
# Local embeddability into finite groups

This file fixes the LEF vocabulary of Section `subsec:lef` and proves the one
technical fact needed to use it: a local embedding, being multiplicative on a
large enough finite set, evaluates fixed words correctly.  This is the
mechanism by which a relator of a finitely presented group is transported into
a finite group.
-/

namespace GroupApproximation

open scoped Pointwise

/-- A map that is multiplicative on a finite set and normalized at `1`. -/
structure LocalMultiplicativeOn {G H : Type*} [Group G] [Group H]
    (s : Finset G) (f : G → H) : Prop where
  map_one : f 1 = 1
  map_mul : ∀ x ∈ s, ∀ y ∈ s, f (x * y) = f x * f y

/-- Section `subsec:lef`: `J` is locally embeddable into finite groups. -/
def IsLEF (J : Type*) [Group J] : Prop :=
  ∀ s : Finset J, ∃ (n : ℕ) (f : J → Equiv.Perm (Fin n)),
    Set.InjOn f (s : Set J) ∧ LocalMultiplicativeOn s f

/-- **LEF is closed under exhaustion by LEF subgroups**: if every finite
subset is contained in an LEF subgroup, the group is LEF.  The subgroup may
depend on the finite subset arbitrarily; its local embedding extends to the
ambient group by the identity off the subgroup. -/
theorem isLEF_of_forall_finset_subgroup {J : Type*} [Group J]
    (h : ∀ s : Finset J, ∃ H : Subgroup J,
      (∀ x ∈ s, x ∈ H) ∧ IsLEF H) : IsLEF J := by
  classical
  intro s
  obtain ⟨H, hmem, hH⟩ := h s
  obtain ⟨n, g, hginj, hgmul⟩ := hH (s.subtype (· ∈ H))
  refine ⟨n, fun x ↦ if hx : x ∈ H then g ⟨x, hx⟩ else 1, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    have hxH := hmem x (Finset.mem_coe.1 hx)
    have hyH := hmem y (Finset.mem_coe.1 hy)
    dsimp only at hxy
    rw [dif_pos hxH, dif_pos hyH] at hxy
    have := hginj
      (Finset.mem_coe.2 (Finset.mem_subtype.2 (Finset.mem_coe.1 hx)))
      (Finset.mem_coe.2 (Finset.mem_subtype.2 (Finset.mem_coe.1 hy)))
      hxy
    exact congrArg Subtype.val this
  · show (if hx : (1 : J) ∈ H then g ⟨1, hx⟩ else 1) = 1
    rw [dif_pos H.one_mem]
    exact hgmul.map_one
  · intro x hx y hy
    have hxH := hmem x hx
    have hyH := hmem y hy
    show (if hz : x * y ∈ H then g ⟨x * y, hz⟩ else 1)
        = (if hz : x ∈ H then g ⟨x, hz⟩ else 1)
          * (if hz : y ∈ H then g ⟨y, hz⟩ else 1)
    rw [dif_pos (H.mul_mem hxH hyH), dif_pos hxH, dif_pos hyH]
    exact hgmul.map_mul ⟨x, hxH⟩ (Finset.mem_subtype.2 hx)
      ⟨y, hyH⟩ (Finset.mem_subtype.2 hy)

end GroupApproximation
