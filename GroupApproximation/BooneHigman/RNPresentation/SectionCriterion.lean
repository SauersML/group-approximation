import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.FinitelyPresentedGroup
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Kernels through a multiplicative section

A normal subgroup `N` contained in the kernel of `φ : K →* H` is the whole kernel as soon as
there is a set-theoretic section `s : H → K ⧸ N` that sends `1` to `1` and intertwines right
multiplication by a generating set of `K` with right multiplication by its image.  Every class
`k N` is then `s (φ k)`, so a class lying over `1` is trivial.

This is the bookkeeping that turns a normal-form computation inside `K ⧸ N` into a presentation.
The finite presentation of a Röver–Nekrashevych group `V_d(G)` is proved this way, with
`K = V_d ∗ G` and `N` the normal closure of finitely many commutation and splitting relators.

* `mk_eq_section`: every class is the section of its image.
* `ker_eq_of_section`: the kernel criterion.
* `isFinitelyPresented_of_section`: the finite-presentation corollary, where `N` is the normal
  closure of a finite set of relators.
-/

namespace GroupApproximation.BooneHigman.RNPresentation

variable {K H : Type*} [Group K] [Group H]

/-- If a section `s : H → K ⧸ N` sends `1` to `1` and intertwines right multiplication by a
generating set `S` of `K`, then every class `k N` equals `s (φ k)`. -/
theorem mk_eq_section (φ : K →* H) (N : Subgroup K) [N.Normal] (S : Set K)
    (hS : Subgroup.closure S = ⊤) (s : H → K ⧸ N) (hs1 : s 1 = 1)
    (hmul : ∀ h : H, ∀ k ∈ S, s h * (k : K ⧸ N) = s (h * φ k)) (k : K) :
    (k : K ⧸ N) = s (φ k) := by
  have hk : k ∈ Subgroup.closure S := by
    rw [hS]
    exact Subgroup.mem_top k
  induction hk using Subgroup.closure_induction_right with
  | one => rw [QuotientGroup.mk_one, map_one, hs1]
  | mul_right x _ y hy ih =>
    rw [QuotientGroup.mk_mul, ih, hmul _ y hy, map_mul]
  | mul_inv_cancel x _ y hy ih =>
    have h := hmul (φ x * (φ y)⁻¹) y hy
    rw [inv_mul_cancel_right] at h
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, ih, ← h, mul_inv_cancel_right, map_mul,
      map_inv]

/-- **Kernel criterion.** A normal subgroup `N ≤ ker φ` equals `ker φ` when some section
`H → K ⧸ N` sends `1` to `1` and intertwines right multiplication by a generating set. -/
theorem ker_eq_of_section (φ : K →* H) (N : Subgroup K) [N.Normal] (hN : N ≤ φ.ker)
    (S : Set K) (hS : Subgroup.closure S = ⊤) (s : H → K ⧸ N) (hs1 : s 1 = 1)
    (hmul : ∀ h : H, ∀ k ∈ S, s h * (k : K ⧸ N) = s (h * φ k)) : φ.ker = N := by
  refine le_antisymm (fun k hk => ?_) hN
  have h := mk_eq_section φ N S hS s hs1 hmul k
  rw [MonoidHom.mem_ker.1 hk, hs1] at h
  exact (QuotientGroup.eq_one_iff k).1 h

/-- **Finite presentation through a section.** Let `K` be finitely presented and `φ : K →* H`
surjective.  Suppose finitely many relators `R ⊆ ker φ` admit a section into `K` modulo their
normal closure, sending `1` to `1` and intertwining right multiplication by a generating set.
Then `H` is finitely presented. -/
theorem isFinitelyPresented_of_section [Group.IsFinitelyPresented K] (φ : K →* H)
    (hφ : Function.Surjective φ) (R : Set K) (hR : R.Finite) (hRker : R ⊆ φ.ker)
    (S : Set K) (hS : Subgroup.closure S = ⊤) (s : H → K ⧸ Subgroup.normalClosure R)
    (hs1 : s 1 = 1)
    (hmul : ∀ h : H, ∀ k ∈ S, s h * (k : K ⧸ Subgroup.normalClosure R) = s (h * φ k)) :
    Group.IsFinitelyPresented H :=
  Group.IsFinitelyPresented.of_surjective φ hφ
    ⟨R, hR, (ker_eq_of_section φ _ (Subgroup.normalClosure_le_normal hRker) S hS s hs1
      hmul).symm⟩

end GroupApproximation.BooneHigman.RNPresentation
