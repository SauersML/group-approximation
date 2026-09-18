import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.StepanovMatui.MatuiAssembly
import GroupApproximation.Meta.AxiomGuard

namespace GroupApproximation
namespace Full
namespace StepanovMatui
namespace Matui

/-!
# Permutations of a clopen tower

`simple_kazhdan_sofic_group.tex`, remark at tex l.307–309:

> For derived topological full groups, Matui showed by a similar argument that a nontrivial normal
> subgroup meets a simple union of products of alternating groups on towers
> [Matui, Lemma 3.4 and Theorem 4.9].

A *tower* along a permutation `f₀` of `X` has a base `W` and levels `f₀^{E i} W` for exponents
`E : Fin n → ℤ`.  When the levels are pairwise disjoint, every permutation `σ` of `Fin n` acts on
the tower by moving level `i` to level `σ i` along `f₀`.  This file builds that action as a group
homomorphism `towerPerm : Perm (Fin n) →* Perm X` and proves:

* `mem_fullGroup_of_piecewise`: a permutation that agrees with elements of `[[T]]` on finitely many
  disjoint clopen pieces and is the identity off them lies in `[[T]]`;
* `towerPerm_mem_fullGroup`, `towerPerm_commutator_mem`: the tower action lands in `[[T]]`, and its
  commutators land in `⁅[[T]], [[T]]⁆`;
* `towerPerm_supportedIn`: the action of `σ` is supported on the levels that `σ` moves;
* `swapAlong_eq_towerPerm`: the swap along `g` of the base with a level is a transposition of the
  tower, so the three-cycles of `MatuiFullGroup` are images of finite permutations.
-/

open scoped commutatorElement

variable {X : Type*}

/-! ## Powers of a permutation -/

theorem perm_zpow_apply_zpow_apply (f : Equiv.Perm X) (a b : ℤ) (x : X) :
    (f ^ a) ((f ^ b) x) = (f ^ (a + b)) x := by
  rw [zpow_add, Equiv.Perm.mul_apply]

theorem perm_zpow_neg_apply_zpow_apply (f : Equiv.Perm X) (a : ℤ) (x : X) :
    (f ^ (-a)) ((f ^ a) x) = x := by
  rw [perm_zpow_apply_zpow_apply, neg_add_cancel, zpow_zero, Equiv.Perm.one_apply]

/-- Forgetting continuity, as a group homomorphism. -/
def homeoToPerm [TopologicalSpace X] : (X ≃ₜ X) →* Equiv.Perm X where
  toFun := Homeomorph.toEquiv
  map_one' := rfl
  map_mul' := fun _ _ => rfl

theorem toEquiv_zpow_apply [TopologicalSpace X] (T : X ≃ₜ X) (k : ℤ) (y : X) :
    (T.toEquiv ^ k) y = (T ^ k) y := by
  have h : homeoToPerm (T ^ k) = homeoToPerm T ^ k := map_zpow homeoToPerm T k
  exact (congrArg (fun g : Equiv.Perm X => g y) h).symm

/-! ## Piecewise elements of the full group -/

/-- A permutation agreeing with elements of `[[T]]` on finitely many disjoint clopen pieces, and
with the identity off them, lies in `[[T]]`. -/
theorem mem_fullGroup_of_piecewise [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {T : X ≃ₜ X} {n : ℕ} (L : Fin n → Set X) (hL : ∀ i, IsClopen (L i))
    (hLd : ∀ i j x, x ∈ L i → x ∈ L j → i = j) (h : Fin n → Equiv.Perm X)
    (hh : ∀ i, h i ∈ fullGroup T) (g : Equiv.Perm X) (hgi : ∀ i, ∀ x ∈ L i, g x = h i x)
    (hgo : ∀ x, (∀ i, x ∉ L i) → g x = x) : g ∈ fullGroup T := by
  classical
  have hh' : ∀ i, ∃ m : X → ℤ, Continuous m ∧ ∀ x, h i x = (T ^ m x) x :=
    fun i => mem_fullGroup.mp (hh i)
  choose m hm hhm using hh'
  refine mem_fullGroup.mpr ⟨fun x => ∑ i, if x ∈ L i then m i x else 0, ?_, fun x => ?_⟩
  · exact continuous_finsetSum Finset.univ fun i _ =>
      continuous_ite_of_isClopen (fun x => x ∈ L i) (hL i) (hm i) continuous_const
  · show g x = (T ^ (∑ i, if x ∈ L i then m i x else 0)) x
    by_cases hx : ∃ i, x ∈ L i
    · obtain ⟨i, hi⟩ := hx
      have hsum : (∑ j, if x ∈ L j then m j x else 0) = m i x := by
        rw [Finset.sum_eq_single i]
        · exact if_pos hi
        · intro j _ hji
          exact if_neg fun hj => hji (hLd j i x hj hi)
        · intro hi'
          exact absurd (Finset.mem_univ i) hi'
      rw [hsum, hgi i x hi, hhm i x]
    · have hsum : (∑ j, if x ∈ L j then m j x else 0) = 0 :=
        Finset.sum_eq_zero fun j _ => if_neg fun hj => hx ⟨j, hj⟩
      rw [hsum, zpow_zero, Homeomorph.one_apply, hgo x fun j hj => hx ⟨j, hj⟩]

/-! ## The tower action -/

open Classical in
/-- Move the level `i` of the tower to the level `σ i` along `f₀`; the identity off the tower. -/
noncomputable def towerFun (f₀ : Equiv.Perm X) (W : Set X) {n : ℕ} (E : Fin n → ℤ)
    (σ : Equiv.Perm (Fin n)) (x : X) : X :=
  if h : ∃ i, (f₀ ^ (-E i)) x ∈ W then (f₀ ^ (E (σ h.choose) - E h.choose)) x else x

section Tower

variable {f₀ : Equiv.Perm X} {W : Set X} {n : ℕ} {E : Fin n → ℤ}

open Classical in
theorem towerFun_of_mem (hdisj : ∀ i j x, (f₀ ^ (-E i)) x ∈ W → (f₀ ^ (-E j)) x ∈ W → i = j)
    {σ : Equiv.Perm (Fin n)} {i : Fin n} {x : X} (hi : (f₀ ^ (-E i)) x ∈ W) :
    towerFun f₀ W E σ x = (f₀ ^ (E (σ i) - E i)) x := by
  have h : ∃ i, (f₀ ^ (-E i)) x ∈ W := ⟨i, hi⟩
  have e : h.choose = i := hdisj _ _ x h.choose_spec hi
  rw [towerFun, dif_pos h, e]

open Classical in
theorem towerFun_of_not {σ : Equiv.Perm (Fin n)} {x : X} (h : ¬∃ i, (f₀ ^ (-E i)) x ∈ W) :
    towerFun f₀ W E σ x = x := by
  rw [towerFun, dif_neg h]

theorem towerFun_level (hdisj : ∀ i j x, (f₀ ^ (-E i)) x ∈ W → (f₀ ^ (-E j)) x ∈ W → i = j)
    {σ : Equiv.Perm (Fin n)} {i : Fin n} {x : X} (hi : (f₀ ^ (-E i)) x ∈ W) :
    (f₀ ^ (-E (σ i))) (towerFun f₀ W E σ x) ∈ W := by
  have e : -E (σ i) + (E (σ i) - E i) = -E i := by ring
  rw [towerFun_of_mem hdisj hi, perm_zpow_apply_zpow_apply, e]
  exact hi

theorem towerFun_one (hdisj : ∀ i j x, (f₀ ^ (-E i)) x ∈ W → (f₀ ^ (-E j)) x ∈ W → i = j)
    (x : X) : towerFun f₀ W E 1 x = x := by
  by_cases h : ∃ i, (f₀ ^ (-E i)) x ∈ W
  · obtain ⟨i, hi⟩ := h
    rw [towerFun_of_mem hdisj hi, Equiv.Perm.one_apply, sub_self, zpow_zero, Equiv.Perm.one_apply]
  · exact towerFun_of_not h

theorem towerFun_towerFun (hdisj : ∀ i j x, (f₀ ^ (-E i)) x ∈ W → (f₀ ^ (-E j)) x ∈ W → i = j)
    {σ τ : Equiv.Perm (Fin n)} (x : X) :
    towerFun f₀ W E τ (towerFun f₀ W E σ x) = towerFun f₀ W E (τ * σ) x := by
  by_cases h : ∃ i, (f₀ ^ (-E i)) x ∈ W
  · obtain ⟨i, hi⟩ := h
    have e : E (τ (σ i)) - E (σ i) + (E (σ i) - E i) = E (τ (σ i)) - E i := by ring
    rw [towerFun_of_mem hdisj (towerFun_level hdisj hi), towerFun_of_mem hdisj hi,
      towerFun_of_mem hdisj hi, perm_zpow_apply_zpow_apply, Equiv.Perm.mul_apply, e]
  · rw [towerFun_of_not h, towerFun_of_not h, towerFun_of_not h]

end Tower

/-- **The tower action**: `σ ∈ Perm (Fin n)` moves level `i` to level `σ i` along `f₀`. -/
noncomputable def towerPerm (f₀ : Equiv.Perm X) (W : Set X) {n : ℕ} (E : Fin n → ℤ)
    (hdisj : ∀ i j x, (f₀ ^ (-E i)) x ∈ W → (f₀ ^ (-E j)) x ∈ W → i = j) :
    Equiv.Perm (Fin n) →* Equiv.Perm X where
  toFun σ :=
    { toFun := towerFun f₀ W E σ
      invFun := towerFun f₀ W E σ⁻¹
      left_inv := fun x => by rw [towerFun_towerFun hdisj, inv_mul_cancel, towerFun_one hdisj]
      right_inv := fun x => by rw [towerFun_towerFun hdisj, mul_inv_cancel, towerFun_one hdisj] }
  map_one' := Equiv.ext fun x => towerFun_one hdisj x
  map_mul' := fun a b => Equiv.ext fun x => (towerFun_towerFun hdisj (σ := b) (τ := a) x).symm

section TowerPerm

variable {f₀ : Equiv.Perm X} {W : Set X} {n : ℕ} {E : Fin n → ℤ}

theorem towerPerm_apply (hdisj : ∀ i j x, (f₀ ^ (-E i)) x ∈ W → (f₀ ^ (-E j)) x ∈ W → i = j)
    (σ : Equiv.Perm (Fin n)) (x : X) : towerPerm f₀ W E hdisj σ x = towerFun f₀ W E σ x :=
  rfl

/-- The tower action of `σ` is supported on the levels moved by `σ`. -/
theorem towerPerm_supportedIn
    (hdisj : ∀ i j x, (f₀ ^ (-E i)) x ∈ W → (f₀ ^ (-E j)) x ∈ W → i = j)
    {σ : Equiv.Perm (Fin n)} {V : Set X}
    (hσ : ∀ i, σ i ≠ i → ∀ x, (f₀ ^ (-E i)) x ∈ W → x ∈ V) :
    HydeLodha.SupportedIn (towerPerm f₀ W E hdisj σ) V := by
  intro x hxV
  rw [towerPerm_apply]
  by_cases h : ∃ i, (f₀ ^ (-E i)) x ∈ W
  · obtain ⟨i, hi⟩ := h
    by_cases hσi : σ i = i
    · rw [towerFun_of_mem hdisj hi, hσi, sub_self, zpow_zero, Equiv.Perm.one_apply]
    · exact absurd (hσ i hσi x hi) hxV
  · exact towerFun_of_not h

/-- The tower action lands in `[[T]]` for a clopen base and `f₀ ∈ [[T]]`. -/
theorem towerPerm_mem_fullGroup [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {T : X ≃ₜ X} (hf₀ : f₀ ∈ fullGroup T) (hW : IsClopen W)
    (hdisj : ∀ i j x, (f₀ ^ (-E i)) x ∈ W → (f₀ ^ (-E j)) x ∈ W → i = j)
    (σ : Equiv.Perm (Fin n)) : towerPerm f₀ W E hdisj σ ∈ fullGroup T := by
  refine mem_fullGroup_of_piecewise (fun i => ⇑(f₀ ^ (-E i)) ⁻¹' W) (fun i => ?_) hdisj
    (fun i => f₀ ^ (E (σ i) - E i)) (fun i => (fullGroup T).zpow_mem hf₀ (E (σ i) - E i)) _
    (fun i x hi => ?_) (fun x hx => ?_)
  · exact hW.preimage
      (IsFullGroupElement.continuous (mem_fullGroup.mp ((fullGroup T).zpow_mem hf₀ (-E i))))
  · exact towerFun_of_mem hdisj (σ := σ) (i := i) (x := x) hi
  · exact towerFun_of_not (σ := σ) (x := x) fun h => Exists.elim h fun i hi => hx i hi

/-- Commutators of tower actions lie in the derived full group. -/
theorem towerPerm_commutator_mem [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {T : X ≃ₜ X} (hf₀ : f₀ ∈ fullGroup T) (hW : IsClopen W)
    (hdisj : ∀ i j x, (f₀ ^ (-E i)) x ∈ W → (f₀ ^ (-E j)) x ∈ W → i = j)
    (σ τ : Equiv.Perm (Fin n)) : towerPerm f₀ W E hdisj ⁅σ, τ⁆ ∈ ⁅fullGroup T, fullGroup T⁆ := by
  rw [map_commutatorElement]
  exact Subgroup.commutator_mem_commutator (towerPerm_mem_fullGroup hf₀ hW hdisj σ)
    (towerPerm_mem_fullGroup hf₀ hW hdisj τ)

/-- **Swaps are transpositions of the tower**: if the base is level `i₀` and `g` moves the base to
level `j` along `f₀`, then the swap along `g` is the tower action of `swap i₀ j`. -/
theorem swapAlong_eq_towerPerm
    (hdisj : ∀ i j x, (f₀ ^ (-E i)) x ∈ W → (f₀ ^ (-E j)) x ∈ W → i = j)
    {i₀ j : Fin n} (hE : E i₀ = 0) (hij : i₀ ≠ j) {g : Equiv.Perm X}
    (hg : ∀ y ∈ W, g y = (f₀ ^ E j) y) :
    swapAlong g W = towerPerm f₀ W E hdisj (Equiv.swap i₀ j) := by
  have hW0 : ∀ y, (f₀ ^ (-E i₀)) y = y := fun y => by
    rw [hE, neg_zero, zpow_zero, Equiv.Perm.one_apply]
  have hback : ∀ y, (f₀ ^ (-E j)) y ∈ W → g⁻¹ y = (f₀ ^ (-E j)) y := by
    intro y hk
    calc g⁻¹ y = g⁻¹ ((f₀ ^ E j) ((f₀ ^ (-E j)) y)) := by
          rw [perm_zpow_apply_zpow_apply, add_neg_cancel, zpow_zero, Equiv.Perm.one_apply]
      _ = (f₀ ^ (-E j)) y := by rw [← hg _ hk, perm_inv_apply_self]
  have hU : ∀ x ∈ W, g x ∉ W := by
    intro x hx hgx
    have h1 : (f₀ ^ (-E i₀)) (g x) ∈ W := by
      rw [hW0]
      exact hgx
    have h2 : (f₀ ^ (-E j)) (g x) ∈ W := by
      rw [hg x hx, perm_zpow_neg_apply_zpow_apply]
      exact hx
    exact hij (hdisj i₀ j (g x) h1 h2)
  refine Equiv.ext fun y => ?_
  by_cases hy : y ∈ W
  · have h0 : (f₀ ^ (-E i₀)) y ∈ W := by
      rw [hW0]
      exact hy
    rw [swapAlong_apply hU, swapFun_of_mem hy, towerPerm_apply, towerFun_of_mem hdisj h0,
      Equiv.swap_apply_left, hE, sub_zero, hg y hy]
  · by_cases hz : g⁻¹ y ∈ W
    · have e : (f₀ ^ (-E j)) y = g⁻¹ y := by
        calc (f₀ ^ (-E j)) y = (f₀ ^ (-E j)) ((f₀ ^ E j) (g⁻¹ y)) := by
              rw [← hg _ hz, perm_apply_inv_self]
          _ = g⁻¹ y := perm_zpow_neg_apply_zpow_apply f₀ (E j) (g⁻¹ y)
      have hlev : (f₀ ^ (-E j)) y ∈ W := by
        rw [e]
        exact hz
      rw [swapAlong_apply hU, swapFun_of_inv_mem hy hz, towerPerm_apply,
        towerFun_of_mem hdisj hlev, Equiv.swap_apply_right, hE, zero_sub, e]
    · rw [swapAlong_apply hU, swapFun_of_not_mem hy hz, towerPerm_apply]
      by_cases hex : ∃ k, (f₀ ^ (-E k)) y ∈ W
      · obtain ⟨k, hk⟩ := hex
        have hk0 : k ≠ i₀ := by
          intro hk0
          rw [hk0, hW0] at hk
          exact hy hk
        have hkj : k ≠ j := by
          intro hkj
          rw [hkj] at hk
          rw [hback y hk] at hz
          exact hz hk
        rw [towerFun_of_mem hdisj hk, Equiv.swap_apply_of_ne_of_ne hk0 hkj, sub_self, zpow_zero,
          Equiv.Perm.one_apply]
      · exact (towerFun_of_not hex).symm

end TowerPerm

end Matui
end StepanovMatui
end Full
end GroupApproximation

#audit_axioms GroupApproximation.Full.StepanovMatui.Matui.mem_fullGroup_of_piecewise
#audit_axioms GroupApproximation.Full.StepanovMatui.Matui.towerPerm_mem_fullGroup
#audit_axioms GroupApproximation.Full.StepanovMatui.Matui.towerPerm_supportedIn
#audit_axioms GroupApproximation.Full.StepanovMatui.Matui.swapAlong_eq_towerPerm
