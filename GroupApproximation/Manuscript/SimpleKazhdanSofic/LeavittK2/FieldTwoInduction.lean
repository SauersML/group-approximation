import Mathlib.Data.Fin.Tuple.Basic
import GroupApproximation.BooneHigman.SteinbergBasic.Naturality
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnK2.BaseChange
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwoDihedral
import GroupApproximation.Meta.AxiomGuard

/-!
# Stable `K₂(𝔽₂) = 0` (lane sk-leavitt-23)

* `act_indexMap_castSucc`: the padding `St_N → St_{N+1}` is compatible with restricting
  vectors to the first `N` coordinates.
* `lev_last_mem_range`: `levSpan (last N)` lies in the image of `St_N(𝔽₂)`.
* `inj_succ`: take `g ∈ St_{N+1}(𝔽₂)` acting trivially.  It lies in `levSpan (last N)`
  (`mem_levSpan_of_act`), so it is padded from some `t ∈ St_N(𝔽₂)` acting trivially.
  So `Inj N → Inj (N + 1)` for `N ≥ 3`.  With `inj_three` this gives `Inj N` for `N ≥ 3`.
* `fieldTwoStableK2`: an element of `K₂(n, 𝔽₂)` padded to `St_{n+3}(𝔽₂)` acts trivially,
  hence is trivial.  This proves `FieldTwoStableK2Statement`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo

open GroupApproximation.SteinbergGroup

theorem act_indexMap_castSucc {N : ℕ} {R : Type*} [Ring R] (t : SteinbergGroup (Fin N) R)
    (v : Fin (N + 1) → R) (m : Fin N) :
    act (indexMap Fin.castSuccEmb t) v m.castSucc = act t (fun m => v m.castSucc) m := by
  refine (rootSpan_induction (p := fun _ _ : Fin N => True)
    (Q := fun t => ∀ (v : Fin (N + 1) → R) (m : Fin N),
      act (indexMap Fin.castSuccEmb t) v m.castSucc = act t (fun m => v m.castSucc) m)
    ?_ ?_ ?_ (mem_rootSpan_true t)) v m
  · intro i j h a _ v m
    show act (indexMap Fin.castSuccEmb (x i j h a)) v m.castSucc =
      act (x i j h a) (fun m => v m.castSucc) m
    rw [indexMap_x, act_x_apply, act_x_apply, Fin.castSuccEmb_apply, Fin.castSuccEmb_apply]
    by_cases hm : m = i
    · rw [if_pos hm, if_pos (congrArg Fin.castSucc hm)]
    · rw [if_neg hm, if_neg (fun e => hm (Fin.castSucc_inj.mp e))]
  · intro v m
    show act (indexMap Fin.castSuccEmb (1 : SteinbergGroup (Fin N) R)) v m.castSucc =
      act (1 : SteinbergGroup (Fin N) R) (fun m => v m.castSucc) m
    rw [map_one, act_one, act_one]
  · intro g k _ _ hg hk v m
    show act (indexMap Fin.castSuccEmb (g * k)) v m.castSucc =
      act (g * k) (fun m => v m.castSucc) m
    rw [map_mul, act_mul, act_mul, hg,
      show (fun m => act (indexMap Fin.castSuccEmb k) v m.castSucc) =
        act k (fun m => v m.castSucc) from funext (hk v)]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.act_indexMap_castSucc

theorem lev_last_mem_range {N : ℕ} {g : SteinbergGroup (Fin (N + 1)) (ZMod 2)}
    (hg : g ∈ levSpan (Fin.last N)) :
    ∃ t : SteinbergGroup (Fin N) (ZMod 2), indexMap Fin.castSuccEmb t = g := by
  refine rootSpan_induction (p := fun i j : Fin (N + 1) => i ≠ Fin.last N ∧ j ≠ Fin.last N)
    (Q := fun g => ∃ t : SteinbergGroup (Fin N) (ZMod 2), indexMap Fin.castSuccEmb t = g)
    ?_ ?_ ?_ hg
  · intro i j h a (hp : i ≠ Fin.last N ∧ j ≠ Fin.last N)
    obtain ⟨i', rfl⟩ := Fin.exists_castSucc_eq.mpr hp.1
    obtain ⟨j', rfl⟩ := Fin.exists_castSucc_eq.mpr hp.2
    have h' : i' ≠ j' := fun e => h (congrArg Fin.castSucc e)
    exact ⟨x i' j' h' a, indexMap_x Fin.castSuccEmb i' j' h' a⟩
  · exact ⟨1, map_one _⟩
  · rintro g k _ _ ⟨t₁, rfl⟩ ⟨t₂, rfl⟩
    exact ⟨t₁ * t₂, map_mul _ t₁ t₂⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.lev_last_mem_range

theorem inj_succ {N : ℕ} (hN : 3 ≤ N) (ih : Inj N) : Inj (N + 1) := by
  intro g hg
  have hthird : ∀ a b : Fin (N + 1), ∃ m : Fin (N + 1), m ≠ a ∧ m ≠ b := fun a b =>
    WeylCalc.exists_third (by omega) a b
  obtain ⟨t, rfl⟩ := lev_last_mem_range (mem_levSpan_of_act hthird (Fin.last N) hg)
  have ht : ∀ w : Fin N → ZMod 2, act t w = w := by
    intro w
    funext m
    have e := congrFun (hg (Fin.snoc (α := fun _ => ZMod 2) w 0)) m.castSucc
    rw [act_indexMap_castSucc] at e
    simpa only [Fin.snoc_castSucc] using e
  rw [ih t ht, map_one]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.inj_succ

theorem inj_of_three_le {M : ℕ} (hM : 3 ≤ M) : Inj M := by
  induction M, hM using Nat.le_induction with
  | base => exact inj_three
  | succ N hN ih => exact inj_succ hN ih

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.inj_of_three_le

/-- **Stable `K₂(𝔽₂) = 0`.** Every `y ∈ K₂(n, 𝔽₂)` dies in `St_{n+3}(𝔽₂)`. -/
theorem fieldTwoStableK2 : FieldTwoStableK2Statement := by
  intro n y hy
  refine ⟨n + 3, by omega, ?_⟩
  refine inj_of_three_le (M := n + 3) (by omega) _ (fun v => act_of_projection_eq_one ?_ v)
  rw [GroupApproximation.BooneHigman.SteinbergBasic.projection_indexMap,
    (GroupApproximation.BooneHigman.SteinbergBasic.mem_K2_iff y).mp hy, map_one]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.fieldTwoStableK2

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo
