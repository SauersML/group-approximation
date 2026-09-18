import GroupApproximation.BooneHigman.Metabelian.EnvelopeRelatorsKernelAct
import GroupApproximation.BooneHigman.Metabelian.EnvelopeSimpleFragCantor
import GroupApproximation.Meta.AxiomGuard

/-!
# Faithfulness: a trivial normal form has trivial deep states

* `rnKer_eq_nil_of_prepend`: if `r · F(y) = y` for every stream `y`, then `r = []`.
* `rnKer_state_eq_one_of_depth`: let `f` have depth `D`, and suppose `f` acts on the cone of `w`
  as the tree automorphism `g` does, i.e. `f (w y) = w (g y)`.  Then every state of `g` at depth
  `D` is trivial.  On the cone of `w t` with `|t| = D`, `f` is a cone map `w t ↦ u`, while `g`
  sends `w t y` to `w (g • t) (g|_t y)`.  Comparing the two prefixes `u` and `w (g • t)` forces
  `g|_t` to fix every stream, and `cantorHom` is injective.
* `rnKer_states_trivial`: if the raw normal-form word `rnKerWord H v L` acts trivially and the
  words recorded in `L` are pairwise incomparable, there is a depth `D` at which every state of
  every `h` in `L` is trivial.  The product of the localized copies equals `v⁻¹ ∈ V_X`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

open Trees

noncomputable section

variable {X : Type*}

/-- A nonempty word cannot be prepended onto every stream: its first letter is missed. -/
theorem rnKer_eq_nil_of_prepend [Nontrivial X] {r : List X} (F : Cantor X → Cantor X)
    (h : ∀ y, prepend r (F y) = y) : r = [] := by
  cases r with
  | nil => rfl
  | cons a r =>
    obtain ⟨b, hb⟩ := exists_ne a
    have h0 : prepend (a :: r) (F fun _ => b) 0 = b := congrFun (h fun _ => b) 0
    rw [prepend_getElem (a :: r) (F fun _ => b) (Nat.zero_lt_succ r.length),
      List.getElem_cons_zero] at h0
    exact absurd h0.symm hb

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnKer_eq_nil_of_prepend

/-- A map of finite depth that acts on the cone of `w` through a tree automorphism `g` forces
all states of `g` at that depth to be trivial. -/
theorem rnKer_state_eq_one_of_depth [Nontrivial X] {f : Equiv.Perm (Cantor X)} {D : ℕ}
    (hf : HasDepth f D) (w : List X) (g : TreeAut X)
    (hw : ∀ y, f (prepend w y) = prepend w (cantorHom g y)) (t : List X) (ht : t.length = D) :
    TreeAut.state g t = 1 := by
  obtain ⟨u, hu⟩ := hf.mono (Nat.le_add_left D w.length) (w ++ t)
    (by rw [List.length_append, ht])
  have key : ∀ y, prepend u y = prepend (w ++ g • t) (cantorHom (TreeAut.state g t) y) :=
    fun y => by rw [← hu y, prepend_append, hw, frag_cantorHom_prepend, prepend_append]
  have y₀ : Cantor X := fun _ => Classical.arbitrary X
  have hc : ∀ y, cantorHom (TreeAut.state g t) y = y := by
    rcases le_total u.length (w ++ g • t).length with hle | hle
    · obtain ⟨r, hr⟩ := prefix_of_prepend_eq (key y₀) hle
      have hr' : ∀ y, prepend r (cantorHom (TreeAut.state g t) y) = y := fun y => by
        apply prepend_injective u
        rw [← prepend_append, hr, ← key y]
      have hr0 := rnKer_eq_nil_of_prepend _ hr'
      intro y
      have hy := hr' y
      rw [hr0, prepend_nil] at hy
      exact hy
    · obtain ⟨r, hr⟩ := prefix_of_prepend_eq (key y₀).symm hle
      have hr' : ∀ y, prepend r y = cantorHom (TreeAut.state g t) y := fun y => by
        apply prepend_injective (w ++ g • t)
        rw [← prepend_append, hr, key y]
      have hr'' : ∀ y, prepend r ((cantorHom (TreeAut.state g t)).symm y) = y := fun y => by
        rw [hr', Equiv.apply_symm_apply]
      have hr0 := rnKer_eq_nil_of_prepend _ hr''
      intro y
      have hy := hr' y
      rw [hr0, prepend_nil] at hy
      exact hy.symm
  apply cantorHom_injective (X := X)
  rw [map_one]
  exact Equiv.ext hc

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnKer_state_eq_one_of_depth

/-- **Faithfulness.**  A raw normal-form word over pairwise incomparable cones that acts
trivially on the Cantor set has all its local elements trivial at some common depth. -/
theorem rnKer_states_trivial [Finite X] [Nontrivial X] (H : Subgroup (TreeAut X)) (x₀ : X)
    (v : ↥(higmanThompsonV X)) (L : List (↥(higmanThompsonV X) × List X × ↥H))
    (hL : ∀ p ∈ L, MapsCone (p.1 : Equiv.Perm (Cantor X)) [x₀] p.2.1)
    (hpair : L.Pairwise fun p q => ¬ p.2.1 <+: q.2.1 ∧ ¬ q.2.1 <+: p.2.1)
    (h1 : rnFreeToPerm H x₀ (rnKerWord H v L) = 1) :
    ∃ D : ℕ, ∀ p ∈ L, ∀ t : List X, t.length = D →
      TreeAut.state (p.2.2 : TreeAut X) t = 1 := by
  rw [rnKerWord_toPerm H x₀ v L hL] at h1
  have hP := eq_inv_of_mul_eq_one_right h1
  obtain ⟨D, hD⟩ := mem_higmanThompsonV.mp (v⁻¹).2
  rw [Subgroup.coe_inv, ← hP] at hD
  exact ⟨D, fun p hp t ht => rnKer_state_eq_one_of_depth hD p.2.1 (p.2.2 : TreeAut X)
    (rnKer_prod_localize_apply (fun q : ↥(higmanThompsonV X) × List X × ↥H => q.2.1)
      (fun q => cantorHom (q.2.2 : TreeAut X)) L hpair p hp) t ht⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnKer_states_trivial

end

end GroupApproximation.BooneHigman.Metabelian.Envelope
