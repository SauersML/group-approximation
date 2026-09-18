import GroupApproximation.BooneHigman.Metabelian.VdKInjActPerm
import GroupApproximation.Meta.AxiomGuard

/-!
# van der Kallen's injectivity action, part 3: the action and the base-point argument

Lane `bh-met-91o`.  Fix a row cocycle `c` (`vdkInjAct_IsCocycle c`).

* `vdkInjAct_genPerm_kills`: the permutations `(vdkInjAct_perm hc i j hij a)⁻¹` kill every
  Steinberg relator of `St_{n+1}(R)`.  This is `vdkInjAct_move_add`, `_commute` and `_adjacent`.
* `vdkInjAct_hom hc : St_{n+1}(R) →* Perm (St_n(R) × R^{n+1})` is the induced action.
* `vdkInjAct_baseSubgroup hc`: the `g ∈ St_n(R)` whose stabilization acts on the fibre over the
  base row `e_last` by right multiplication by `g⁻¹`.
* If `c` is based (`vdkInjAct_IsBased c`), every generator `x_{ij}(a)` of `St_n(R)` lies in the
  base subgroup.  Its stabilization fixes `e_last` (`vdkInjCoset_x_mem`), and its cocycle value
  there is `x_{ij}(a)`.  So the base subgroup is everything.
* `vdkInjAct_stab_injective_of_cocycle`: if `stab g = 1`, then `(1, e_last) = (g⁻¹, e_last)`.
  Hence `g = 1`, and `vdkInjAct_K2Stab_injective_of_cocycle` follows.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open scoped commutatorElement

variable {n : ℕ} {R : Type*} [CommRing R] {c : vdkInjAct_Cocycle n R}

theorem vdkInjAct_perm_add (hc : vdkInjAct_IsCocycle c) (i j : Fin (n + 1)) (hij : i ≠ j)
    (a b : R) :
    vdkInjAct_perm hc i j hij b * vdkInjAct_perm hc i j hij a =
      vdkInjAct_perm hc i j hij (a + b) :=
  Equiv.ext fun z ↦ vdkInjAct_move_add hc i j hij a b z

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_perm_add

theorem vdkInjAct_perm_commute (hc : vdkInjAct_IsCocycle c) (i j k l : Fin (n + 1))
    (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (hli : l ≠ i) (a b : R) :
    vdkInjAct_perm hc k l hkl b * vdkInjAct_perm hc i j hij a =
      vdkInjAct_perm hc i j hij a * vdkInjAct_perm hc k l hkl b :=
  Equiv.ext fun z ↦ vdkInjAct_move_commute hc i j k l hij hkl hjk hli a b z

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_perm_commute

theorem vdkInjAct_perm_adjacent (hc : vdkInjAct_IsCocycle c) (i j k : Fin (n + 1))
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) :
    vdkInjAct_perm hc j k hjk b * vdkInjAct_perm hc i j hij a =
      vdkInjAct_perm hc i j hij a * vdkInjAct_perm hc j k hjk b *
        vdkInjAct_perm hc i k hik (a * b) :=
  Equiv.ext fun z ↦ vdkInjAct_move_adjacent hc i j k hij hjk hik a b z

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_perm_adjacent

/-- The permutation attached to a Steinberg generator `x_{ij}(a)` of `St_{n+1}(R)`: the inverse
of the right action `move_{ij}(a)`. -/
noncomputable def vdkInjAct_genPerm (hc : vdkInjAct_IsCocycle c)
    (g : SteinbergGenerator (Fin (n + 1)) R) : Equiv.Perm (St n R × (Fin (n + 1) → R)) :=
  (vdkInjAct_perm hc g.row g.column g.row_ne_column g.coefficient)⁻¹

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_genPerm

/-- The relation checks: every Steinberg relator of `St_{n+1}(R)` acts trivially. -/
theorem vdkInjAct_genPerm_kills (hc : vdkInjAct_IsCocycle c)
    (w : FreeGroup (SteinbergGenerator (Fin (n + 1)) R))
    (hw : w ∈ SteinbergGroup.relations (I := Fin (n + 1)) (R := R)) :
    FreeGroup.lift (vdkInjAct_genPerm hc) w = 1 := by
  change SteinbergGroup.IsRelation w at hw
  cases hw with
  | add i j hij a b =>
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of, vdkInjAct_genPerm]
      change (vdkInjAct_perm hc i j hij a)⁻¹ * (vdkInjAct_perm hc i j hij b)⁻¹ *
        ((vdkInjAct_perm hc i j hij (a + b))⁻¹)⁻¹ = 1
      exact vdkInjAct_add_aux (vdkInjAct_perm_add hc i j hij a b)
  | commute i j k l hij hkl hjk hli a b =>
      simp only [map_commutatorElement, FreeGroup.lift_apply_of, vdkInjAct_genPerm]
      change ⁅(vdkInjAct_perm hc i j hij a)⁻¹, (vdkInjAct_perm hc k l hkl b)⁻¹⁆ = 1
      exact vdkInjAct_comm_aux (vdkInjAct_perm_commute hc i j k l hij hkl hjk hli a b)
  | adjacent i j k hij hjk hik a b =>
      simp only [map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of,
        vdkInjAct_genPerm]
      change ⁅(vdkInjAct_perm hc i j hij a)⁻¹, (vdkInjAct_perm hc j k hjk b)⁻¹⁆ *
        ((vdkInjAct_perm hc i k hik (a * b))⁻¹)⁻¹ = 1
      exact vdkInjAct_adj_aux (vdkInjAct_perm_adjacent hc i j k hij hjk hik a b)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_genPerm_kills

/-- The action of `St_{n+1}(R)` on `St_n(R) × R^{n+1}` defined by the row cocycle `c`. -/
noncomputable def vdkInjAct_hom (hc : vdkInjAct_IsCocycle c) :
    St (n + 1) R →* Equiv.Perm (St n R × (Fin (n + 1) → R)) :=
  PresentedGroup.toGroup (f := vdkInjAct_genPerm hc) (vdkInjAct_genPerm_kills hc)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_hom

theorem vdkInjAct_hom_x (hc : vdkInjAct_IsCocycle c) (i j : Fin (n + 1)) (hij : i ≠ j) (a : R) :
    vdkInjAct_hom hc (x i j hij a) = (vdkInjAct_perm hc i j hij a)⁻¹ := by
  exact PresentedGroup.toGroup.of _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_hom_x

/-- The `g ∈ St_n(R)` whose stabilization acts on the fibre over `e_last` by `h ↦ h g⁻¹`. -/
noncomputable def vdkInjAct_baseSubgroup (hc : vdkInjAct_IsCocycle c) : Subgroup (St n R) where
  carrier := {g | ∀ h : St n R, vdkInjAct_hom hc (stab n R g) (h, Pi.single (Fin.last n) 1) =
    (h * g⁻¹, Pi.single (Fin.last n) 1)}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    intro h
    rw [map_mul, map_mul, Equiv.Perm.mul_apply, hb h, ha, mul_inv_rev, mul_assoc]
  one_mem' := by
    simp only [Set.mem_setOf_eq]
    intro h
    rw [map_one, map_one, Equiv.Perm.one_apply, inv_one, mul_one]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    intro h
    rw [map_inv, map_inv, Equiv.Perm.inv_eq_iff_eq, ha, inv_inv, mul_inv_cancel_right]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_baseSubgroup

theorem vdkInjAct_mem_baseSubgroup (hc : vdkInjAct_IsCocycle c) (g : St n R) :
    g ∈ vdkInjAct_baseSubgroup hc ↔ ∀ h : St n R,
      vdkInjAct_hom hc (stab n R g) (h, Pi.single (Fin.last n) 1) =
        (h * g⁻¹, Pi.single (Fin.last n) 1) :=
  Iff.rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_mem_baseSubgroup

/-- A based cocycle puts every generator `x_{ij}(a)` of `St_n(R)` in the base subgroup. -/
theorem vdkInjAct_x_mem_base (hc : vdkInjAct_IsCocycle c) (hb : vdkInjAct_IsBased c)
    (i j : Fin n) (hij : i ≠ j) (a : R) : x i j hij a ∈ vdkInjAct_baseSubgroup hc := by
  have hrow : vdkInjAct_row (Pi.single (Fin.last n) (1 : R))
      (x i.castSucc j.castSucc (fun h ↦ hij (Fin.castSucc_inj.mp h)) a) =
        Pi.single (Fin.last n) 1 :=
    (vdkInjCoset_mem_rowStab _).mp (vdkInjCoset_x_mem _ _ _ a (Fin.castSucc_ne_last i))
  rw [vdkInjAct_mem_baseSubgroup]
  intro h
  rw [stab_x, vdkInjAct_hom_x, Equiv.Perm.inv_eq_iff_eq, vdkInjAct_perm_apply,
    hb i j hij _ a, inv_mul_cancel_right, hrow]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_x_mem_base

theorem vdkInjAct_mem_base_all (hc : vdkInjAct_IsCocycle c) (hb : vdkInjAct_IsBased c)
    (g : St n R) : g ∈ vdkInjAct_baseSubgroup hc := by
  refine PresentedGroup.generated_by _ (vdkInjAct_baseSubgroup hc) ?_ g
  rintro ⟨i, j, hij, a⟩
  exact vdkInjAct_x_mem_base hc hb i j hij a

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_mem_base_all

/-- **Base-point injectivity.**  A based row cocycle makes `stab : St_n(R) → St_{n+1}(R)`
injective. -/
theorem vdkInjAct_stab_injective_of_cocycle (hc : vdkInjAct_IsCocycle c)
    (hb : vdkInjAct_IsBased c) : Function.Injective (stab n R) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h := (vdkInjAct_mem_baseSubgroup hc g).mp (vdkInjAct_mem_base_all hc hb g) 1
  rw [hg, map_one, Equiv.Perm.one_apply, one_mul] at h
  have h1 : g⁻¹ = 1 := (congrArg Prod.fst h).symm
  exact inv_eq_one.mp h1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_stab_injective_of_cocycle

theorem vdkInjAct_K2Stab_injective_of_cocycle (hc : vdkInjAct_IsCocycle c)
    (hb : vdkInjAct_IsBased c) : Function.Injective (K2Stab n R) := by
  intro u v huv
  refine Subtype.ext (vdkInjAct_stab_injective_of_cocycle hc hb ?_)
  exact congrArg Subtype.val huv

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_K2Stab_injective_of_cocycle

end GroupApproximation.BooneHigman.Metabelian.ElemFP

