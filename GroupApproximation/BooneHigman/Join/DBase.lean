import GroupApproximation.BooneHigman.Join.Rigid
import GroupApproximation.BooneHigman.Join.HigmanVCalibCore

/-!
# General-alphabet tools for the normal form of `V_d` (lane bh-pal-met-join)

Here `Q = higmanVCCommon_Q d`, for any alphabet size `d`.

* Incomparability of extensions: `dinc_append`, `dinc_cons`.
* Cone maps of products, inverses, prefix lifts and letters: the `dmc_*` lemmas.
* `jH_eq_one_of_jperm`: an element of an antichain subgroup whose boundary action is trivial
  is `1`.  So two elements of one antichain subgroup with the same action are equal
  (`jH_eq_of_jperm`).
* `jL_split_prod`: the split relator, as a product over the alphabet.
* `jL_symmD`: letters are symmetric.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace GroupApproximation.BooneHigman.Join

open GroupApproximation.BooneHigman.Metabelian.Envelope

variable {d : ℕ}

/-- Incomparable words have incomparable extensions. -/
theorem dinc_append {X : Type*} {x y : List X} (h1 : ¬ x <+: y) (h2 : ¬ y <+: x)
    (u v : List X) : ¬ x ++ u <+: y ++ v := by
  intro h
  rcases List.prefix_or_prefix_of_prefix ((List.prefix_append x u).trans h)
      (List.prefix_append y v) with h' | h'
  · exact h1 h'
  · exact h2 h'

#audit_axioms GroupApproximation.BooneHigman.Join.dinc_append

theorem dinc_append_left {X : Type*} {x y : List X} (h1 : ¬ x <+: y) (h2 : ¬ y <+: x)
    (u : List X) : ¬ x ++ u <+: y := by
  have h := dinc_append h1 h2 u []
  rwa [List.append_nil] at h

#audit_axioms GroupApproximation.BooneHigman.Join.dinc_append_left

theorem dinc_append_right {X : Type*} {x y : List X} (h1 : ¬ x <+: y) (h2 : ¬ y <+: x)
    (v : List X) : ¬ x <+: y ++ v := by
  have h := dinc_append h1 h2 [] v
  rwa [List.append_nil] at h

#audit_axioms GroupApproximation.BooneHigman.Join.dinc_append_right

/-- Words that branch at different letters are incomparable. -/
theorem dinc_cons {X : Type*} (x : List X) {a b : X} (hab : a ≠ b) (u v : List X) :
    ¬ x ++ a :: u <+: x ++ b :: v := by
  rw [List.prefix_append_right_inj, List.cons_prefix_cons]
  exact fun h => hab h.1

#audit_axioms GroupApproximation.BooneHigman.Join.dinc_cons

theorem dinc_child {X : Type*} (x : List X) {a b : X} (hab : a ≠ b) :
    ¬ x ++ [a] <+: x ++ [b] :=
  dinc_cons x hab [] []

#audit_axioms GroupApproximation.BooneHigman.Join.dinc_child

theorem dmc_mul {a b : higmanVCCommon_Q d} {u v w : List (Fin d)} (ha : MapsCone (jperm d a) u v)
    (hb : MapsCone (jperm d b) v w) : MapsCone (jperm d (b * a)) u w := by
  rw [jperm_mul]
  exact MapsCone.comp ha hb

#audit_axioms GroupApproximation.BooneHigman.Join.dmc_mul

theorem dmc_inv {a : higmanVCCommon_Q d} {u v : List (Fin d)} (ha : MapsCone (jperm d a) u v) :
    MapsCone (jperm d a⁻¹) v u := by
  rw [jperm_inv]
  exact ha.inv

#audit_axioms GroupApproximation.BooneHigman.Join.dmc_inv

theorem dmc_one (u : List (Fin d)) : MapsCone (jperm d 1) u u := by
  rw [jperm_one]
  exact mapsCone_one u

#audit_axioms GroupApproximation.BooneHigman.Join.dmc_one

theorem dmc_pow {a : higmanVCCommon_Q d} {u : List (Fin d)} (ha : MapsCone (jperm d a) u u) :
    ∀ n : ℕ, MapsCone (jperm d (a ^ n)) u u
  | 0 => by rw [pow_zero]; exact dmc_one u
  | n + 1 => by rw [pow_succ]; exact dmc_mul ha (dmc_pow ha n)

#audit_axioms GroupApproximation.BooneHigman.Join.dmc_pow

theorem dmc_loc (w : List (Fin d)) {g : Equiv.Perm (Cantor (Fin d))} {c c' : List (Fin d)}
    (h : MapsCone g c c') : MapsCone (localize w g) (w ++ c) (w ++ c') := by
  intro y
  rw [prepend_append, localize_apply_prepend, h y, ← prepend_append]

#audit_axioms GroupApproximation.BooneHigman.Join.dmc_loc

theorem dmc_loc_fix (w : List (Fin d)) (g : Equiv.Perm (Cantor (Fin d))) {c : List (Fin d)}
    (h1 : ¬ w <+: c) (h2 : ¬ c <+: w) : MapsCone (localize w g) c c :=
  fun y => localize_apply_of_not (fun h => Set.disjoint_left.mp (disjoint_cone h1 h2) h
    (prepend_mem_cone c y)) g

#audit_axioms GroupApproximation.BooneHigman.Join.dmc_loc_fix

theorem dmc_phi (w : List (Fin d)) {a : higmanVCCommon_Q d} {u v : List (Fin d)}
    (ha : MapsCone (jperm d a) u v) : MapsCone (jperm d (jPhi d w a)) (w ++ u) (w ++ v) := by
  rw [jperm_jPhi]
  exact dmc_loc w ha

#audit_axioms GroupApproximation.BooneHigman.Join.dmc_phi

theorem dmc_phi_fix (w : List (Fin d)) (a : higmanVCCommon_Q d) {c : List (Fin d)}
    (h1 : ¬ w <+: c) (h2 : ¬ c <+: w) : MapsCone (jperm d (jPhi d w a)) c c := by
  rw [jperm_jPhi]
  exact dmc_loc_fix w _ h1 h2

#audit_axioms GroupApproximation.BooneHigman.Join.dmc_phi_fix

theorem dmc_jL_left {x y : List (Fin d)} (h1 : ¬ x <+: y) (h2 : ¬ y <+: x) :
    MapsCone (jperm d (jL x y)) x y := by
  rw [jperm_jL h1 h2]
  exact mapsCone_coneSwap_left h1 h2

#audit_axioms GroupApproximation.BooneHigman.Join.dmc_jL_left

theorem dmc_jL_right {x y : List (Fin d)} (h1 : ¬ x <+: y) (h2 : ¬ y <+: x) :
    MapsCone (jperm d (jL x y)) y x := by
  rw [jperm_jL h1 h2]
  exact mapsCone_coneSwap_right h1 h2

#audit_axioms GroupApproximation.BooneHigman.Join.dmc_jL_right

theorem dmc_jL_fix {x y z : List (Fin d)} (h1 : ¬ x <+: y) (h2 : ¬ y <+: x)
    (hxz : ¬ x <+: z) (hzx : ¬ z <+: x) (hyz : ¬ y <+: z) (hzy : ¬ z <+: y) :
    MapsCone (jperm d (jL x y)) z z := by
  rw [jperm_jL h1 h2]
  exact mapsCone_coneSwap_fix h1 h2 hxz hzx hyz hzy

#audit_axioms GroupApproximation.BooneHigman.Join.dmc_jL_fix

/-- **Letters are symmetric.** -/
theorem jL_symmD (hd : 1 < d) {x y : List (Fin d)} (h1 : ¬ x <+: y) (h2 : ¬ y <+: x) :
    jL x y = jL y x := by
  have h := rcl hd (jL x y) h1 h2 (dmc_jL_left h1 h2) (dmc_jL_right h1 h2)
  rw [jL_sq, one_mul, jL_inv] at h
  exact h

#audit_axioms GroupApproximation.BooneHigman.Join.jL_symmD

/-- The split relator, as a product over the alphabet. -/
theorem jL_split_prod {x y : List (Fin d)} (h1 : ¬ x <+: y) (h2 : ¬ y <+: x) :
    jL x y = ((List.finRange d).map fun a => jL (x ++ [a]) (y ++ [a])).prod := by
  unfold jL
  rw [higmanVCCommon_mk_split h1 h2, higmanVC_splitAll, map_list_prod, List.map_map]
  all_goals rfl

#audit_axioms GroupApproximation.BooneHigman.Join.jL_split_prod

/-- **An element of an antichain subgroup acting trivially is `1`.** -/
theorem jH_eq_one_of_jperm (hd : 1 < d) {C : Finset (List (Fin d))} (hC : IsAC C)
    {σ : higmanVCCommon_Q d} (hσ : σ ∈ jH d C) (h : jperm d σ = 1) : σ = 1 := by
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr hd
  obtain ⟨r, rfl⟩ := MonoidHom.mem_range.mp hσ
  have hπ : FreeGroup.lift (fun p : ↥C × ↥C => Equiv.swap p.1 p.2) r = 1 := by
    refine Equiv.ext fun a => Subtype.ext ?_
    have h1 : MapsCone (jperm d (((higmanVCCommon_mk d).comp (higmanVCAll_iota C)) r)) a.1
        (FreeGroup.lift (fun p : ↥C × ↥C => Equiv.swap p.1 p.2) r a).1 :=
      higmanVCAll_mapsCone_word hC r a
    rw [h] at h1
    exact (MapsCone.unique (mapsCone_one a.1) h1).symm
  have h1 : higmanVCAll_iota C r ∈ Subgroup.normalClosure (higmanVC_rels d fun _ => True) := by
    rw [← QuotientGroup.ker_mk' (Subgroup.normalClosure (higmanVC_rels d fun _ => True)),
      MonoidHom.mem_ker, higmanVCAll_mk_iota]
    exact higmanVCAll_lift_eq_one (higmanVCAll_gen d C) higmanVCAll_gen_self higmanVCAll_gen_sq
      (higmanVCAll_gen_conj hC) r hπ
  exact higmanVCCommon_mk_eq_one_iff.mpr h1

#audit_axioms GroupApproximation.BooneHigman.Join.jH_eq_one_of_jperm

/-- Two elements of one antichain subgroup with the same action are equal. -/
theorem jH_eq_of_jperm (hd : 1 < d) {C : Finset (List (Fin d))} (hC : IsAC C)
    {σ τ : higmanVCCommon_Q d} (hσ : σ ∈ jH d C) (hτ : τ ∈ jH d C)
    (h : jperm d σ = jperm d τ) : σ = τ := by
  have h1 : τ⁻¹ * σ = 1 := by
    refine jH_eq_one_of_jperm hd hC ((jH d C).mul_mem ((jH d C).inv_mem hτ) hσ) ?_
    rw [jperm_mul, jperm_inv, h, inv_mul_cancel]
  exact (inv_mul_eq_one.mp h1).symm

#audit_axioms GroupApproximation.BooneHigman.Join.jH_eq_of_jperm

end GroupApproximation.BooneHigman.Join
