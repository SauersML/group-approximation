import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCSwindleHom
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Tactic.Group

/-!
# Rigid conjugation in the all-swaps quotient (lane bh-pal-met-join)

`Q = higmanVCCommon_Q d` is the all-swaps free group modulo the standard relators.  This file
proves that conjugation in `Q` follows the boundary action whenever the latter is rigid.

* `jE d : Q →* V_d` is the evaluation, and `jperm d q` is the boundary permutation of `q`.
* `jL x y` is the class of the letter `(x, y)`.
* `rcl`: if `jperm d q` carries the cones of incomparable words `x`, `y` onto the cones of
  `x'`, `y'` by prefix substitution, then `q · (x, y) · q⁻¹ = (x', y')`.  The proof splits the
  letter deep enough for the push property (`higmanVCCommon_push`), conjugates the pieces, and
  recombines them (`higmanVCCommon_mk_deep`).
* `jH d C` is the antichain subgroup of `C`, and `rcl_H` conjugates it rigidly.
* `jPhi d c : Q →* Q` is the prefix endomorphism `(x, y) ↦ (c x, c y)`, and `rcl_phi` says
  `q · jPhi c r · q⁻¹ = jPhi c' r` whenever `jperm d q` carries the cone of `c` onto that of `c'`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace GroupApproximation.BooneHigman.Join

open GroupApproximation.BooneHigman.Metabelian.Envelope

variable {d : ℕ}

/-- The evaluation of the all-swaps quotient in `V_d`. -/
noncomputable def jE (d : ℕ) : higmanVCCommon_Q d →* ↥(higmanThompsonV (Fin d)) :=
  QuotientGroup.lift (Subgroup.normalClosure (higmanVC_rels d fun _ => True)) (higmanVC_evalAll d)
    (Subgroup.normalClosure_le_normal (higmanVC_rels_subset_ker d fun _ => True))

#audit_axioms GroupApproximation.BooneHigman.Join.jE

/-- The boundary permutation of an element of the quotient. -/
noncomputable def jperm (d : ℕ) (q : higmanVCCommon_Q d) : Equiv.Perm (Cantor (Fin d)) :=
  (jE d q : Equiv.Perm (Cantor (Fin d)))

#audit_axioms GroupApproximation.BooneHigman.Join.jperm

theorem jperm_mk (g : FreeGroup (List (Fin d) × List (Fin d))) :
    jperm d (higmanVCCommon_mk d g) = higmanVCCommon_perm d g :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Join.jperm_mk

theorem jperm_mul (q r : higmanVCCommon_Q d) : jperm d (q * r) = jperm d q * jperm d r := by
  unfold jperm
  rw [map_mul, Subgroup.coe_mul]

#audit_axioms GroupApproximation.BooneHigman.Join.jperm_mul

theorem jperm_inv (q : higmanVCCommon_Q d) : jperm d q⁻¹ = (jperm d q)⁻¹ := by
  unfold jperm
  rw [map_inv, Subgroup.coe_inv]

#audit_axioms GroupApproximation.BooneHigman.Join.jperm_inv

theorem jperm_one : jperm d 1 = 1 := by
  unfold jperm
  rw [map_one, Subgroup.coe_one]

#audit_axioms GroupApproximation.BooneHigman.Join.jperm_one

theorem mk_surj (q : higmanVCCommon_Q d) : ∃ g, higmanVCCommon_mk d g = q :=
  QuotientGroup.mk'_surjective _ q

#audit_axioms GroupApproximation.BooneHigman.Join.mk_surj

/-- The class of the letter `(x, y)`. -/
noncomputable def jL (x y : List (Fin d)) : higmanVCCommon_Q d :=
  higmanVCCommon_mk d (FreeGroup.of (x, y))

#audit_axioms GroupApproximation.BooneHigman.Join.jL

theorem jL_sq (x y : List (Fin d)) : jL x y * jL x y = 1 :=
  higmanVCCommon_mk_sq x y

#audit_axioms GroupApproximation.BooneHigman.Join.jL_sq

theorem jL_inv (x y : List (Fin d)) : (jL x y)⁻¹ = jL x y :=
  inv_eq_of_mul_eq_one_right (jL_sq x y)

#audit_axioms GroupApproximation.BooneHigman.Join.jL_inv

theorem jL_comparable {x y : List (Fin d)} (h : ¬ (¬ x <+: y ∧ ¬ y <+: x)) : jL x y = 1 :=
  higmanVCCommon_mk_comparable h

#audit_axioms GroupApproximation.BooneHigman.Join.jL_comparable

theorem jL_self (x : List (Fin d)) : jL x x = 1 :=
  jL_comparable fun h => h.1 (List.prefix_refl x)

#audit_axioms GroupApproximation.BooneHigman.Join.jL_self

theorem jperm_jL {x y : List (Fin d)} (h1 : ¬ x <+: y) (h2 : ¬ y <+: x) :
    jperm d (jL x y) = coneSwap x y h1 h2 := by
  show higmanVCCommon_perm d (FreeGroup.of (x, y)) = _
  rw [higmanVCCommon_perm_of, vgenSwapOrOne_eq h1 h2]

#audit_axioms GroupApproximation.BooneHigman.Join.jperm_jL

/-- Rigid conjugation of the deep splits of a letter, by induction on the depth. -/
theorem rcl_deep (hd : 1 < d) (g : FreeGroup (List (Fin d) × List (Fin d))) {N : ℕ}
    (hN : HigmanVCCommonPush d g N) (m : ℕ) :
    ∀ {x y x' y' : List (Fin d)}, N ≤ x.length + m → N ≤ y.length + m → ¬ x <+: y →
      ¬ y <+: x → MapsCone (higmanVCCommon_perm d g) x x' →
      MapsCone (higmanVCCommon_perm d g) y y' →
      higmanVCCommon_mk d (g * higmanVCCommon_deep d m x y * g⁻¹) =
        higmanVCCommon_mk d (higmanVCCommon_deep d m x' y') := by
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr hd
  induction m with
  | zero =>
    intro x y x' y' hx hy hxy hyx hmx hmy
    obtain ⟨x'', y'', hx'', hy'', _, _, he⟩ :=
      hN x y (by omega) (by omega) hxy hyx
    rw [MapsCone.unique hx'' hmx, MapsCone.unique hy'' hmy] at he
    exact he
  | succ m ih =>
    intro x y x' y' hx hy hxy hyx hmx hmy
    have hxy' : ¬ x' <+: y' := higmanVCCommon_incomp_image (by omega) hmx hmy hxy hyx
    have hyx' : ¬ y' <+: x' := higmanVCCommon_incomp_image (by omega) hmy hmx hyx hxy
    have hc : ∀ t : FreeGroup (List (Fin d) × List (Fin d)),
        g * t * g⁻¹ = MulAut.conj g t := fun t => rfl
    rw [higmanVCCommon_deep_succ, higmanVCCommon_deep_succ, hc, map_list_prod, map_list_prod,
      map_list_prod, List.map_map, List.map_map, List.map_map]
    refine congrArg List.prod (List.map_congr_left fun a _ => ?_)
    simp only [Function.comp_apply]
    rw [← hc]
    exact ih (by simp only [List.length_append, List.length_singleton]; omega)
      (by simp only [List.length_append, List.length_singleton]; omega)
      (higmanVFP_ext_incomp hxy hyx a a) (higmanVFP_ext_incomp hyx hxy a a)
      (hmx.append [a]) (hmy.append [a])

#audit_axioms GroupApproximation.BooneHigman.Join.rcl_deep

/-- **Rigid conjugation of a letter**, on words. -/
theorem rcl_word (hd : 1 < d) (g : FreeGroup (List (Fin d) × List (Fin d)))
    {x y x' y' : List (Fin d)} (hxy : ¬ x <+: y) (hyx : ¬ y <+: x)
    (hx : MapsCone (higmanVCCommon_perm d g) x x') (hy : MapsCone (higmanVCCommon_perm d g) y y') :
    higmanVCCommon_mk d (g * FreeGroup.of (x, y) * g⁻¹) =
      higmanVCCommon_mk d (FreeGroup.of (x', y')) := by
  obtain ⟨N, hN⟩ := higmanVCCommon_push hd g
  have hxy' : ¬ x' <+: y' := higmanVCCommon_incomp_image (by omega) hx hy hxy hyx
  have hyx' : ¬ y' <+: x' := higmanVCCommon_incomp_image (by omega) hy hx hyx hxy
  have h1 := rcl_deep hd g hN N (x := x) (y := y) (by omega) (by omega) hxy hyx hx hy
  rw [map_mul, map_mul, higmanVCCommon_mk_deep N hxy hyx, higmanVCCommon_mk_deep N hxy' hyx']
    at h1
  rw [map_mul, map_mul]
  exact h1

#audit_axioms GroupApproximation.BooneHigman.Join.rcl_word

/-- **Rigid conjugation of a letter** in the quotient. -/
theorem rcl (hd : 1 < d) (q : higmanVCCommon_Q d) {x y x' y' : List (Fin d)}
    (hxy : ¬ x <+: y) (hyx : ¬ y <+: x) (hx : MapsCone (jperm d q) x x')
    (hy : MapsCone (jperm d q) y y') : q * jL x y * q⁻¹ = jL x' y' := by
  obtain ⟨g, rfl⟩ := mk_surj q
  have h := rcl_word hd g hxy hyx hx hy
  rw [map_mul, map_mul, map_inv] at h
  exact h

#audit_axioms GroupApproximation.BooneHigman.Join.rcl

/-- The antichain subgroup of a finite set of words: the classes of words in its letters. -/
noncomputable def jH (d : ℕ) (C : Finset (List (Fin d))) : Subgroup (higmanVCCommon_Q d) :=
  ((higmanVCCommon_mk d).comp (higmanVCAll_iota C)).range

#audit_axioms GroupApproximation.BooneHigman.Join.jH

theorem jL_mem_jH {C : Finset (List (Fin d))} {x y : List (Fin d)} (hx : x ∈ C) (hy : y ∈ C) :
    jL x y ∈ jH d C :=
  ⟨FreeGroup.of (⟨x, hx⟩, ⟨y, hy⟩), by
    show higmanVCCommon_mk d (higmanVCAll_iota C _) = _
    rw [higmanVCAll_iota_of]
    rfl⟩

#audit_axioms GroupApproximation.BooneHigman.Join.jL_mem_jH

/-- Induction principle for the antichain subgroup: a property of `Q` closed under products and
inverses and true for the letters of `C` holds on `jH d C`. -/
theorem jH_induction {C : Finset (List (Fin d))} {P : higmanVCCommon_Q d → Prop} (h1 : P 1)
    (hL : ∀ x ∈ C, ∀ y ∈ C, P (jL x y)) (hmul : ∀ a b, P a → P b → P (a * b))
    (hinv : ∀ a, P a → P a⁻¹) {σ : higmanVCCommon_Q d} (hσ : σ ∈ jH d C) : P σ := by
  obtain ⟨r, rfl⟩ := MonoidHom.mem_range.mp hσ
  clear hσ
  induction r using FreeGroup.induction_on with
  | C1 => simpa using h1
  | of p =>
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := p
    show P (higmanVCCommon_mk d (higmanVCAll_iota C (FreeGroup.of _)))
    rw [higmanVCAll_iota_of]
    exact hL x hx y hy
  | inv_of p ih =>
    simp only [MonoidHom.comp_apply, map_inv] at ih ⊢
    exact hinv _ ih
  | mul a b iha ihb =>
    simp only [MonoidHom.comp_apply, map_mul] at iha ihb ⊢
    exact hmul _ _ iha ihb

#audit_axioms GroupApproximation.BooneHigman.Join.jH_induction

/-- `C` is an antichain for the prefix order. -/
def IsAC (C : Finset (List (Fin d))) : Prop :=
  ∀ u ∈ C, ∀ v ∈ C, u ≠ v → ¬ u <+: v

#audit_axioms GroupApproximation.BooneHigman.Join.IsAC

/-- **Rigid conjugation of an antichain subgroup.** -/
theorem rcl_H (hd : 1 < d) {C C' : Finset (List (Fin d))} (hC : IsAC C) (q : higmanVCCommon_Q d)
    (hq : ∀ c ∈ C, ∃ c' ∈ C', MapsCone (jperm d q) c c') {σ : higmanVCCommon_Q d}
    (hσ : σ ∈ jH d C) : q * σ * q⁻¹ ∈ jH d C' := by
  refine jH_induction (P := fun s => q * s * q⁻¹ ∈ jH d C') ?_ ?_ ?_ ?_ hσ
  · show q * 1 * q⁻¹ ∈ jH d C'
    rw [mul_one, mul_inv_cancel]
    exact (jH d C').one_mem
  · intro x hx y hy
    show q * jL x y * q⁻¹ ∈ jH d C'
    by_cases hxy : x = y
    · subst hxy
      rw [jL_self, mul_one, mul_inv_cancel]
      exact (jH d C').one_mem
    · obtain ⟨x', hx', hmx⟩ := hq x hx
      obtain ⟨y', hy', hmy⟩ := hq y hy
      rw [rcl hd q (hC x hx y hy hxy) (hC y hy x hx (Ne.symm hxy)) hmx hmy]
      exact jL_mem_jH hx' hy'
  · intro a b ha hb
    show q * (a * b) * q⁻¹ ∈ jH d C'
    have e : q * (a * b) * q⁻¹ = (q * a * q⁻¹) * (q * b * q⁻¹) := by group
    rw [e]
    exact (jH d C').mul_mem ha hb
  · intro a ha
    show q * a⁻¹ * q⁻¹ ∈ jH d C'
    have e : q * a⁻¹ * q⁻¹ = (q * a * q⁻¹)⁻¹ := by group
    rw [e]
    exact (jH d C').inv_mem ha

#audit_axioms GroupApproximation.BooneHigman.Join.rcl_H

theorem jH_mono {C C' : Finset (List (Fin d))} (h : C ⊆ C') : jH d C ≤ jH d C' := by
  intro σ hσ
  refine jH_induction (P := fun s => s ∈ jH d C') (jH d C').one_mem ?_
    (fun a b => (jH d C').mul_mem) (fun a => (jH d C').inv_mem) hσ
  intro x hx y hy
  exact jL_mem_jH (h hx) (h hy)

#audit_axioms GroupApproximation.BooneHigman.Join.jH_mono

/-- The prefix endomorphism `(x, y) ↦ (c x, c y)` of the quotient. -/
noncomputable def jPhi (d : ℕ) (c : List (Fin d)) : higmanVCCommon_Q d →* higmanVCCommon_Q d :=
  QuotientGroup.lift (Subgroup.normalClosure (higmanVC_rels d fun _ => True))
    ((higmanVCCommon_mk d).comp (higSw_lift c))
    (Subgroup.normalClosure_le_normal (by
      intro t ht
      exact MonoidHom.mem_ker.mpr (higmanVCCommon_mk_rel (higSw_lift_rels c ht))))

#audit_axioms GroupApproximation.BooneHigman.Join.jPhi

theorem jPhi_mk (c : List (Fin d)) (g : FreeGroup (List (Fin d) × List (Fin d))) :
    jPhi d c (higmanVCCommon_mk d g) = higmanVCCommon_mk d (higSw_lift c g) :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Join.jPhi_mk

theorem jPhi_jL (c x y : List (Fin d)) : jPhi d c (jL x y) = jL (c ++ x) (c ++ y) := by
  unfold jL
  rw [jPhi_mk, higSw_lift_of]

#audit_axioms GroupApproximation.BooneHigman.Join.jPhi_jL

theorem jPhi_append (c c' : List (Fin d)) (q : higmanVCCommon_Q d) :
    jPhi d c (jPhi d c' q) = jPhi d (c ++ c') q := by
  obtain ⟨g, rfl⟩ := mk_surj q
  rw [jPhi_mk, jPhi_mk, jPhi_mk]
  have e : (higSw_lift c).comp (higSw_lift c') = higSw_lift (c ++ c') := by
    refine FreeGroup.ext_hom _ _ fun p => ?_
    obtain ⟨x, y⟩ := p
    show higSw_lift c (higSw_lift c' (FreeGroup.of (x, y))) =
      higSw_lift (c ++ c') (FreeGroup.of (x, y))
    simp only [higSw_lift_of, List.append_assoc]
  exact congrArg (higmanVCCommon_mk d) (DFunLike.congr_fun e g)

#audit_axioms GroupApproximation.BooneHigman.Join.jPhi_append

theorem jperm_jPhi (c : List (Fin d)) (q : higmanVCCommon_Q d) :
    jperm d (jPhi d c q) = localize c (jperm d q) := by
  obtain ⟨g, rfl⟩ := mk_surj q
  rw [jPhi_mk, jperm_mk, jperm_mk]
  exact higSw_perm_lift c g

#audit_axioms GroupApproximation.BooneHigman.Join.jperm_jPhi

theorem perm_apply_inv_self {α : Type*} (f : Equiv.Perm α) (x : α) : f (f⁻¹ x) = x :=
  f.apply_symm_apply x

#audit_axioms GroupApproximation.BooneHigman.Join.perm_apply_inv_self

theorem perm_inv_apply_self {α : Type*} (f : Equiv.Perm α) (x : α) : f⁻¹ (f x) = x :=
  f.symm_apply_apply x

#audit_axioms GroupApproximation.BooneHigman.Join.perm_inv_apply_self

theorem jPhi_nil' (q : higmanVCCommon_Q d) : jPhi d [] q = q := by
  obtain ⟨g, rfl⟩ := mk_surj q
  induction g using FreeGroup.induction_on with
  | C1 => rw [map_one, map_one]
  | of p =>
    obtain ⟨x, y⟩ := p
    exact jPhi_jL [] x y
  | inv_of p ih => rw [map_inv, map_inv, ih]
  | mul a b iha ihb => rw [map_mul, map_mul, iha, ihb]

#audit_axioms GroupApproximation.BooneHigman.Join.jPhi_nil'

/-- **Rigid conjugation of a prefix image.** -/
theorem rcl_phi (hd : 1 < d) (q : higmanVCCommon_Q d) {c c' : List (Fin d)}
    (hc : MapsCone (jperm d q) c c') (r : higmanVCCommon_Q d) :
    q * jPhi d c r * q⁻¹ = jPhi d c' r := by
  have key : ((MulAut.conj q).toMonoidHom.comp (jPhi d c)).comp (higmanVCCommon_mk d) =
      (jPhi d c').comp (higmanVCCommon_mk d) := by
    refine FreeGroup.ext_hom _ _ fun p => ?_
    obtain ⟨x, y⟩ := p
    show q * jPhi d c (jL x y) * q⁻¹ = jPhi d c' (jL x y)
    rw [jPhi_jL, jPhi_jL]
    by_cases h : ¬ x <+: y ∧ ¬ y <+: x
    · exact rcl hd q ((higSw_incomp_iff c x y).mpr h).1 ((higSw_incomp_iff c x y).mpr h).2
        (hc.append x) (hc.append y)
    · rw [jL_comparable (fun h' => h ((higSw_incomp_iff c x y).mp h')),
        jL_comparable (fun h' => h ((higSw_incomp_iff c' x y).mp h')), mul_one, mul_inv_cancel]
  obtain ⟨g, rfl⟩ := mk_surj r
  exact DFunLike.congr_fun key g

#audit_axioms GroupApproximation.BooneHigman.Join.rcl_phi

/-- The prefix image of an antichain subgroup. -/
theorem jPhi_mem_jH (c : List (Fin d)) {C : Finset (List (Fin d))} {σ : higmanVCCommon_Q d}
    (hσ : σ ∈ jH d C) : jPhi d c σ ∈ jH d (C.image (c ++ ·)) := by
  refine jH_induction (P := fun s => jPhi d c s ∈ jH d (C.image (c ++ ·))) ?_ ?_ ?_ ?_ hσ
  · show jPhi d c 1 ∈ jH d (C.image (c ++ ·))
    rw [map_one]
    exact Subgroup.one_mem _
  · intro x hx y hy
    show jPhi d c (jL x y) ∈ jH d (C.image (c ++ ·))
    rw [jPhi_jL]
    exact jL_mem_jH (Finset.mem_image_of_mem (c ++ ·) hx) (Finset.mem_image_of_mem (c ++ ·) hy)
  · intro a b ha hb
    show jPhi d c (a * b) ∈ jH d (C.image (c ++ ·))
    rw [map_mul]
    exact Subgroup.mul_mem _ ha hb
  · intro a ha
    show jPhi d c a⁻¹ ∈ jH d (C.image (c ++ ·))
    rw [map_inv]
    exact Subgroup.inv_mem _ ha

#audit_axioms GroupApproximation.BooneHigman.Join.jPhi_mem_jH

end GroupApproximation.BooneHigman.Join
