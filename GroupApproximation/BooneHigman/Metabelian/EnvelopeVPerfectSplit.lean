import GroupApproximation.BooneHigman.Metabelian.EnvelopeVPerfectChain
import GroupApproximation.BooneHigman.Metabelian.EnvelopeGenTorsionNakayama
import GroupApproximation.Meta.AxiomGuard

/-!
# A cone swap is the product of its children

Route to `GenTorsionVPerfectStatement`, step 2.

* `vPerfectChain_maps`, `vPerfectChain_eq_coneSwap`: over a duplicate-free list of all letters,
  the chain of child swaps is `s(v, w)` itself.
* `vPerfectCls`: the class of a cone swap in the abelianization of `V`. It has square `1`
  (`vPerfectCls_sq`). For pairwise incomparable `a, b, c`, conjugating by `s(a, b)` gives
  `cls(b, c) = cls(a, c)` (`vPerfectCls_move`). Also `cls(a, b) = cls(b, a)` (`vPerfectCls_symm`).
* `vPerfect_child_eq`: all children of `s(v, w)` have one class, so the chain over `L` has class
  `cls ^ L.length` (`vPerfectChain_cls`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

variable {X : Type*} [Finite X] {v w : List X}

/-- Over a duplicate-free list, the chain carries `cone (v ++ [y])` onto `cone (w ++ [y])` and
back, for every `y` in the list. -/
theorem vPerfectChain_maps (hvw : ¬ v <+: w) (hwv : ¬ w <+: v) : ∀ (L : List X), L.Nodup →
    ∀ y ∈ L, MapsCone (vPerfectChain hvw hwv L : Equiv.Perm (Cantor X)) (v ++ [y]) (w ++ [y]) ∧
      MapsCone (vPerfectChain hvw hwv L : Equiv.Perm (Cantor X)) (w ++ [y]) (v ++ [y])
  | [], _, _, hy => absurd hy List.not_mem_nil
  | y0 :: L, hnd, y, hy => by
    obtain ⟨hy0L, hndL⟩ := List.nodup_cons.mp hnd
    rw [vPerfectChain_cons_coe]
    rcases List.mem_cons.mp hy with h | hyL
    · subst h
      exact ⟨(vPerfectChain_fix_left hvw hwv hy0L).comp (mapsCone_coneSwap_left _ _),
        (vPerfectChain_fix_right hvw hwv hy0L).comp (mapsCone_coneSwap_right _ _)⟩
    · have hne : y ≠ y0 := fun h => hy0L (by rw [← h]; exact hyL)
      have ih := vPerfectChain_maps hvw hwv L hndL y hyL
      exact ⟨ih.1.comp (vgen_mapsCone_coneSwap_fix (vPerfect_inc_cross hvw hwv y0 y0)
          (vPerfect_inc_cross hwv hvw y0 y0) (vPerfect_inc_cross hwv hvw y y0)
          (vPerfect_inc_cross hvw hwv y0 y) (vPerfect_inc_letter w hne)
          (vPerfect_inc_letter w (Ne.symm hne))),
        ih.2.comp (vgen_mapsCone_coneSwap_fix (vPerfect_inc_cross hvw hwv y0 y0)
          (vPerfect_inc_cross hwv hvw y0 y0) (vPerfect_inc_letter v hne)
          (vPerfect_inc_letter v (Ne.symm hne)) (vPerfect_inc_cross hvw hwv y y0)
          (vPerfect_inc_cross hwv hvw y0 y))⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.vPerfectChain_maps

/-- Over a duplicate-free list of all letters, the chain of children is `s(v, w)`. -/
theorem vPerfectChain_eq_coneSwap (hvw : ¬ v <+: w) (hwv : ¬ w <+: v) (L : List X)
    (hnd : L.Nodup) (hall : ∀ y, y ∈ L) :
    (vPerfectChain hvw hwv L : Equiv.Perm (Cantor X)) = coneSwap v w hvw hwv := by
  refine Equiv.ext fun x => ?_
  rw [coneSwap_apply]
  by_cases hv : IsStreamPrefix v x
  · obtain ⟨z, rfl⟩ := mem_cone_iff.mp hv
    obtain ⟨y, z', rfl⟩ : ∃ (y : X) (z' : Cantor X), z = prepend [y] z' :=
      ⟨z 0, dropN 1 z, (vPerfect_prepend_head z).symm⟩
    rw [coneSwapFun_prepend_left, ← prepend_append v, ← prepend_append w]
    exact (vPerfectChain_maps hvw hwv L hnd y (hall y)).1 z'
  · by_cases hw : IsStreamPrefix w x
    · obtain ⟨z, rfl⟩ := mem_cone_iff.mp hw
      obtain ⟨y, z', rfl⟩ : ∃ (y : X) (z' : Cantor X), z = prepend [y] z' :=
        ⟨z 0, dropN 1 z, (vPerfect_prepend_head z).symm⟩
      rw [coneSwapFun_prepend_right hvw hwv, ← prepend_append w, ← prepend_append v]
      exact (vPerfectChain_maps hvw hwv L hnd y (hall y)).2 z'
    · rw [coneSwapFun_of_not hv hw]
      exact vPerfectChain_fix hvw hwv L x fun y _ =>
        ⟨fun h => hv (IsStreamPrefix.of_prefix (List.prefix_append v [y]) h),
          fun h => hw (IsStreamPrefix.of_prefix (List.prefix_append w [y]) h)⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.vPerfectChain_eq_coneSwap

/-- The class of the cone swap `s(a, b)` in the abelianization of `V`. -/
noncomputable def vPerfectCls {a b : List X} (h1 : ¬ a <+: b) (h2 : ¬ b <+: a) :
    Abelianization ↥(higmanThompsonV X) :=
  (Abelianization.of : ↥(higmanThompsonV X) →* Abelianization ↥(higmanThompsonV X))
    ⟨coneSwap a b h1 h2, coneSwap_mem_higmanThompsonV h1 h2⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.vPerfectCls

theorem vPerfectCls_sq {a b : List X} (h1 : ¬ a <+: b) (h2 : ¬ b <+: a) :
    vPerfectCls h1 h2 ^ 2 = 1 := by
  have e : (⟨coneSwap a b h1 h2, coneSwap_mem_higmanThompsonV h1 h2⟩ : ↥(higmanThompsonV X)) *
      ⟨coneSwap a b h1 h2, coneSwap_mem_higmanThompsonV h1 h2⟩ = 1 :=
    Subtype.ext (coneSwap_mul_self h1 h2)
  rw [pow_two, vPerfectCls, ← map_mul, e, map_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.vPerfectCls_sq

/-- For pairwise incomparable `a, b, c`, conjugation by `s(a, b)` carries `s(b, c)` to
`s(a, c)`. -/
theorem vPerfectCls_move {a b c : List X} (hab : ¬ a <+: b) (hba : ¬ b <+: a)
    (hac : ¬ a <+: c) (hca : ¬ c <+: a) (hbc : ¬ b <+: c) (hcb : ¬ c <+: b) :
    vPerfectCls hbc hcb = vPerfectCls hac hca :=
  gentorsion_class_eq_of_conj (coneSwap_mem_higmanThompsonV hab hba)
    (coneSwap_mem_higmanThompsonV hbc hcb) (coneSwap_mem_higmanThompsonV hac hca)
    (vgen_conj_coneSwap hac hca hbc hcb (mapsCone_coneSwap_right hab hba)
      (vgen_mapsCone_coneSwap_fix hab hba hca hac hcb hbc))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.vPerfectCls_move

theorem vPerfectCls_symm {a b : List X} (hab : ¬ a <+: b) (hba : ¬ b <+: a) :
    vPerfectCls hab hba = vPerfectCls hba hab :=
  gentorsion_class_eq_of_conj (coneSwap_mem_higmanThompsonV hab hba)
    (coneSwap_mem_higmanThompsonV hab hba) (coneSwap_mem_higmanThompsonV hba hab)
    (vgen_conj_coneSwap hba hab hab hba (mapsCone_coneSwap_left hab hba)
      (mapsCone_coneSwap_right hab hba))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.vPerfectCls_symm

end GroupApproximation.BooneHigman.Metabelian.Envelope
