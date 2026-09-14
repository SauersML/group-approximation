import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerPhiMapTransportPerm
import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedBridgeDoublingRun
import GroupApproximation.Meta.AxiomGuard

/-!
# The rotation of a restriction after inserting an edge

Osin, arXiv:math/0411039v3, Appendix, the assumption before Lemma 9.3: "inside every 2-gon of
`Φ′_M`, there is a vertex of `Φ_M`".

A face-edge doubling is an edge insertion `EdgeInsertion.toCombMap M a b` at the corners `a = w_j`
and `b = σ (α a)`: the new dart `some none` sits before `a` in the rotation, and `none` before `b`.
The collapsed map of a region family is a restriction of the diagram to a set of darts closed under
reversal.  This module computes the rotation of the restriction after the insertion, for a retained
set holding `a`, `α a` and `b`.
* When the new darts are retained, the new rotation follows the old one, except that it turns to
  `some none` where the old one turned to `a`, and to `none` from `α a`.
* When the new darts are not retained, the new rotation follows the old one.

* `PhiMapTransport.restriction_sigma_val_of_run`: a first run to a retained dart is the rotation of
  the restriction.
* `PhiMapTransport.sigma_val_of_retained`, `sigma_val_symm_of_retained`, `sigma_val_some_none`,
  `sigma_val_none`, `sigma_val_of_deleted`: the new rotation.
* `PhiMapTransport.facePerm_val_of_retained`, `facePerm_val_some_none`, `facePerm_val_self`,
  `facePerm_val_of_deleted`: the new face rotation.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`), through Osin's Lemma 9.7(a);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.PhiMapTransport

open Equiv EdgeInsertion

universe u

section Restriction

variable {N : CombMap.{u}} {keep : N.Dart → Prop} (hkeep : ∀ d, keep (N.alpha d) ↔ keep d)

/-- **A first run to a retained dart is the rotation of the restriction.** -/
theorem restriction_sigma_val_of_run {x y : N.Dart} (hx : keep x) (hy : keep y) {m : ℕ}
    (hm : 0 < m) (hrun : (N.sigma ^ m) x = y)
    (hskip : ∀ k, 0 < k → k < m → ¬ keep ((N.sigma ^ k) x)) :
    ((CombMap.PredicateRestriction.toCombMap N keep hkeep).sigma ⟨x, hx⟩).1 = y := by
  have h : (CombMap.PredicateRestriction.toCombMap N keep hkeep).sigma ⟨x, hx⟩ = ⟨y, hy⟩ :=
    PermFirstReturn.apply_eq_of_isFirstReturn
      (CombMap.PredicateRestriction.sigma_firstReturn N keep) hm hrun fun k hk hkm hmem => by
        obtain ⟨z, hz⟩ := hmem
        have hz' : (N.sigma ^ k) x = z.1 := hz.symm
        apply hskip k hk hkm
        rw [hz']
        exact z.2
  rw [h]

end Restriction

section Insert

variable {M : CombMap.{u}} {a b : M.Dart} {keep : M.Dart → Prop}
  (hkeep : ∀ d, keep (M.alpha d) ↔ keep d) {keep' : (toCombMap M a b).Dart → Prop}
  (hkeep' : ∀ d, keep' ((toCombMap M a b).alpha d) ↔ keep' d)
  (hembed : ∀ z, keep' (embed M z) ↔ keep z)

/-- The old rotation from `σ⁻¹ b` reaches `b` in one step. -/
theorem sigma_val_symm (hb : keep (M.sigma.symm b)) (hbk : keep b) :
    ((CombMap.PredicateRestriction.toCombMap M keep hkeep).sigma ⟨M.sigma.symm b, hb⟩).1 = b :=
  restriction_sigma_val_of_run hkeep hb hbk Nat.one_pos
    (by rw [pow_one, Equiv.apply_symm_apply]) fun k hk hk1 => absurd hk1 (by omega)

open scoped Classical in
/-- **The new rotation at an old dart, when the new darts are retained.** -/
theorem sigma_val_of_retained (hab : a ≠ b) (ha : keep a) (hb : keep (M.sigma.symm b))
    (hsn : keep' (some none)) {z : M.Dart} (hz : keep z) (hzb : z ≠ M.sigma.symm b) :
    ((CombMap.PredicateRestriction.toCombMap (toCombMap M a b) keep' hkeep').sigma
        ⟨embed M z, (hembed z).mpr hz⟩).1 =
      if ((CombMap.PredicateRestriction.toCombMap M keep hkeep).sigma ⟨z, hz⟩).1 = a then
        some none
      else embed M ((CombMap.PredicateRestriction.toCombMap M keep hkeep).sigma ⟨z, hz⟩).1 := by
  obtain ⟨m, hm, hrun, hskip⟩ := CombMap.PredicateRestriction.sigma_firstReturn M keep ⟨z, hz⟩
  have hrun' : (M.sigma ^ m) z =
      ((CombMap.PredicateRestriction.toCombMap M keep hkeep).sigma ⟨z, hz⟩).1 := hrun
  obtain ⟨k', hk', hlift, hskip'⟩ := EnclosedBridgeDoubling.firstKept_lift hab hembed ha hb hzb hm
    (fun t ht htm hkt => hskip t ht htm ⟨⟨_, hkt⟩, rfl⟩)
  rw [hrun'] at hlift
  by_cases h : ((CombMap.PredicateRestriction.toCombMap M keep hkeep).sigma ⟨z, hz⟩).1 = a
  · rw [if_pos h] at hlift ⊢
    exact restriction_sigma_val_of_run hkeep' _ hsn hk' hlift hskip'
  · rw [if_neg h] at hlift ⊢
    exact restriction_sigma_val_of_run hkeep' _
      ((hembed _).mpr ((CombMap.PredicateRestriction.toCombMap M keep hkeep).sigma ⟨z, hz⟩).2)
      hk' hlift hskip'

/-- **The new rotation at `σ⁻¹ b`, when `none` is retained.** -/
theorem sigma_val_symm_of_retained (hab : a ≠ b) (hb : keep (M.sigma.symm b)) (hn : keep' none) :
    ((CombMap.PredicateRestriction.toCombMap (toCombMap M a b) keep' hkeep').sigma
        ⟨embed M (M.sigma.symm b), (hembed _).mpr hb⟩).1 = none := by
  classical
  refine restriction_sigma_val_of_run hkeep' _ hn Nat.one_pos ?_ fun k hk hk1 =>
    absurd hk1 (by omega)
  rw [pow_one]
  exact (EnclosedBridgeDoubling.sigma_eq_none_iff hab _).mpr rfl

include hembed in
/-- **The new rotation at `some none`.** -/
theorem sigma_val_some_none (hab : a ≠ b) (ha : keep a) (hsn : keep' (some none)) :
    ((CombMap.PredicateRestriction.toCombMap (toCombMap M a b) keep' hkeep').sigma
        ⟨some none, hsn⟩).1 = embed M a := by
  refine restriction_sigma_val_of_run hkeep' _ ((hembed a).mpr ha) Nat.one_pos ?_ fun k hk hk1 =>
    absurd hk1 (by omega)
  rw [pow_one]
  exact GeodesicCollar.edgeInsertion_sigma_some_none hab

include hembed in
/-- **The new rotation at `none`.** -/
theorem sigma_val_none (hbk : keep b) (hn : keep' none) :
    ((CombMap.PredicateRestriction.toCombMap (toCombMap M a b) keep' hkeep').sigma
        ⟨none, hn⟩).1 = embed M b := by
  refine restriction_sigma_val_of_run hkeep' _ ((hembed b).mpr hbk) Nat.one_pos ?_ fun k hk hk1 =>
    absurd hk1 (by omega)
  rw [pow_one]
  exact EdgeInsertion.sigma_none_apply a b

/-- **The new rotation at an old dart, when the new darts are not retained.** -/
theorem sigma_val_of_deleted (hab : a ≠ b) (ha : keep a) (hb : keep (M.sigma.symm b))
    (hbk : keep b) (hsn : ¬ keep' (some none)) (hn : ¬ keep' none) {z : M.Dart} (hz : keep z) :
    ((CombMap.PredicateRestriction.toCombMap (toCombMap M a b) keep' hkeep').sigma
        ⟨embed M z, (hembed z).mpr hz⟩).1 =
      embed M ((CombMap.PredicateRestriction.toCombMap M keep hkeep).sigma ⟨z, hz⟩).1 := by
  classical
  by_cases hzb : z = M.sigma.symm b
  · subst hzb
    rw [sigma_val_symm hkeep hz hbk]
    refine restriction_sigma_val_of_run hkeep' _ ((hembed b).mpr hbk) (m := 1 + 1) (by omega)
      ?_ ?_
    · rw [pow_succ', Perm.mul_apply, pow_one,
        (EnclosedBridgeDoubling.sigma_eq_none_iff hab _).mpr rfl]
      exact EdgeInsertion.sigma_none_apply a b
    · intro k hk hk2
      obtain rfl : k = 1 := by omega
      rw [pow_one, (EnclosedBridgeDoubling.sigma_eq_none_iff hab _).mpr rfl]
      exact hn
  · obtain ⟨m, hm, hrun, hskip⟩ := CombMap.PredicateRestriction.sigma_firstReturn M keep ⟨z, hz⟩
    have hrun' : (M.sigma ^ m) z =
        ((CombMap.PredicateRestriction.toCombMap M keep hkeep).sigma ⟨z, hz⟩).1 := hrun
    obtain ⟨k', hk', hlift, hskip'⟩ :=
      EnclosedBridgeDoubling.firstKept_lift hab hembed ha hb hzb hm
        (fun t ht htm hkt => hskip t ht htm ⟨⟨_, hkt⟩, rfl⟩)
    rw [hrun'] at hlift
    by_cases h : ((CombMap.PredicateRestriction.toCombMap M keep hkeep).sigma ⟨z, hz⟩).1 = a
    · rw [if_pos h] at hlift
      rw [h]
      refine restriction_sigma_val_of_run hkeep' _ ((hembed a).mpr ha) (m := k' + 1) (by omega)
        ?_ ?_
      · rw [pow_succ', Perm.mul_apply, hlift]
        exact GeodesicCollar.edgeInsertion_sigma_some_none hab
      · intro t ht htk
        rcases Nat.lt_or_ge t k' with htk' | htk'
        · exact hskip' t ht htk'
        · obtain rfl : t = k' := by omega
          rw [hlift]
          exact hsn
    · rw [if_neg h] at hlift
      exact restriction_sigma_val_of_run hkeep' _
        ((hembed _).mpr ((CombMap.PredicateRestriction.toCombMap M keep hkeep).sigma ⟨z, hz⟩).2)
        hk' hlift hskip'

/-! ## The face rotation -/

/-- **The old face rotation at the doubled dart** is the next corner. -/
theorem facePerm_val_self (ha : keep a) (hba : M.sigma (M.alpha a) = b) (hbk : keep b) :
    ((CombMap.PredicateRestriction.toCombMap M keep hkeep).facePerm ⟨a, ha⟩).1 = b :=
  restriction_sigma_val_of_run hkeep ((hkeep a).mpr ha) hbk Nat.one_pos
    (by rw [pow_one]; exact hba) fun k hk hk1 => absurd hk1 (by omega)

open scoped Classical in
/-- **The new face rotation at an old dart other than `a`, when the new darts are retained.** -/
theorem facePerm_val_of_retained (hab : a ≠ b) (ha : keep a) (hba : M.sigma (M.alpha a) = b)
    (hsn : keep' (some none)) {z : M.Dart} (hz : keep z) (hza : z ≠ a) :
    ((CombMap.PredicateRestriction.toCombMap (toCombMap M a b) keep' hkeep').facePerm
        ⟨embed M z, (hembed z).mpr hz⟩).1 =
      if ((CombMap.PredicateRestriction.toCombMap M keep hkeep).facePerm ⟨z, hz⟩).1 = a then
        some none
      else embed M ((CombMap.PredicateRestriction.toCombMap M keep hkeep).facePerm ⟨z, hz⟩).1 := by
  have hαb : M.sigma.symm b = M.alpha a := (Equiv.symm_apply_eq M.sigma).mpr hba.symm
  have hb : keep (M.sigma.symm b) := by rw [hαb]; exact (hkeep a).mpr ha
  exact sigma_val_of_retained hkeep hkeep' hembed hab ha hb hsn ((hkeep z).mpr hz)
    fun h => hza (M.alpha.injective (h.trans hαb))

include hembed in
/-- **The new face rotation at `some none`**, when `none` is retained. -/
theorem facePerm_val_some_none (hbk : keep b) (hsn : keep' (some none)) (hn : keep' none) :
    ((CombMap.PredicateRestriction.toCombMap (toCombMap M a b) keep' hkeep').facePerm
        ⟨some none, hsn⟩).1 = embed M b :=
  sigma_val_none hkeep' hembed hbk hn

/-- **The new face rotation at an old dart, when the new darts are not retained.** -/
theorem facePerm_val_of_deleted (hab : a ≠ b) (ha : keep a) (hba : M.sigma (M.alpha a) = b)
    (hbk : keep b) (hsn : ¬ keep' (some none)) (hn : ¬ keep' none) {z : M.Dart} (hz : keep z) :
    ((CombMap.PredicateRestriction.toCombMap (toCombMap M a b) keep' hkeep').facePerm
        ⟨embed M z, (hembed z).mpr hz⟩).1 =
      embed M ((CombMap.PredicateRestriction.toCombMap M keep hkeep).facePerm ⟨z, hz⟩).1 := by
  have hαb : M.sigma.symm b = M.alpha a := (Equiv.symm_apply_eq M.sigma).mpr hba.symm
  have hb : keep (M.sigma.symm b) := by rw [hαb]; exact (hkeep a).mpr ha
  exact sigma_val_of_deleted hkeep hkeep' hembed hab ha hb hbk hsn hn ((hkeep z).mpr hz)

end Insert

end GroupApproximation.GGT.VanKampen.PhiMapTransport

#audit_axioms GroupApproximation.GGT.VanKampen.PhiMapTransport.restriction_sigma_val_of_run
#audit_axioms GroupApproximation.GGT.VanKampen.PhiMapTransport.sigma_val_of_retained
#audit_axioms GroupApproximation.GGT.VanKampen.PhiMapTransport.sigma_val_of_deleted
#audit_axioms GroupApproximation.GGT.VanKampen.PhiMapTransport.facePerm_val_of_retained
#audit_axioms GroupApproximation.GGT.VanKampen.PhiMapTransport.facePerm_val_of_deleted
