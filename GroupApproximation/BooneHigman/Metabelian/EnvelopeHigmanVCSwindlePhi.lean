import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCSwindleHom
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTreeNFConverse
import GroupApproximation.Meta.AxiomGuard

/-!
# Prefix endomorphisms of the all-swaps quotient (lane bh-hig-02)

Since the prefix lift `higSw_lift c` carries the standard relators into themselves, it descends
to an endomorphism `higSw_phi d c` of `Q = higmanVCCommon_Q d`, sending the generator
`(x, y)` to `(c x, c y)` (`higSw_phi_gen`).  These compose by concatenation
(`higSw_phi_append`), `higSw_phi d []` is the identity (`higSw_phi_nil`), and on `V_d` the
endomorphism `higSw_phi d c` is the localization to the cone of `c` (`higSw_E_phi`).  In
particular `higSw_phi d c` maps the kernel `Z = ker Ē` into itself (`higSw_phi_ker`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- The normal closure of the standard relators is killed by the lifted quotient map. -/
theorem higSw_normalClosure_le {d : ℕ} (c : List (Fin d)) :
    Subgroup.normalClosure (higmanVC_rels d fun _ => True) ≤
      ((higmanVCCommon_mk d).comp (higSw_lift c)).ker := by
  refine Subgroup.normalClosure_le_normal ?_
  intro t ht
  exact MonoidHom.mem_ker.mpr (higmanVCCommon_mk_rel (higSw_lift_rels c ht))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higSw_normalClosure_le

/-- **The prefix endomorphism** `φ_c` of `Q`, induced by `(x, y) ↦ (c x, c y)`. -/
noncomputable def higSw_phi (d : ℕ) (c : List (Fin d)) :
    higmanVCCommon_Q d →* higmanVCCommon_Q d :=
  QuotientGroup.lift (Subgroup.normalClosure (higmanVC_rels d fun _ => True))
    ((higmanVCCommon_mk d).comp (higSw_lift c)) (higSw_normalClosure_le c)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higSw_phi

/-- `φ_c` on the class of a word. -/
theorem higSw_phi_mk {d : ℕ} (c : List (Fin d)) (g : FreeGroup (List (Fin d) × List (Fin d))) :
    higSw_phi d c (higmanVCCommon_mk d g) = higmanVCCommon_mk d (higSw_lift c g) :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higSw_phi_mk

/-- `φ_c` on a generator: `(x, y) ↦ (c x, c y)`. -/
theorem higSw_phi_gen {d : ℕ} (c x y : List (Fin d)) :
    higSw_phi d c (higmanVCCommon_mk d (FreeGroup.of (x, y))) =
      higmanVCCommon_mk d (FreeGroup.of (c ++ x, c ++ y)) := by
  rw [higSw_phi_mk, higSw_lift_of]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higSw_phi_gen

/-- Prefix lifts compose by concatenation. -/
theorem higSw_lift_append {d : ℕ} (c c' : List (Fin d)) :
    (higSw_lift c).comp (higSw_lift c') = higSw_lift (c ++ c') := by
  refine FreeGroup.ext_hom _ _ fun p => ?_
  obtain ⟨x, y⟩ := p
  show higSw_lift c (higSw_lift c' (FreeGroup.of (x, y))) =
    higSw_lift (c ++ c') (FreeGroup.of (x, y))
  simp only [higSw_lift_of, List.append_assoc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higSw_lift_append

/-- The empty prefix lift is the identity. -/
theorem higSw_lift_nil (d : ℕ) : higSw_lift ([] : List (Fin d)) = MonoidHom.id _ := by
  refine FreeGroup.ext_hom _ _ fun p => ?_
  obtain ⟨x, y⟩ := p
  rw [higSw_lift_of, MonoidHom.id_apply, List.nil_append, List.nil_append]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higSw_lift_nil

/-- **Composition.**  `φ_c ∘ φ_{c'} = φ_{c c'}`. -/
theorem higSw_phi_append {d : ℕ} (c c' : List (Fin d)) (q : higmanVCCommon_Q d) :
    higSw_phi d c (higSw_phi d c' q) = higSw_phi d (c ++ c') q := by
  obtain ⟨g, rfl⟩ := higmanVCTreeNF_mk_surjective d q
  simp only [higSw_phi_mk]
  exact congrArg (higmanVCCommon_mk d) (DFunLike.congr_fun (higSw_lift_append c c') g)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higSw_phi_append

/-- `φ_[]` is the identity. -/
theorem higSw_phi_nil {d : ℕ} (q : higmanVCCommon_Q d) : higSw_phi d [] q = q := by
  obtain ⟨g, rfl⟩ := higmanVCTreeNF_mk_surjective d q
  rw [higSw_phi_mk, higSw_lift_nil, MonoidHom.id_apply]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higSw_phi_nil

/-- **Localization.**  On the boundary, `Ē ∘ φ_c` is `Ē` localized to the cone of `c`. -/
theorem higSw_E_phi {d : ℕ} (c : List (Fin d)) (q : higmanVCCommon_Q d) :
    ((higmanVCTreeNF_E d (higSw_phi d c q) : ↥(higmanThompsonV (Fin d))) :
        Equiv.Perm (Cantor (Fin d))) =
      localize c ((higmanVCTreeNF_E d q : ↥(higmanThompsonV (Fin d))) :
        Equiv.Perm (Cantor (Fin d))) := by
  obtain ⟨g, rfl⟩ := higmanVCTreeNF_mk_surjective d q
  exact higSw_perm_lift c g

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higSw_E_phi

/-- **`φ_c` preserves `Z = ker Ē`.** -/
theorem higSw_phi_ker {d : ℕ} (c : List (Fin d)) {z : higmanVCCommon_Q d}
    (hz : z ∈ (higmanVCTreeNF_E d).ker) : higSw_phi d c z ∈ (higmanVCTreeNF_E d).ker := by
  refine MonoidHom.mem_ker.mpr (Subtype.ext ?_)
  rw [higSw_E_phi, MonoidHom.mem_ker.mp hz]
  exact map_one (localize c)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higSw_phi_ker

end GroupApproximation.BooneHigman.Metabelian.Envelope
