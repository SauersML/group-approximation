import GroupApproximation.BooneHigman.Metabelian.EnvelopeRelatorsCoreCones
import GroupApproximation.Meta.AxiomGuard

/-!
# Finite core relators: conjugated local copies in the quotient

Fix a normal subgroup `N` of `RNFree X H` containing every commutation relator
`nfCommRelators H x₀`.  In `RNFree X H ⧸ N` the conjugate `rfConjL H N e` of the local copy of
`H` depends only on the cone `w` that `e` carries `cone [x₀]` onto (`rcore_rfConjL_congr`).
* `rcore_disj_subset` (**step 3**): if the disjoint-cone relators hold for the two pairs
  `(e₁, [x₁])` and `(e₂, [x₁, x₁])`, they hold for all pairs.  Transport along an element of
  `V_X` fixing `cone [x₀]` (`rcore_exists_stab_mapsCone`).
* `rcore_commute_rfConjL_incomp`: once all disjoint-cone relators hold, local copies on
  incomparable cones commute.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

open Trees

noncomputable section

variable {X : Type*} [Finite X]

theorem rcore_rfConjL_eq (H : Subgroup (TreeAut X)) (N : Subgroup (RNFree X H)) [N.Normal]
    (e : ↥(higmanThompsonV X)) (k : ↥H) :
    rfConjL H N e k = rfV H N e * rfL H N k * (rfV H N e)⁻¹ := by
  rw [rfConjL_apply, rfL_apply, rfV_apply, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
    QuotientGroup.mk_inv]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rcore_rfConjL_eq

theorem rcore_conj_rfConjL (H : Subgroup (TreeAut X)) (N : Subgroup (RNFree X H)) [N.Normal]
    (g e : ↥(higmanThompsonV X)) (k : ↥H) :
    rfV H N g * rfConjL H N e k * (rfV H N g)⁻¹ = rfConjL H N (g * e) k := by
  rw [rcore_rfConjL_eq, rcore_rfConjL_eq, map_mul, mul_inv_rev]
  simp only [mul_assoc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rcore_conj_rfConjL

/-- The local copy commutes with every element of `V_X` fixing `cone [x₀]`. -/
theorem rcore_rfL_commute_fix (H : Subgroup (TreeAut X)) (N : Subgroup (RNFree X H))
    [N.Normal] (x₀ : X) (hcomm : nfCommRelators H x₀ ⊆ N) (f : ↥(higmanThompsonV X))
    (hf : MapsCone (f : Equiv.Perm (Cantor X)) [x₀] [x₀]) (k : ↥H) :
    Commute (rfL H N k) (rfV H N f) := by
  have h := rf_commute_of_mem (N := N) (hcomm ⟨k, f, hf, rfl⟩)
  exact h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rcore_rfL_commute_fix

theorem rcore_conj_rfL_fix (H : Subgroup (TreeAut X)) (N : Subgroup (RNFree X H)) [N.Normal]
    (x₀ : X) (hcomm : nfCommRelators H x₀ ⊆ N) (f : ↥(higmanThompsonV X))
    (hf : MapsCone (f : Equiv.Perm (Cantor X)) [x₀] [x₀]) (k : ↥H) :
    rfV H N f * rfL H N k * (rfV H N f)⁻¹ = rfL H N k := by
  rw [← (rcore_rfL_commute_fix H N x₀ hcomm f hf k).eq, mul_inv_cancel_right]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rcore_conj_rfL_fix

theorem rcore_rfConjL_mul_fix (H : Subgroup (TreeAut X)) (N : Subgroup (RNFree X H))
    [N.Normal] (x₀ : X) (hcomm : nfCommRelators H x₀ ⊆ N) (e f : ↥(higmanThompsonV X))
    (hf : MapsCone (f : Equiv.Perm (Cantor X)) [x₀] [x₀]) (k : ↥H) :
    rfConjL H N (e * f) k = rfConjL H N e k := by
  have hc := rcore_rfL_commute_fix H N x₀ hcomm f hf k
  rw [rcore_rfConjL_eq, rcore_rfConjL_eq, map_mul, mul_inv_rev]
  calc rfV H N e * rfV H N f * rfL H N k * ((rfV H N f)⁻¹ * (rfV H N e)⁻¹)
      = rfV H N e * (rfV H N f * rfL H N k) * (rfV H N f)⁻¹ * (rfV H N e)⁻¹ := by
        simp only [mul_assoc]
    _ = rfV H N e * (rfL H N k * rfV H N f) * (rfV H N f)⁻¹ * (rfV H N e)⁻¹ := by
        rw [hc.eq]
    _ = rfV H N e * rfL H N k * (rfV H N e)⁻¹ := by
        simp only [mul_assoc, mul_inv_cancel_left]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rcore_rfConjL_mul_fix

/-- `rfConjL H N e` depends only on the cone that `e` carries `cone [x₀]` onto. -/
theorem rcore_rfConjL_congr (H : Subgroup (TreeAut X)) (N : Subgroup (RNFree X H)) [N.Normal]
    (x₀ : X) (hcomm : nfCommRelators H x₀ ⊆ N) {w : List X} {e₁ e₂ : ↥(higmanThompsonV X)}
    (he₁ : MapsCone (e₁ : Equiv.Perm (Cantor X)) [x₀] w)
    (he₂ : MapsCone (e₂ : Equiv.Perm (Cantor X)) [x₀] w) (k : ↥H) :
    rfConjL H N e₂ k = rfConjL H N e₁ k := by
  have h := rcore_rfConjL_mul_fix H N x₀ hcomm e₁ (e₁⁻¹ * e₂) (he₂.comp he₁.inv) k
  rwa [mul_inv_cancel_left] at h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rcore_rfConjL_congr

theorem rcore_commute_transport (H : Subgroup (TreeAut X)) (N : Subgroup (RNFree X H))
    [N.Normal] (x₀ : X) (hcomm : nfCommRelators H x₀ ⊆ N) {w₀ w : List X}
    {e₀ e g : ↥(higmanThompsonV X)} (he₀ : MapsCone (e₀ : Equiv.Perm (Cantor X)) [x₀] w₀)
    (he : MapsCone (e : Equiv.Perm (Cantor X)) [x₀] w)
    (hg0 : MapsCone (g : Equiv.Perm (Cantor X)) [x₀] [x₀])
    (hgw : MapsCone (g : Equiv.Perm (Cantor X)) w₀ w) {h k : ↥H}
    (hc : Commute (rfL H N h) (rfConjL H N e₀ k)) : Commute (rfL H N h) (rfConjL H N e k) := by
  have h1 := (Commute.conj_iff (rfV H N g)).mpr hc
  rwa [rcore_conj_rfL_fix H N x₀ hcomm g hg0, rcore_conj_rfConjL,
    ← rcore_rfConjL_congr H N x₀ hcomm (e₁ := g * e₀) (he₀.comp hgw) he k] at h1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rcore_commute_transport

/-- **Step 3.** Two disjoint-cone pairs give every disjoint-cone relator. -/
theorem rcore_disj_subset (H : Subgroup (TreeAut X)) (N : Subgroup (RNFree X H)) [N.Normal]
    {x₀ x₁ : X} (hne : x₁ ≠ x₀) (hcomm : nfCommRelators H x₀ ⊆ N)
    {e₁ e₂ : ↥(higmanThompsonV X)} (he₁ : MapsCone (e₁ : Equiv.Perm (Cantor X)) [x₀] [x₁])
    (he₂ : MapsCone (e₂ : Equiv.Perm (Cantor X)) [x₀] [x₁, x₁])
    (hE : ∀ h k : ↥H,
      Commute (rfL H N h) (rfConjL H N e₁ k) ∧ Commute (rfL H N h) (rfConjL H N e₂ k)) :
    nfDisjRelators H x₀ ⊆ N := by
  rintro r ⟨h, k, e, w, he, hxw, hwx, rfl⟩
  refine rf_mem_of_commute (N := N) ?_
  change Commute (rfL H N h) (rfConjL H N e k)
  obtain ⟨g, hgV, hg0, hgw⟩ := rcore_exists_stab_mapsCone hne hxw hwx
  rcases hgw with hgw | hgw
  · exact rcore_commute_transport H N x₀ hcomm he₁ he (g := ⟨g, hgV⟩) hg0 hgw (hE h k).1
  · exact rcore_commute_transport H N x₀ hcomm he₂ he (g := ⟨g, hgV⟩) hg0 hgw (hE h k).2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rcore_disj_subset

/-- Local copies on incomparable cones commute in the quotient. -/
theorem rcore_commute_rfConjL_incomp [Nontrivial X] (H : Subgroup (TreeAut X))
    (N : Subgroup (RNFree X H)) [N.Normal] (x₀ : X) (hcomm : nfCommRelators H x₀ ⊆ N)
    (hdisj : nfDisjRelators H x₀ ⊆ N) {u w : List X} (huw : ¬ u <+: w) (hwu : ¬ w <+: u)
    {e₁ e₂ : ↥(higmanThompsonV X)} (he₁ : MapsCone (e₁ : Equiv.Perm (Cantor X)) [x₀] u)
    (he₂ : MapsCone (e₂ : Equiv.Perm (Cantor X)) [x₀] w) (h k : ↥H) :
    Commute (rfConjL H N e₁ h) (rfConjL H N e₂ k) := by
  obtain ⟨g, hgV, hgu, w', hgw, hxw', hw'x⟩ := rcore_exists_to_root x₀ huw hwu
  have hc : Commute (rfL H N h) (rfConjL H N (⟨g, hgV⟩ * e₂) k) :=
    rf_commute_of_mem (N := N) (hdisj ⟨h, k, ⟨g, hgV⟩ * e₂, w', he₂.comp hgw, hxw', hw'x, rfl⟩)
  have hL : rfConjL H N (⟨g, hgV⟩ * e₁) h = rfL H N h := by
    have h1 := rcore_rfConjL_mul_fix H N x₀ hcomm 1 (⟨g, hgV⟩ * e₁) (he₁.comp hgu) h
    rwa [one_mul, rcore_rfConjL_eq H N 1 h, map_one, one_mul, inv_one, mul_one] at h1
  rw [← hL, ← rcore_conj_rfConjL, ← rcore_conj_rfConjL] at hc
  exact (Commute.conj_iff (rfV H N ⟨g, hgV⟩)).mp hc

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rcore_commute_rfConjL_incomp

end

end GroupApproximation.BooneHigman.Metabelian.Envelope
