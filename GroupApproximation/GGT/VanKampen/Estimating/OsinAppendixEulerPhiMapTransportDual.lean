import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerPhiMapTransportPerm
import GroupApproximation.GGT.VanKampen.CombMapDual
import GroupApproximation.Meta.AxiomGuard

/-!
# The retained darts of two dual restrictions

Osin, arXiv:math/0411039v3, Appendix, the assumption before Lemma 9.3: "inside every 2-gon of
`Φ′_M`, there is a vertex of `Φ_M`".

`RegionCandidate.phiMapO family E` restricts the dual of the collapsed map to the crossing darts.
Let `ιc` embed one collapsed map into another, commuting with reversal and carrying the crossings
exactly onto the crossings.  If the face rotations agree along `ιc` up to a detour past one
non-crossing dart, or agree outright, the two restrictions are isomorphic.

* `PhiMapTransport.retainedEquiv`, `retainedEquiv_val`, `retainedEquiv_alpha`.
* `PhiMapTransport.retainedEquiv_sigma_bypass`, `retainedEquiv_sigma_of_semiconj`.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`), through Osin's Lemma 9.7(a);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.PhiMapTransport

open Equiv

universe u v

variable {R : CombMap.{u}} {R' : CombMap.{v}} (ιc : R.Dart ↪ R'.Dart)
  {kp : R.Dart → Prop} (hkp : ∀ x, kp (R.dual.alpha x) ↔ kp x)
  {kp' : R'.Dart → Prop} (hkp' : ∀ x, kp' (R'.dual.alpha x) ↔ kp' x)
  (hcorr : ∀ x, kp' (ιc x) ↔ kp x) (hrange : ∀ x', kp' x' → x' ∈ Set.range ιc)

/-- **The retained darts of two restrictions correspond** through an embedding carrying one retained
set onto the other. -/
noncomputable def retainedEquiv :
    (CombMap.PredicateRestriction.toCombMap R.dual kp hkp).Dart ≃
      (CombMap.PredicateRestriction.toCombMap R'.dual kp' hkp').Dart :=
  Equiv.ofBijective (fun y => ⟨ιc y.1, (hcorr y.1).mpr y.2⟩)
    ⟨fun y z h => Subtype.ext (ιc.injective (congrArg Subtype.val h)), fun y' => by
      obtain ⟨x, hx⟩ := hrange y'.1 y'.2
      exact ⟨⟨x, (hcorr x).mp (by rw [hx]; exact y'.2)⟩, Subtype.ext hx⟩⟩

theorem retainedEquiv_val (y : (CombMap.PredicateRestriction.toCombMap R.dual kp hkp).Dart) :
    (retainedEquiv ιc hkp hkp' hcorr hrange y).1 = ιc y.1 := rfl

/-- **The correspondence commutes with reversal.** -/
theorem retainedEquiv_alpha (hαc : ∀ x, ιc (R.alpha x) = R'.alpha (ιc x))
    (y : (CombMap.PredicateRestriction.toCombMap R.dual kp hkp).Dart) :
    retainedEquiv ιc hkp hkp' hcorr hrange
        ((CombMap.PredicateRestriction.toCombMap R.dual kp hkp).alpha y) =
      (CombMap.PredicateRestriction.toCombMap R'.dual kp' hkp').alpha
        (retainedEquiv ιc hkp hkp' hcorr hrange y) :=
  Subtype.ext (hαc y.1)

/-- **The correspondence commutes with rotation**, when the face rotations agree along `ιc` up to a
detour past one dart that is not retained. -/
theorem retainedEquiv_sigma_bypass {w : R.Dart} {s : R'.Dart} (hs : s ∉ Set.range ιc)
    (hw : ¬ kp w) (h0 : R.facePerm w ≠ w)
    (h1 : ∀ x, x ≠ w → R.facePerm x ≠ w → R'.facePerm (ιc x) = ιc (R.facePerm x))
    (h2 : ∀ x, x ≠ w → R.facePerm x = w → R'.facePerm (ιc x) = s)
    (h3 : R'.facePerm s = ιc (R.facePerm w))
    (y : (CombMap.PredicateRestriction.toCombMap R.dual kp hkp).Dart) :
    (CombMap.PredicateRestriction.toCombMap R'.dual kp' hkp').sigma
        (retainedEquiv ιc hkp hkp' hcorr hrange y) =
      retainedEquiv ιc hkp hkp' hcorr hrange
        ((CombMap.PredicateRestriction.toCombMap R.dual kp hkp).sigma y) := by
  have hq : PermFirstReturn.IsFirstReturn R.facePerm
      (CombMap.PredicateRestriction.sigma R.dual kp) (Function.Embedding.subtype kp) :=
    CombMap.PredicateRestriction.sigma_firstReturn R.dual kp
  have hq2 := isFirstReturn_bypass hs h0 h1 h2 h3 (e := Function.Embedding.subtype kp)
    (fun hmem => by
      obtain ⟨c, hc⟩ := hmem
      apply hw
      rw [← hc]
      exact c.2) hq
  exact apply_equiv_of_isFirstReturn (retainedEquiv ιc hkp hkp' hcorr hrange) (fun _ => rfl) hq2
    (CombMap.PredicateRestriction.sigma_firstReturn R'.dual kp') y

/-- **The correspondence commutes with rotation**, when the face rotations agree along `ιc`. -/
theorem retainedEquiv_sigma_of_semiconj
    (h : ∀ x, R'.facePerm (ιc x) = ιc (R.facePerm x))
    (y : (CombMap.PredicateRestriction.toCombMap R.dual kp hkp).Dart) :
    (CombMap.PredicateRestriction.toCombMap R'.dual kp' hkp').sigma
        (retainedEquiv ιc hkp hkp' hcorr hrange y) =
      retainedEquiv ιc hkp hkp' hcorr hrange
        ((CombMap.PredicateRestriction.toCombMap R.dual kp hkp).sigma y) := by
  have hq : PermFirstReturn.IsFirstReturn R.facePerm
      (CombMap.PredicateRestriction.sigma R.dual kp) (Function.Embedding.subtype kp) :=
    CombMap.PredicateRestriction.sigma_firstReturn R.dual kp
  have hq2 := isFirstReturn_of_semiconj h (e := Function.Embedding.subtype kp) hq
  exact apply_equiv_of_isFirstReturn (retainedEquiv ιc hkp hkp' hcorr hrange) (fun _ => rfl) hq2
    (CombMap.PredicateRestriction.sigma_firstReturn R'.dual kp') y

end GroupApproximation.GGT.VanKampen.PhiMapTransport

#audit_axioms GroupApproximation.GGT.VanKampen.PhiMapTransport.retainedEquiv_alpha
#audit_axioms GroupApproximation.GGT.VanKampen.PhiMapTransport.retainedEquiv_sigma_bypass
#audit_axioms GroupApproximation.GGT.VanKampen.PhiMapTransport.retainedEquiv_sigma_of_semiconj
