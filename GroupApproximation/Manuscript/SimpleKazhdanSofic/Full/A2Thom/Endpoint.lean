import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.A2Thom.Shift
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.A2Thom.LEF
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.A2ThomT.Assembly
import GroupApproximation.Kazhdan.KazhdanFiniteGeneration
import GroupApproximation.Meta.AxiomGuard

/-!
# Thom's group: finitely generated, Kazhdan, LEF, not residually finite

`simple_kazhdan_sofic_group.tex`, Introduction, tex l.57–59 (table row A2): "Thom constructed a
finitely generated Kazhdan group that is locally embeddable into finite groups but not residually
finite" (Thom, Groups Geom. Dyn. 4 (2010), §2.1, Lemmas 2.1 and 2.3).

The group is `G = G_0(F_p[t,t⁻¹]) / C` (`Full.A2Endpoint.ThomGroup (ZMod p)`).

* (T): `G_0(F_p[t,t⁻¹])` has (T) (Thom, Lemma 2.1; `Full.A2ThomT.hasKazhdanPropertyT_thomG0`),
  and (T) passes to quotients.
* FG: every Kazhdan group is finitely generated.
* LEF: `isLEF_thomGroup` (Thom, Lemma 2.3; `Full/A2Thom/LEF.lean`).
* not RF: Mal'cev plus Thom's non-injective surjective shift (`Full/A2Thom/Shift.lean`).
-/

namespace GroupApproximation.Full.A2Thom

open GroupApproximation.Full.A2Endpoint

/-- **Thom, Lemma 2.1** (tex l.57–59, "Kazhdan"): Thom's group has property (T). -/
theorem hasKazhdanPropertyT_thomGroup (p : ℕ) [Fact p.Prime] :
    HasKazhdanPropertyT.{0, 0} (ThomGroup (ZMod p)) :=
  HasKazhdanPropertyT.of_surjective (QuotientGroup.mk' (thomC (ZMod p)))
    (QuotientGroup.mk'_surjective (thomC (ZMod p)))
    (Full.A2ThomT.hasKazhdanPropertyT_thomG0 p)

/-- tex l.57–59 ("finitely generated"): Thom's group is finitely generated. -/
theorem thomGroup_fg (p : ℕ) [Fact p.Prime] : Group.FG (ThomGroup (ZMod p)) :=
  KazhdanFiniteGeneration.fg_of_hasKazhdanPropertyT _ (hasKazhdanPropertyT_thomGroup p)

/-- tex l.57–59 ("not residually finite"): Thom's group is not residually finite. -/
theorem not_isResiduallyFinite_thomGroup (p : ℕ) [Fact p.Prime] :
    ¬ IsResiduallyFinite (ThomGroup (ZMod p)) :=
  not_isResiduallyFinite_thomGroup_of_fg (ZMod p) (thomGroup_fg p)

/-- tex l.57–59, all four properties of Thom's group together (Thom, GGD 4 (2010), §2.1). -/
theorem thomGroup_endpoint (p : ℕ) [Fact p.Prime] :
    Group.FG (ThomGroup (ZMod p)) ∧ HasKazhdanPropertyT.{0, 0} (ThomGroup (ZMod p)) ∧
      IsLEF (ThomGroup (ZMod p)) ∧ ¬ IsResiduallyFinite (ThomGroup (ZMod p)) :=
  ⟨thomGroup_fg p, hasKazhdanPropertyT_thomGroup p, isLEF_thomGroup p,
    not_isResiduallyFinite_thomGroup p⟩

#audit_axioms GroupApproximation.Full.A2Thom.thomGroup_endpoint

end GroupApproximation.Full.A2Thom
