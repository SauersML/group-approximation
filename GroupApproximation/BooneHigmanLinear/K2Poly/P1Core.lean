import GroupApproximation.BooneHigmanLinear.K2Poly.P1Tree
import GroupApproximation.BooneHigmanLinear.PaninAffine.Main
import GroupApproximation.BooneHigmanLinear.PaninAffine.Cor29Wire
import GroupApproximation.BooneHigmanLinear.PaninAffine.PatchWire
import GroupApproximation.BooneHigmanLinear.Tulenbaev.LocalGlobal
import GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Reductions
import GroupApproximation.BooneHigmanLinear.CharZero.K2Found.RatFuncFinitary
import GroupApproximation.Meta.AxiomGuard

/-!
# P1 from the core open inputs of the K₂ program

k2-poly (lane bh-pal-wire, lead). This sharpens `P1Tree.gapOver_of_inputs` with the pieces
landed since:

* GEO-AFF `PaninAffine.infiniteFieldAffineMonicFibre` and F.5 `K2Found.ratFuncFinitaryAt`
  (proved);
* A5.2 is needed only as `FieldNF.FieldCosetAt`; the stronger wide normal-form
  input implies it in `FieldNF.WideMain`;
* Cor 2.9 ⇐ GEO-AFF + excision + monic injectivity + `Cor29FinitaryAt`
  (`PaninAffine.nkFieldInjAt_of_geometry`, k2-panin);
* H.b and monic injectivity ⇐ LG + T Prop 4.3(a) + excision
  (`TulenbaevHorrocks.stMonicInjStatement_of`, pal-q111).

`gapOver_of_core hD hC hLoc` gives Route A's P1. Its three remaining inputs are:

* `hD`: `Tulenbaev.StDilationStatementAt 5`; the local–global principle follows from it
  using the proved maximal-ideal finite-stage theorem;
* `hC`: `FieldNF.FieldCosetAt F` at every field (A5.2, the field coset step);
* `hLoc`: `TulenbaevHorrocks.StLocalHorrocksStatementAt 5` (T Prop 4.3(a) over local rings).

Zariski excision is supplied by `PaninAffine.stZariskiExcisionAt`, and the finitary step
by `K2Found.cor29FinitaryAt`. Neither is an assumed literature input.
-/

namespace GroupApproximation.BooneHigmanLinear.K2Poly

/-- Monic injectivity for every ring, from LG, the local Horrocks property and excision. -/
theorem stMonicInj_of_core (hLG : Tulenbaev.StLocalGlobalStatementAt 5)
    (hLoc : TulenbaevHorrocks.StLocalHorrocksStatementAt 5) :
    TulenbaevHorrocks.StMonicInjStatementAt 5 :=
  TulenbaevHorrocks.stMonicInjStatement_of hLG hLoc fun A _ _ hN =>
    PaninAffine.stZariskiExcisionAt hN (Polynomial A)

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.stMonicInj_of_core

/-- **Route A's P1** from dilation, the field coset step and local Horrocks. -/
theorem gapOver_of_core (hD : Tulenbaev.StDilationStatementAt 5)
    (hC : ∀ (F : Type) [Field F], FieldNF.FieldCosetAt F)
    (hLoc : TulenbaevHorrocks.StLocalHorrocksStatementAt 5) :
    ∀ p : ℕ, p.Prime → BooneHigman.Metabelian.ElemFP.PolyK2NilGapStatementOver (ZMod p) 4 :=
  have hLG := Tulenbaev.stLocalGlobal_of_dilation hD
  have hMon := stMonicInj_of_core hLG hLoc
  gapOver_of_inputs hLG hC
    (fun K _ _ k r hr M _ =>
      PaninAffine.nkFieldInjAt_of_geometry (PaninAffine.infiniteFieldAffineMonicFibre K)
        (fun A _ => PaninAffine.stZariskiExcisionAt hr A) (fun A _ => hMon A r hr) M)
    (fun p _ k r _ => K2Found.ratFuncFinitaryAt (ZMod p) k r)
    (fun p _ k r hr f hf α hα =>
      hMon _ r hr f hf α (hα (Localization.Away f)
        (algebraMap _ (Localization.Away f)) (IsLocalization.Away.algebraMap_isUnit f)))

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.gapOver_of_core

end GroupApproximation.BooneHigmanLinear.K2Poly
