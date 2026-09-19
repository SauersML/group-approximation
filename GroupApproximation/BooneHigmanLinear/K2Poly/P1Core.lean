import GroupApproximation.BooneHigmanLinear.K2Poly.P1Tree
import GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.WideMain
import GroupApproximation.BooneHigmanLinear.PaninAffine.Main
import GroupApproximation.BooneHigmanLinear.PaninAffine.Cor29Wire
import GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Reductions
import GroupApproximation.BooneHigmanLinear.CharZero.K2Found.RatFuncFinitary
import GroupApproximation.Meta.AxiomGuard

/-!
# P1 from the core open inputs of the K₂ program

k2-poly (lane bh-pal-wire, lead). This sharpens `P1Tree.gapOver_of_inputs` with the pieces
landed since:

* GEO-AFF `PaninAffine.infiniteFieldAffineMonicFibre` and F.5 `K2Found.ratFuncFinitaryAt`
  (proved);
* A5.2 ⇐ `FieldNF.fnWide_Statement` (`fnWide_coset_of_statement`, k2-field-a);
* Cor 2.9 ⇐ GEO-AFF + excision + monic injectivity + `Cor29FinitaryAt`
  (`PaninAffine.nkFieldInjAt_of_geometry`, k2-panin);
* H.b and monic injectivity ⇐ LG + T Prop 4.3(a) + excision
  (`TulenbaevHorrocks.stMonicInjStatement_of`, pal-q111).

`gapOver_of_core hLG hW hLoc hExc hCF` gives Route A's P1. Its five inputs are:

* `hLG`: `Tulenbaev.StLocalGlobalStatementAt 5` (A2/LG);
* `hW`: `FieldNF.fnWide_Statement F` at every field (A5.2, the single wide residual);
* `hLoc`: `TulenbaevHorrocks.StLocalHorrocksStatementAt 5` (T Prop 4.3(a) over local rings);
* `hExc`: Zariski excision `PaninAffine.StZariskiExcisionAt A r` for `r ≥ 5` (F.4, LSV 2.6);
* `hCF`: the finitary step `PaninAffine.Cor29FinitaryAt` at the maximal ideals of `K[s]`.
-/

namespace GroupApproximation.BooneHigmanLinear.K2Poly

/-- Monic injectivity for every ring, from LG, the local Horrocks property and excision. -/
theorem stMonicInj_of_core (hLG : Tulenbaev.StLocalGlobalStatementAt 5)
    (hLoc : TulenbaevHorrocks.StLocalHorrocksStatementAt 5)
    (hExc : ∀ (A : Type) [CommRing A] (r : ℕ), 5 ≤ r → PaninAffine.StZariskiExcisionAt A r) :
    TulenbaevHorrocks.StMonicInjStatementAt 5 :=
  TulenbaevHorrocks.stMonicInjStatement_of hLG hLoc fun A _ N hN => hExc (Polynomial A) N hN

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.stMonicInj_of_core

/-- **Route A's P1** from the five core inputs. -/
theorem gapOver_of_core (hLG : Tulenbaev.StLocalGlobalStatementAt 5)
    (hW : ∀ (F : Type) [Field F], FieldNF.fnWide_Statement F)
    (hLoc : TulenbaevHorrocks.StLocalHorrocksStatementAt 5)
    (hExc : ∀ (A : Type) [CommRing A] (r : ℕ), 5 ≤ r → PaninAffine.StZariskiExcisionAt A r)
    (hCF : ∀ (K : Type) [Field K] [Infinite K] (k r : ℕ), 5 ≤ r →
      ∀ (M : Ideal (MvPolynomial (Fin k) K)) [M.IsMaximal],
        PaninAffine.Cor29FinitaryAt (MvPolynomial (Fin k) K) M r) :
    ∀ p : ℕ, p.Prime → BooneHigman.Metabelian.ElemFP.PolyK2NilGapStatementOver (ZMod p) 4 :=
  have hMon := stMonicInj_of_core hLG hLoc hExc
  gapOver_of_inputs hLG (fun F _ => FieldNF.fnWide_coset_of_statement (hW F))
    (fun K _ _ k r hr M _ =>
      PaninAffine.nkFieldInjAt_of_geometry (PaninAffine.infiniteFieldAffineMonicFibre K)
        (fun A _ => hExc A r hr) (fun A _ => hMon A r hr) M (hCF K k r hr M))
    (fun p _ k r _ => K2Found.ratFuncFinitaryAt (ZMod p) k r)
    (fun p _ k r hr =>
      TulenbaevHorrocks.horrocksMonicAt_of_stMonicInjAt (hMon _ r hr))

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.gapOver_of_core

end GroupApproximation.BooneHigmanLinear.K2Poly
