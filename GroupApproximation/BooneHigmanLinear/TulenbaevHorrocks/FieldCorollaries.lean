import GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Reductions
import GroupApproximation.BooneHigman.Metabelian.ElemFPBhNagaoWireUncondBase
import GroupApproximation.BooneHigmanLinear.K2Poly.Statements
import GroupApproximation.Meta.AxiomGuard

/-!
# Horrocks for `St_N`: corollaries through the `K₂` chain (lane pal-q111)

The corollaries of `TulenbaevHorrocks.Field` and `TulenbaevHorrocks.Reductions` that use the heavy
`K₂` chain.  They sit apart so that the two light files build even while the chain is red.

* `stHorrocksAt_of_fieldNK`: the Horrocks property of `St_N` over every field, `N ≥ 5`, from
  `FieldNKStatement` (board piece A5).
* `stHorrocksAt_zmod`: over `F_p`, `N ≥ 5`, unconditionally, from Nagao
  (`ElemFP.bhNagaoUncond_wire_K2_bot_nagao`).
* `horrocksMonicAt_of_stMonicInjAt`: `StMonicInjAt` gives `K2Poly`'s `HorrocksMonicAt`.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace TulenbaevHorrocks

open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman.SteinbergBasic Polynomial

/-- **The field case over every field, `N ≥ 5`**, from `FieldNKStatement` (board piece A5). -/
theorem stHorrocksAt_of_fieldNK (h : FieldNKStatement) (k : Type) [Field k] {N : ℕ}
    (hN : 5 ≤ N) : StHorrocksAt k N :=
  stHorrocksAt_of_const k (by omega) (h k N hN)

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.stHorrocksAt_of_fieldNK

/-- **Horrocks for `St_N` over `F_p`, `N ≥ 5`, unconditionally** (Nagao's `K₂(N, F_p[X]) = 1`). -/
theorem stHorrocksAt_zmod {p : ℕ} (hp : p.Prime) {N : ℕ} (hN : 5 ≤ N) :
    StHorrocksAt (ZMod p) N := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact stHorrocksAt_of_K2_eq_bot (ZMod p) (by omega)
    (BooneHigman.Metabelian.ElemFP.bhNagaoUncond_wire_K2_bot_nagao hp N hN)

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.stHorrocksAt_zmod

/-- `StMonicInjAt` gives the board's `HorrocksMonicAt` (K2Poly, LSV route). -/
theorem horrocksMonicAt_of_stMonicInjAt {A : Type} [CommRing A] {N : ℕ}
    (h : StMonicInjAt A N) : HorrocksMonicAt A N :=
  fun f hf α hα => h f hf α (hα (Localization.Away f) (algebraMap A[X] (Localization.Away f))
    (IsLocalization.Away.algebraMap_isUnit f))

#audit_axioms
  GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.horrocksMonicAt_of_stMonicInjAt

end TulenbaevHorrocks
end BooneHigmanLinear
end GroupApproximation
