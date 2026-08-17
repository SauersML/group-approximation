import GroupApproximation.Computability.IndexMapComputable
import GroupApproximation.Computability.ComputableConfigReduction

/-!
# A modular machine whose halting problem on configurations is undecidable

`exists_modularMachine_halting_not_computablePred` gives a machine together with
a map `f : ℕ → ℕ × ℕ` along which halting is undecidable, and that is not the
statement the Adian--Rabin lane can consume: the words of `G_M` are attached to
*configurations*, so what is needed is undecidability of `mm.Halts` itself, with
no indexing map.  The two are not interchangeable — composing a computable
predicate with an arbitrary `f` need not be computable — and the gap is exactly
`Computable f`.

This module closes it.  The construction is the one in
`ModularMachineUndecidable`, repeated here rather than edited there so that the
existing statement keeps its users, with the single addition that the index map
is handed back together with its computability, supplied by
`IndexMapComputable.computable_index_map`.

The reason that computability is available at all is that the map only ever
builds an *initial* configuration.  Nothing about the transition function, and
nothing from `PartrecToTM2 → TM2to1 → TM1to0`, has to be computable; the
choice-based symbol encoding of `TMData.ofFintype` is applied to finitely many
symbols and contributes fixed naturals.  See `D4'` in
`Computability.AdianRabinMarkovProperty`.
-/

namespace GroupApproximation
namespace Computability

open Turing Turing.PartrecToTM2

/-- **The indexed statement, with the index map's computability.**  Identical to
`exists_modularMachine_halting_not_computablePred` except for the extra
conjunct, which is what the configuration form needs. -/
theorem exists_modularMachine_halting_computable_index (n : ℕ) :
    ∃ (mm : BooneGroup.ModularMachine) (f : ℕ → ℕ × ℕ), Computable f ∧
      ¬ ComputablePred fun m : ℕ => mm.Halts (f m) := by
  classical
  obtain ⟨c, hc⟩ := tm0_halting_not_computablePred n
  letI : Inhabited Λ' := ⟨trNormal c Cont'.halt⟩
  letI : Fintype (TM2to1.Γ' K' (fun _ : K' => Γ')) := TM2to1.Γ'.fintype
  have hs2 : TM2.Supports tr (codeSupp c Cont'.halt) := tr_supports c Cont'.halt
  have hs1 := TM2to1.tr_supports tr hs2
  have hs0 := TM1to0.tr_supports (TM2to1.tr tr) hs1
  set M₀ := TM1to0.tr (TM2to1.tr tr) with hM₀
  set S₀ := TM1to0.trStmts (TM2to1.tr tr) (TM2to1.trSupp tr (codeSupp c Cont'.halt))
    with hS₀
  have hdef : (default : TM1to0.Λ' (TM2to1.tr tr)) ∈ S₀ := hs0.1
  letI : Inhabited {q // q ∈ S₀} := ⟨⟨default, hdef⟩⟩
  set M₁ := TM0Restrict.restrict M₀ S₀ with hM₁
  set D := TMData.ofFintype (TM2to1.Γ' K' (fun _ : K' => Γ')) {q // q ∈ S₀} with hD
  have hinit : ∀ l : List (TM2to1.Γ' K' (fun _ : K' => Γ')),
      TM0Restrict.unrestrict (TM0.init l : TM0.Cfg _ {q // q ∈ S₀}) = TM0.init l :=
    fun _ => rfl
  refine ⟨(D.toQuad M₁).toModular,
    fun m => (D.toQuad M₁).encCfg (D.initQCfg (TM2to1.trInit K'.main (trList [m]))),
    computable_index_map D M₁, ?_⟩
  intro hcomp
  refine hc ?_
  have hkey : ∀ m : ℕ, ((D.toQuad M₁).toModular.Halts
      ((D.toQuad M₁).encCfg (D.initQCfg (TM2to1.trInit K'.main (trList [m]))))
      ↔ (TM0.eval M₀ (TM2to1.trInit K'.main (trList [m]))).Dom) := by
    intro m
    rw [QuadMachine.halts_encCfg_iff _ (D.rep_initQCfg M₁ _).wf,
      D.QHalts_iff_TMHalts (D.rep_initQCfg M₁ _),
      TM0Restrict.tmHalts_iff M₀ hs0, hinit,
      TMData.tmHalts_iff_eval_dom]
  have hEq : (fun m : ℕ => (D.toQuad M₁).toModular.Halts
        ((D.toQuad M₁).encCfg (D.initQCfg (TM2to1.trInit K'.main (trList [m])))))
      = fun m : ℕ => (TM0.eval M₀ (TM2to1.trInit K'.main (trList [m]))).Dom :=
    funext fun m => propext (hkey m)
  exact hEq ▸ hcomp

/-- **The halting problem of a fixed modular machine, on its own
configurations, is undecidable.**  Unconditional: no hypothesis and no
literature input, the undecidable source being Mathlib's
`ComputablePred.halting_problem` reached through Mathlib's own compiler.

This is the form the group side consumes: the words of `G_M` attached to a
configuration `(i, j)` are explicit in `i` and `j`, so with this statement every
encoding difficulty stays on the machine side. -/
theorem exists_modularMachine_config_halting_not_computablePred :
    ∃ mm : BooneGroup.ModularMachine,
      ¬ ComputablePred fun p : ℕ × ℕ => mm.Halts p :=
  exists_modularMachine_config_halting_not_computablePred_of_computable
    (exists_modularMachine_halting_computable_index 0)

end Computability
end GroupApproximation
