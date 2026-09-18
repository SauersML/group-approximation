import GroupApproximation.BooneHigman.Metabelian.ElemFPK2StabRange
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2SplitStab
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyNagaoJResMain
import GroupApproximation.BooneHigman.Metabelian.ElemFPBhNagaoWireUncondChain
import GroupApproximation.BooneHigman.Metabelian.VdKParPresKernel
import GroupApproximation.Meta.AxiomGuard

/-!
# Diagonal stability on `ker ev₀`: the unconditional `k = 1` instance

Lane `bh-met-96`, part 1 of 3.  Target: `PolyK2StabRangeDiagStatement` (module
`ElemFPK2StabRange`), the second conjunct of `P1 = PolyK2NilGapStatementOver (ZMod p) 4`.

What Nagao's theorem gives, now that it is unconditional (`k2PolyNagaoJRes_K2_bot`:
`K₂(N, F_p[X]) = ⊥` for `N ≥ 5`):

* `stabDiagVdk_eq_one_mvFinOne`: every element of `K₂(N, F_p[s])`, `N ≥ 5`, is trivial,
  where `F_p[s] = MvPolynomial (Fin 1) (ZMod p)`.
* `stabDiagVdk_diag_one`: **the `k = 1` instance of `PolyK2StabRangeDiagStatement`**, at rank
  `N = 1 + 4 = 5`.  Its hypotheses on `u` are not needed.
* `stabDiagVdk_noHiddenRel_mvFinOne`, `stabDiagVdk_noHiddenRel_poly`: the parabolic presentation
  of lane `bh-met-92g` has no hidden relations, `ker Π = ⊥` (`vdkParPres_NoHiddenRel n R`), for
  `R = F_p[s]` and `R = F_p[X]` at every `n ≥ 5`.  This is the "`ker Π = ⊥` for `F_p[s]`" of
  the frontier note.  For `F_p[s]`, `sr ≤ 2` (`vdkStab_stableRangeLE_polyOne`), so `n = 5` is
  the rank `sr + 3` asked for there.

LOUD (scope).  `ker Π = ⊥` over `F_p[s]` only covers `k = 1`.  The diagonal statement at `k` is
about the ring `F_p[s_1..s_k]` at rank `k + 4`.  At `k ≥ 2` it needs `ker Π = ⊥` (or injectivity
of `K2Stab` on `ker ev₀`) over `F_p[s_1..s_k]` itself.  Nagao gives nothing there (see part 2,
`ElemFPStabDiagVdkWire`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic

/-- **Nagao over `F_p[s]`**: every element of `K₂(N, F_p[s])`, `N ≥ 5`, is trivial. -/
theorem stabDiagVdk_eq_one_mvFinOne {p N : ℕ} (hp : p.Prime) (hN : 5 ≤ N)
    (u : K2n N (MvPolynomial (Fin 1) (ZMod p))) : u = 1 :=
  eq_one_of_K2_eq_bot (bhNagaoUncond_K2_bot_mvFinOne hp hN) u

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.stabDiagVdk_eq_one_mvFinOne

/-- **The `k = 1` instance of `PolyK2StabRangeDiagStatement`, unconditionally**: over
`F_p[s] = MvPolynomial (Fin 1) (ZMod p)` at rank `1 + 4`.  Since `K₂(5, F_p[s]) = ⊥`, neither
hypothesis on `u` is used. -/
theorem stabDiagVdk_diag_one (p : ℕ) (hp : p.Prime) :
    ∀ u : K2n (1 + 4) (MvPolynomial (Fin 1) (ZMod p)),
      K2Map (MvPolynomial.constantCoeff : MvPolynomial (Fin 1) (ZMod p) →+* ZMod p) u = 1 →
        K2Stab (1 + 4) (MvPolynomial (Fin 1) (ZMod p)) u = 1 → u = 1 :=
  fun u _ _ ↦ stabDiagVdk_eq_one_mvFinOne hp (by omega) u

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.stabDiagVdk_diag_one

/-- **No hidden relations over `F_p[s]`**: `ker Π = ⊥` for the parabolic presentation
`R^n ⋊ St_n(R) ↠ P` at every `n ≥ 5`, `R = MvPolynomial (Fin 1) (ZMod p)`.  By
`vdkParPres_noHiddenRel_iff_K2Stab_injective` this is injectivity of `K2Stab n R`, which holds
because the source `K₂(n, F_p[s])` is trivial. -/
theorem stabDiagVdk_noHiddenRel_mvFinOne {p n : ℕ} (hp : p.Prime) (hn : 5 ≤ n) :
    vdkParPres_NoHiddenRel n (MvPolynomial (Fin 1) (ZMod p)) :=
  vdkParPres_noHiddenRel_iff_K2Stab_injective.mpr fun a b _ ↦
    (stabDiagVdk_eq_one_mvFinOne hp hn a).trans (stabDiagVdk_eq_one_mvFinOne hp hn b).symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.stabDiagVdk_noHiddenRel_mvFinOne

/-- **No hidden relations over `F_p[X]`**: `ker Π = ⊥` at every `n ≥ 5`,
`R = Polynomial (ZMod p)`, from Nagao's `K₂(n, F_p[X]) = ⊥`. -/
theorem stabDiagVdk_noHiddenRel_poly {p n : ℕ} (hp : p.Prime) (hn : 5 ≤ n) :
    vdkParPres_NoHiddenRel n (Polynomial (ZMod p)) :=
  vdkParPres_noHiddenRel_iff_K2Stab_injective.mpr fun a b _ ↦
    (eq_one_of_K2_eq_bot (k2PolyNagaoJRes_K2_bot hp hn) a).trans
      (eq_one_of_K2_eq_bot (k2PolyNagaoJRes_K2_bot hp hn) b).symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.stabDiagVdk_noHiddenRel_poly

end GroupApproximation.BooneHigman.Metabelian.ElemFP
