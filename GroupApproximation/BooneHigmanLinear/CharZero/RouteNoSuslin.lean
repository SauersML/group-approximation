import GroupApproximation.BooneHigmanLinear.CharZero.ElementaryHost
import GroupApproximation.BooneHigmanLinear.CharZero.CharPElementaryHost
import GroupApproximation.BooneHigmanLinear.FrontierFour
import GroupApproximation.BooneHigman.Metabelian.ChainQuasiLinear
import GroupApproximation.Meta.AxiomGuard

/-!
# Route A without `S1`

`BooneHigmanLinear.FrontierFour` states T1, T2 and T3 from the four route-A inputs `S1`, `P1`, `Z1`
and `H1`. The linear host there uses `S1` (Suslin's local step over `ℤ[1/m][x]`) only through
the absorption leaves `GL_M(S) ↪ E_N(S)`. The char-`p` absorption comes from `S1` too, through
`Absorption.suslinBase3_localHorrocks`.

With `NoSuslin.charZeroLinearHost_of_splitGap` and `NoSuslin.charPLinearHost_of_elementaryFP`,
the linear host needs no absorption at all. So all three theorems below drop `S1`:

* `linearHost_noSuslin (hP1 hZ1)`: every finitely generated linear group, over any field, embeds
  in a finitely presented self-similar group;
* `finitelyGeneratedLinearStatement_noSuslin (hP1 hZ1 hH1)`: T3;
* `finitelyGeneratedMetabelianStatement_noSuslin (hP1 hZ1 hH1)`: T2, finitely generated form;
* `finitelyPresentedMetabelianStatement_noSuslin (hP1 hZ1 hH1)`: T1. A finitely presented group
  is finitely generated, so this is a specialization of T2 and does not go through the Nagao route.

The binders have the same names and types as in `FrontierFour`:
* `hP1 : ∀ p, p.Prime → ElemFP.PolyK2NilGapStatementOver (ZMod p) 4`;
* `hZ1 : ElemFPCharZero.CharZeroK2SplitGapStatement`;
* `hH1 : Envelope.HigmanVCStepBCoreStatement`.
The composition reuses `FrontierFour`'s `envelope_routeA` and `coprimarySplitting_routeA`, and
the `P1` reductions from `linearHost_routeA`. It adds no new mathematics.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace NoSuslin

open GroupApproximation.BooneHigman
open GroupApproximation.BooneHigman.Metabelian

/-- **The linear host from `P1` and `Z1`**, with no Suslin input: every finitely generated
subgroup of `GL_n(K)`, for any field `K`, embeds in a finitely presented self-similar group. -/
theorem linearHost_noSuslin
    (hP1 : ∀ p : ℕ, p.Prime → ElemFP.PolyK2NilGapStatementOver (ZMod p) 4)
    (hZ1 : ElemFPCharZero.CharZeroK2SplitGapStatement) : Products.LinearHostStatement :=
  Chain.linearHostStatement_of_charP_charZero
    (charPLinearHost_of_elementaryFP
      (ElemFP.polynomialFpElementaryFP_of_polynomialFpK2Vanishing
        (ElemFP.polynomialFpK2Vanishing_of_gapOver hP1 ElemFP.vdkRowExt_fieldK2Vanishing)))
    (charZeroLinearHost_of_splitGap hZ1)

#audit_axioms linearHost_noSuslin

/-- **T3 from `P1`, `Z1` and `H1`**: every finitely generated subgroup of `GL_n(K)`, for any
field `K`, embeds in a finitely presented simple group. -/
theorem finitelyGeneratedLinearStatement_noSuslin
    (hP1 : ∀ p : ℕ, p.Prime → ElemFP.PolyK2NilGapStatementOver (ZMod p) 4)
    (hZ1 : ElemFPCharZero.CharZeroK2SplitGapStatement)
    (hH1 : Envelope.HigmanVCStepBCoreStatement) : FinitelyGeneratedLinearStatement :=
  Products.finitelyGeneratedLinearStatement_of_hosts (linearHost_noSuslin hP1 hZ1)
    (envelope_routeA hH1)

#audit_axioms finitelyGeneratedLinearStatement_noSuslin

/-- **T2 from `P1`, `Z1` and `H1`**: finitely generated metabelian groups embed in finitely
presented simple groups. -/
theorem finitelyGeneratedMetabelianStatement_noSuslin
    (hP1 : ∀ p : ℕ, p.Prime → ElemFP.PolyK2NilGapStatementOver (ZMod p) 4)
    (hZ1 : ElemFPCharZero.CharZeroK2SplitGapStatement)
    (hH1 : Envelope.HigmanVCStepBCoreStatement) : FinitelyGeneratedMetabelianStatement :=
  Products.finitelyGeneratedMetabelianStatement_of_pieces
    (Coprimary.metabelianPieces_of_splitting coprimarySplitting_routeA
      (linearHost_noSuslin hP1 hZ1))
    (envelope_routeA hH1)

#audit_axioms finitelyGeneratedMetabelianStatement_noSuslin

/-- **T1 from `P1`, `Z1` and `H1`**: finitely presented metabelian groups embed in finitely
presented simple groups (a finitely presented group is finitely generated). -/
theorem finitelyPresentedMetabelianStatement_noSuslin
    (hP1 : ∀ p : ℕ, p.Prime → ElemFP.PolyK2NilGapStatementOver (ZMod p) 4)
    (hZ1 : ElemFPCharZero.CharZeroK2SplitGapStatement)
    (hH1 : Envelope.HigmanVCStepBCoreStatement) : FinitelyPresentedMetabelianStatement := by
  intro G _ hfp hmeta
  have hfg : Group.FG G := by
    obtain ⟨_, φ, hφ, -⟩ := hfp.out
    exact Group.fg_of_surjective hφ
  exact finitelyGeneratedMetabelianStatement_noSuslin hP1 hZ1 hH1 G hfg hmeta

#audit_axioms finitelyPresentedMetabelianStatement_noSuslin

end NoSuslin
end BooneHigmanLinear
end GroupApproximation
