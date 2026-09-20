import GroupApproximation.BooneHigmanLinear.FrontierFour
import GroupApproximation.BooneHigmanLinear.PolyFpK2Core
import GroupApproximation.Meta.AxiomGuard

/-!
# Route A with the char-`p` input shrunk to `K₂(N, F_p[s₁..s_k]) = ⊥` for `k ≥ 2`

Route A of the metabelian chain (`FrontierFour.lean`) takes the char-`p` input as

* `P1 : ∀ p prime, ElemFP.PolyK2NilGapStatementOver (ZMod p) 4`.

`P1` is the conjunction of two statements: the one-variable nil part (stable `NK₂(F_p[s]) = 0`) and
injective stability at the diagonal rank `k + 4`. The chain consumes it only through
`ElemFP.PolynomialFpK2VanishingStatement`: `K₂(N, F_p[s₁..s_k]) = ⊥` for `N ≥ k + 4`, `N ≥ 5`.
Its slice `k ≤ 1` is proved with no hypothesis
(`ElemFP.bhNagaoUncond_polynomialFpK2Vanishing_le_one`). That slice consists of the field case
and the Euclidean case `F_p[X]` (bh-met-94e, Nagao-style Euclid and Weyl moves), which
ms-sk-uncond-a re-exports as `LVPolyK2`'s `skPolyK2_stableK2Trivial_polynomial_zmod`.

This module replaces `P1` by the smaller statement that is actually owed:

* `PolyFpK2VanishingGeTwoStatement`: `K₂(N, F_p[s₁..s_k]) = ⊥` for `k ≥ 2`, `N ≥ k + 4`.
  - `polynomialFpK2Vanishing_of_geTwo` gives the chain's vanishing statement from it, together
    with the proved `k ≤ 1` slice.
  - `polyFpK2VanishingGeTwo_of_gapOver` shows it is no stronger than `P1`.
* `TulenbaevPolyFpK2Statement`: `K₂(N, F_p[s₁..s_k]) = ⊥` for every `k` and every `N ≥ 5`.
  - `polyFpK2VanishingGeTwo_of_tulenbaev` shows it implies the owed statement.
  - `tulenbaevPolyFpK2_of_injStab_of_stable` derives it from two named inputs of very different
    depth:
    - `TulenbaevInjStabFpStatement`, injective stability. An element of `K₂(N, F_p[s₁..s_k])`
      that dies after padding is trivial, for `N ≥ 5` and every `k`. This is M. Tulenbaev,
      *The Steinberg group of a polynomial ring* (Mat. Sb. 117 (1982); Math. USSR Sb. 45 (1983)
      139–154), Theorem 5.3, for `A = F_p`, where `dim A + 3 = 3 < 5`. Its proof is ELEMENTARY,
      about 15 pages of Steinberg-group manipulations:
      - a local–global principle for the relative group `St_r(A[X], XA[X])` (§2);
      - a Horrocks theorem for `St_r` over local rings (§§3–5);
      - Nagata's change of variables and Suslin's monic lemma;
      - the Suslin–Tulenbaev stability theorem for `K₂` (Zap. LOMI 64, 1976).
    - `StableK2PolyFpVanishingStatement`, stable vanishing. Every element of `K₂(N, F_p[s₁..s_k])`
      dies after padding: stable `K₂(F_p[s₁..s_k]) = K₂(F_p) = 0`. This is Quillen's homotopy
      invariance of `K₂` for regular rings, through the fundamental theorem of higher
      `K`-theory. No elementary proof is known to this lane for `k ≥ 2`. It is the deep part of
      `P1`, and the true remaining obstruction.
* `finitelyPresentedMetabelianStatement_routeAV`, `finitelyGeneratedMetabelianStatement_routeAV`
  and `finitelyGeneratedLinearStatement_routeAV`: T1, T2 and T3 from `S1`, the owed char-`p`
  statement, `Z1` and `H1`.

The foundational statements and generic stability reductions live in `PolyFpK2Core`, so the
`K2Poly` development does not import this endpoint assembly. This module adds no new mathematics:
it is wiring plus the `k ≤ 1` case split.
-/

namespace GroupApproximation
namespace BooneHigmanLinear

open GroupApproximation.BooneHigman

/-- The chain's char-`p` vanishing statement from the owed `k ≥ 2` part and the proved `k ≤ 1`
slice (the field case and Nagao). -/
theorem polynomialFpK2Vanishing_of_geTwo (h : PolyFpK2VanishingGeTwoStatement) :
    Metabelian.ElemFP.PolynomialFpK2VanishingStatement := by
  intro p hp k N hkN h5N
  rcases le_or_gt k 1 with hk | hk
  · exact Metabelian.ElemFP.bhNagaoUncond_polynomialFpK2Vanishing_le_one p hp k N hk hkN h5N
  · exact h p hp k N (by omega) hkN

#audit_axioms GroupApproximation.BooneHigmanLinear.polynomialFpK2Vanishing_of_geTwo

/-- The char-`p` elementary target from the owed statement. -/
theorem polynomialFpElementaryFP_of_geTwo (h : PolyFpK2VanishingGeTwoStatement) :
    Metabelian.ElemFP.PolynomialFpElementaryFPStatement :=
  Metabelian.ElemFP.polynomialFpElementaryFP_of_polynomialFpK2Vanishing
    (polynomialFpK2Vanishing_of_geTwo h)

#audit_axioms GroupApproximation.BooneHigmanLinear.polynomialFpElementaryFP_of_geTwo

/-- **T1 (route A, owed char-`p` input).** Finitely presented metabelian groups embed in finitely
presented simple groups, given `S1`, the owed char-`p` statement, `Z1` and `H1`. -/
theorem finitelyPresentedMetabelianStatement_routeAV
    (hS1 : Metabelian.Absorption.suslinZLocal_BadStatement) (hV : PolyFpK2VanishingGeTwoStatement)
    (hZ1 : Metabelian.ElemFPCharZero.CharZeroK2SplitGapStatement)
    (hH1 : Metabelian.Envelope.HigmanVCStepBCoreStatement) :
    FinitelyPresentedMetabelianStatement :=
  Metabelian.ElemFP.bhNagaoUncond_fpMetabelian_of_polyFpEFP hS1
    (polynomialFpElementaryFP_of_geTwo hV) hZ1 hH1

#audit_axioms GroupApproximation.BooneHigmanLinear.finitelyPresentedMetabelianStatement_routeAV

/-- **T2 (route A, owed char-`p` input).** Finitely generated metabelian groups embed in finitely
presented simple groups, given `S1`, the owed char-`p` statement, `Z1` and `H1`. -/
theorem finitelyGeneratedMetabelianStatement_routeAV
    (hS1 : Metabelian.Absorption.suslinZLocal_BadStatement) (hV : PolyFpK2VanishingGeTwoStatement)
    (hZ1 : Metabelian.ElemFPCharZero.CharZeroK2SplitGapStatement)
    (hH1 : Metabelian.Envelope.HigmanVCStepBCoreStatement) :
    FinitelyGeneratedMetabelianStatement :=
  Products.finitelyGeneratedMetabelianStatement_of_pieces
    (Metabelian.Coprimary.metabelianPieces_of_splitting coprimarySplitting_routeA
      (linearHost_of_polyFpEFP hS1 (polynomialFpElementaryFP_of_geTwo hV) hZ1))
    (envelope_routeA hH1)

#audit_axioms GroupApproximation.BooneHigmanLinear.finitelyGeneratedMetabelianStatement_routeAV

/-- **T3 (route A, owed char-`p` input).** Every finitely generated subgroup of `GL_n(K)`, for any
field `K`, embeds in a finitely presented simple group, given `S1`, the owed char-`p` statement,
`Z1` and `H1`. -/
theorem finitelyGeneratedLinearStatement_routeAV
    (hS1 : Metabelian.Absorption.suslinZLocal_BadStatement) (hV : PolyFpK2VanishingGeTwoStatement)
    (hZ1 : Metabelian.ElemFPCharZero.CharZeroK2SplitGapStatement)
    (hH1 : Metabelian.Envelope.HigmanVCStepBCoreStatement) :
    FinitelyGeneratedLinearStatement :=
  Products.finitelyGeneratedLinearStatement_of_hosts
    (linearHost_of_polyFpEFP hS1 (polynomialFpElementaryFP_of_geTwo hV) hZ1)
    (envelope_routeA hH1)

#audit_axioms GroupApproximation.BooneHigmanLinear.finitelyGeneratedLinearStatement_routeAV

end BooneHigmanLinear
end GroupApproximation
