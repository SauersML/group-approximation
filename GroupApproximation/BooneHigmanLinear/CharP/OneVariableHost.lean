import GroupApproximation.BooneHigmanLinear.CharP.LowTrdegCoords
import GroupApproximation.BooneHigman.Metabelian.ChainCharP
import GroupApproximation.BooneHigman.Metabelian.AbsorptionEndpoint
import GroupApproximation.BooneHigman.Metabelian.AbsorptionSuslinReduction
import GroupApproximation.BooneHigman.Metabelian.ElemFPBhNagaoWireUncondChain
import GroupApproximation.BooneHigman.Metabelian.ChainWiredAffine
import GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost
import GroupApproximation.Meta.AxiomGuard

/-!
# The characteristic-`p` linear host in transcendence degree at most one

The characteristic-`p` chain `Chain.charPLinearHostStatement_of_chain` takes five inputs. Two of
them, Suslin's `SL_N(F_p[s_0..s_{k-1}]) = E_N` and the finite presentation of
`E_N(F_p[s_0..s_{k-1}])`, are open in general in this development.  For `k ≤ 1` both are
theorems:

* `Absorption.specialLinearInElementary_charPPoly_one`: `SL_N(F_p[s_0]) = E_N` (Euclid);
* `ElemFP.bhNagaoUncond_polynomialFpElementaryFP_le_one`: `E_N(F_p[s_0..s_{k-1}])` is finitely
  presented for `k ≤ 1`, `N ≥ k + 4` (Nagao for `k = 1`).

The other three inputs are theorems for every `k`: the affine extension
(`Chain.affineExtensionFPStatement_holds`), the self-similar tree host
(`CharPHost.TreeHost.charPAffineSelfSimilarStatement_holds`, which needs one variable), and the
coordinates (`LowTrdegCoords.lean`, which also bounds the number of variables).

Results:

* `embedsInFPSelfSimilarGroup_of_glPoly_le_one`: every group embedding in `GL_M(F_p[s])`, in at
  most one variable, embeds in a finitely presented self-similar group;
* `lowTrdegCharPLinearHost`: every finitely generated linear group over a field `K` with
  `trdeg_{F_p} K ≤ 1` embeds in a finitely presented self-similar group.  This is the
  `trdeg ≤ 1` slice of `Chain.CharPLinearHostStatement`, with no hypotheses;
* `lowTrdegCharP_embedsInFinitelyPresentedSimpleGroup`: the matching slice of T3 (Boone–Higman
  for these linear groups), from the envelope statement `Products.FPSelfSimilarEnvelopeStatement`
  alone.  LOUD: that one is conditional on the envelope.
-/

namespace GroupApproximation.BooneHigmanLinear.CharP

open GroupApproximation.BooneHigman
open GroupApproximation.BooneHigman.Metabelian

/-- **One-variable host.**  A group embedding in `GL_M(F_p[s_0, ..., s_{k-1}])` with `k ≤ 1`
embeds in a finitely presented self-similar group. -/
theorem embedsInFPSelfSimilarGroup_of_glPoly_le_one (p : ℕ) [Fact p.Prime] {k : ℕ} (hk : k ≤ 1)
    (M : ℕ) {G : Type*} [Group G]
    {ψ : G →* Matrix.GeneralLinearGroup (Fin M) (MvPolynomial (Fin k) (ZMod p))}
    (hψ : Function.Injective ψ) : Products.EmbedsInFPSelfSimilarGroup G := by
  have hlift : Function.Injective (Matrix.GeneralLinearGroup.map (n := Fin M)
      (MvPolynomial.rename (R := ZMod p) (Fin.castLE hk)).toRingHom) :=
    Coordinates.glMap_injective
      (f := (MvPolynomial.rename (R := ZMod p) (Fin.castLE hk)).toRingHom)
      (MvPolynomial.rename_injective (R := ZMod p) (Fin.castLE hk) (Fin.castLE_injective hk))
  obtain ⟨f, hf⟩ := Absorption.exists_injective_hom_elementaryGroup (Chain.CharPPoly p 1)
    (M := M) (N := 2 * M + 5) (by omega)
    (Absorption.specialLinearInElementary_charPPoly_one p (by omega))
  have hE : Group.IsFinitelyPresented
      (elementaryGroup (Fin (2 * M + 5)) (Chain.CharPPoly p 1)) :=
    ElemFP.bhNagaoUncond_polynomialFpElementaryFP_le_one p Fact.out 1 (2 * M + 5) le_rfl
      (by omega)
  haveI : Group.IsFinitelyPresented
      (Chain.AffineElementaryGroup (2 * M + 5) (Chain.CharPPoly p 1)) :=
    Chain.affineExtensionFPStatement_holds (Chain.CharPPoly p 1)
      (Chain.finiteType_int_transfer _
        (Chain.finiteType_int_of_surjective _ (Chain.charPPoly_map_surjective p 1)) _)
      (2 * M + 5) (by omega) hE
  obtain ⟨X, _, _, ρ, hρ⟩ :=
    CharPHost.TreeHost.charPAffineSelfSimilarStatement_holds p 1 (2 * M + 5) le_rfl (by omega)
  exact Chain.embedsInFPSelfSimilarGroup_of_affineHost (X := X) ρ hρ
    (f := f.comp ((Matrix.GeneralLinearGroup.map (n := Fin M)
      (MvPolynomial.rename (R := ZMod p) (Fin.castLE hk)).toRingHom).comp ψ))
    (hf.comp (hlift.comp hψ))

#audit_axioms
  GroupApproximation.BooneHigmanLinear.CharP.embedsInFPSelfSimilarGroup_of_glPoly_le_one

/-- **The characteristic-`p` linear host in transcendence degree at most one**: every finitely
generated subgroup of `GL_n(K)`, for a field `K` over `F_p` with `trdeg_{F_p} K ≤ 1`, embeds in a
finitely presented self-similar group. -/
def LowTrdegCharPLinearHostStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra (ZMod p) K],
    Algebra.trdeg (ZMod p) K ≤ 1 →
      ∀ (n : ℕ) (H : Subgroup (Matrix.GeneralLinearGroup (Fin n) K)), H.FG →
        Products.EmbedsInFPSelfSimilarGroup H

#audit_axioms GroupApproximation.BooneHigmanLinear.CharP.LowTrdegCharPLinearHostStatement

/-- **The statement holds, with no hypotheses.** -/
theorem lowTrdegCharPLinearHost : LowTrdegCharPLinearHostStatement := by
  intro p _ K _ _ htr n H hH
  obtain ⟨s, M, hs, ψ, hψ⟩ := exists_polynomialCoordinates_le_one p K htr n H hH
  exact embedsInFPSelfSimilarGroup_of_glPoly_le_one p hs M hψ

#audit_axioms GroupApproximation.BooneHigmanLinear.CharP.lowTrdegCharPLinearHost

/-- **The `trdeg ≤ 1` slice of T3, from the envelope statement alone.**  LOUD: conditional on
`Products.FPSelfSimilarEnvelopeStatement` (Zaremsky's envelope theorem, open here). -/
theorem lowTrdegCharP_embedsInFinitelyPresentedSimpleGroup
    (henv : Products.FPSelfSimilarEnvelopeStatement) (p : ℕ) [Fact p.Prime] (K : Type)
    [Field K] [Algebra (ZMod p) K] (htr : Algebra.trdeg (ZMod p) K ≤ 1) (n : ℕ)
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin n) K)) (hH : H.FG) :
    EmbedsInFinitelyPresentedSimpleGroup H :=
  (lowTrdegCharPLinearHost p K htr n H hH).embedsInFinitelyPresentedSimpleGroup henv

#audit_axioms
  GroupApproximation.BooneHigmanLinear.CharP.lowTrdegCharP_embedsInFinitelyPresentedSimpleGroup

end GroupApproximation.BooneHigmanLinear.CharP
