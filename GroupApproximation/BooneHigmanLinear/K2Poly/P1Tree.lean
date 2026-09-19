import GroupApproximation.BooneHigmanLinear.K2Poly.FieldNK
import GroupApproximation.BooneHigmanLinear.K2Poly.LSVForm
import GroupApproximation.BooneHigmanLinear.PaninAffine.Statements
import GroupApproximation.Meta.AxiomGuard

/-!
# P1 from its named open inputs: the K₂ program tree in one statement

k2-poly (lane bh-pal-wire, lead). Route A's input P1, i.e. `PolyK2NilGapStatementOver (ZMod p) 4`
for every prime `p`, follows from five named inputs. Each is a board piece with an owner:

* `hLG`: Tulenbaev's local–global principle `Tulenbaev.StLocalGlobalStatementAt 5` (A2/LG);
* `hC`: the coset step `FieldNF.FieldCosetAt F` at every field (A5.2), which gives A5 through
  `fieldNK_of_fieldCoset`, since A5.1 is proved;
* `hCor29`: LSV Cor 2.9 `NKFieldInjAt` at the maximal localizations of `K[s₁..s_k]`, for every
  infinite field `K`;
* `hFin`: the finitary descent `PaninAffine.RatFuncFinitaryAt` (A1/F.5);
* `hH`: Horrocks for monic polynomials, `HorrocksMonicAt` over `F_p[s][X]` (A4/H.b).

The route: LSV Theorem 2.2 over `K = F_p(T)` (`unstableNKPoly_of_LSV`), then k2-panin's
reduction A (`PaninAffine.unstableNKPolyFp_of_ratFunc`), then `gapOver_of_unstableNK`.
-/

namespace GroupApproximation.BooneHigmanLinear.K2Poly

/-- `F_p(T)` is infinite. -/
theorem ratFunc_zmod_infinite (p : ℕ) [Fact p.Prime] : Infinite (RatFunc (ZMod p)) :=
  Infinite.of_injective _ (RatFunc.algebraMap_injective (K := ZMod p))

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.ratFunc_zmod_infinite

/-- **The unstable `NK₂` target** `UnstableNKPolyFpStatement` from the five named inputs. -/
theorem unstableNKPolyFp_of_inputs (hLG : Tulenbaev.StLocalGlobalStatementAt 5)
    (hC : ∀ (F : Type) [Field F], FieldNF.FieldCosetAt F)
    (hCor29 : ∀ (K : Type) [Field K] [Infinite K] (k r : ℕ), 5 ≤ r →
      ∀ (M : Ideal (MvPolynomial (Fin k) K)) [M.IsMaximal],
        NKFieldInjAt (Localization.AtPrime M) r)
    (hFin : ∀ (p : ℕ) [Fact p.Prime] (k r : ℕ), 5 ≤ r → PaninAffine.RatFuncFinitaryAt (ZMod p) k r)
    (hH : ∀ (p : ℕ) [Fact p.Prime] (k r : ℕ), 5 ≤ r →
      HorrocksMonicAt (Polynomial (MvPolynomial (Fin k) (ZMod p))) r) :
    UnstableNKPolyFpStatement :=
  PaninAffine.unstableNKPolyFp_of_ratFunc
    (fun p _ k r hr =>
      haveI := ratFunc_zmod_infinite p
      unstableNKPoly_of_LSV (RatFunc (ZMod p)) k hr hLG (fieldNK_of_fieldCoset hC)
        (hCor29 (RatFunc (ZMod p)) k r hr))
    hFin hH

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.unstableNKPolyFp_of_inputs

/-- **Route A's P1** from the five named inputs. -/
theorem gapOver_of_inputs (hLG : Tulenbaev.StLocalGlobalStatementAt 5)
    (hC : ∀ (F : Type) [Field F], FieldNF.FieldCosetAt F)
    (hCor29 : ∀ (K : Type) [Field K] [Infinite K] (k r : ℕ), 5 ≤ r →
      ∀ (M : Ideal (MvPolynomial (Fin k) K)) [M.IsMaximal],
        NKFieldInjAt (Localization.AtPrime M) r)
    (hFin : ∀ (p : ℕ) [Fact p.Prime] (k r : ℕ), 5 ≤ r → PaninAffine.RatFuncFinitaryAt (ZMod p) k r)
    (hH : ∀ (p : ℕ) [Fact p.Prime] (k r : ℕ), 5 ≤ r →
      HorrocksMonicAt (Polynomial (MvPolynomial (Fin k) (ZMod p))) r) :
    ∀ p : ℕ, p.Prime → BooneHigman.Metabelian.ElemFP.PolyK2NilGapStatementOver (ZMod p) 4 :=
  gapOver_of_unstableNK (unstableNKPolyFp_of_inputs hLG hC hCor29 hFin hH)

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.gapOver_of_inputs

end GroupApproximation.BooneHigmanLinear.K2Poly
