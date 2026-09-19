import GroupApproximation.BooneHigmanLinear.Tulenbaev.Components
import GroupApproximation.BooneHigmanLinear.PaninAffine.Statements
import GroupApproximation.Meta.AxiomGuard

/-!
# The formal part of Lavrenov–Sinchuk–Voronetsky's Theorem 2.2 (k2-poly piece FORM)

A. Lavrenov, S. Sinchuk, E. Voronetsky, *On the 𝔸¹-invariance of K₂ modeled on linear and even
orthogonal groups*, arXiv:2110.11087, Theorem 2.2. Its final step says the following. Suppose NK
satisfies the Quillen–Suslin local–global principle (their Lemma 2.4), vanishes on fields (their
axiom A5), and at every local ring `R_𝔪` injects into NK of the fraction field (their Cor 2.9).
Then NK vanishes on `R`.

This module states that step for the unstable functor `K₂(r, -)` and proves it. The inputs are:
* the local–global principle `Tulenbaev.StLocalGlobalStatementAt` (lane sk-k2-loc, piece LG);
* NK₂ vanishing over fields, `K2Poly.FieldNKStatement` (piece A5, reduced to `FieldStabAt`,
  lanes k2-field-a/b);
* `NKFieldInjAt`: at a local ring `B`, some injection `ι : B → E` into a field is injective on
  `NK₂`. This is LSV Cor 2.9 with `m = 1`, `E = Frac B`. It is the next residual, from
  `PaninAffine` plus Zariski excision (F.4) and monic injectivity (LSV Lemma 2.7, from H).

Stating `NKFieldInjAt` with an existential field `E` and ring map `ι`, instead of naming
`FractionRing B`, keeps the `Localization` instance diamonds out of the statement.
-/

namespace GroupApproximation.BooneHigmanLinear.K2Poly

open GroupApproximation.BooneHigman
open GroupApproximation.SteinbergGroup

/-- **LSV Cor 2.9 at one ring (`m = 1` form).**  There are a field `E` and a ring map `ι : B → E`
such that an element of `K₂(r, B[X])` killed by `X ↦ 0` and by `ι` is trivial. -/
def NKFieldInjAt (B : Type) [CommRing B] (r : ℕ) : Prop :=
  ∃ (E : Type) (_ : Field E) (ι : B →+* E),
    ∀ u : SteinbergBasic.K2 (Fin r) (Polynomial B),
      SteinbergBasic.K2Map (Polynomial.evalRingHom 0 : Polynomial B →+* B) u = 1 →
        SteinbergGroup.ringMap (Polynomial.mapRingHom ι)
          (u : SteinbergBasic.St r (Polynomial B)) = 1 →
          (u : SteinbergBasic.St r (Polynomial B)) = 1

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.NKFieldInjAt

/-- **Local step.**  Injectivity into a field and `NK₂` vanishing over fields give `NK₂(B) = 1`. -/
theorem unstableNKAt_of_fieldInj {B : Type} [CommRing B] {r : ℕ} (hr : 5 ≤ r)
    (hA5 : FieldNKStatement) (hinj : NKFieldInjAt B r) : UnstableNKAt B r := by
  obtain ⟨E, _, ι, hι⟩ := hinj
  intro u hu
  have hE : UnstableNKAt E r := unstableNKAt_of_fieldConst (hA5 E r hr)
  have hv0 : SteinbergBasic.K2Map (Polynomial.evalRingHom 0 : Polynomial E →+* E)
      (SteinbergBasic.K2Map (Polynomial.mapRingHom ι) u) = 1 := by
    rw [Metabelian.ElemFP.K2Map_K2Map, PaninAffine.evalRingHom_zero_comp_mapRingHom,
      ← Metabelian.ElemFP.K2Map_K2Map, hu, map_one]
  have hv := hE _ hv0
  exact Subtype.ext (hι u hu (congrArg Subtype.val hv))

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.unstableNKAt_of_fieldInj

/-- **LSV Thm 2.2, final step, for `K₂(r, -)`.**  The local–global principle, `NK₂` vanishing at
every localization at a maximal ideal, gives `NK₂(R) = 1`. -/
theorem unstableNKAt_of_local {R : Type} [CommRing R] {r : ℕ} (hr : 5 ≤ r)
    (hLG : Tulenbaev.StLocalGlobalStatementAt 5)
    (hloc : ∀ (M : Ideal R) [M.IsMaximal], UnstableNKAt (Localization.AtPrime M) r) :
    UnstableNKAt R r := by
  intro u hu
  have hu0 : SteinbergGroup.ringMap (Polynomial.evalRingHom 0 : Polynomial R →+* R)
      (u : SteinbergBasic.St r (Polynomial R)) = 1 := congrArg Subtype.val hu
  apply Subtype.ext
  show (u : SteinbergBasic.St r (Polynomial R)) = 1
  have key := hLG R r hr (u : SteinbergBasic.St r (Polynomial R)) (fun M _ => by
    rw [hu0, map_one, map_one]
    have hmem : SteinbergGroup.ringMap
        (Polynomial.mapRingHom (algebraMap R (Localization.AtPrime M)))
        (u : SteinbergBasic.St r (Polynomial R)) ∈
          SteinbergBasic.K2 (Fin r) (Polynomial (Localization.AtPrime M)) :=
      SteinbergBasic.ringMap_mem_K2 _ u.2
    have h0 : SteinbergBasic.K2Map
        (Polynomial.evalRingHom 0 :
          Polynomial (Localization.AtPrime M) →+* Localization.AtPrime M)
        ⟨_, hmem⟩ = 1 := by
      apply Subtype.ext
      show SteinbergGroup.ringMap (Polynomial.evalRingHom 0)
          (SteinbergGroup.ringMap (Polynomial.mapRingHom (algebraMap R (Localization.AtPrime M)))
            (u : SteinbergBasic.St r (Polynomial R))) = 1
      rw [SteinbergBasic.ringMap_ringMap, PaninAffine.evalRingHom_zero_comp_mapRingHom,
        ← SteinbergBasic.ringMap_ringMap, hu0, map_one]
    exact congrArg Subtype.val (hloc M ⟨_, hmem⟩ h0))
  rw [key, hu0, map_one]

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.unstableNKAt_of_local

/-- **The LSV target for `P1` from the three pieces.**  With the local–global principle, `NK₂`
vanishing over fields, and Cor 2.9 at every maximal localization of `K[s₁..s_k]`, unstable
`NK₂(K[s₁..s_k]) = 1` for every `r ≥ 5`.  Take `K = F_p(T)` for `PaninAffine`'s `hInf` input. -/
theorem unstableNKPoly_of_LSV (K : Type) [Field K] (k : ℕ) {r : ℕ} (hr : 5 ≤ r)
    (hLG : Tulenbaev.StLocalGlobalStatementAt 5) (hA5 : FieldNKStatement)
    (hCor29 : ∀ (M : Ideal (MvPolynomial (Fin k) K)) [M.IsMaximal],
      NKFieldInjAt (Localization.AtPrime M) r) :
    UnstableNKAt (MvPolynomial (Fin k) K) r :=
  unstableNKAt_of_local hr hLG fun M _ => unstableNKAt_of_fieldInj hr hA5 (hCor29 M)

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.unstableNKPoly_of_LSV

end GroupApproximation.BooneHigmanLinear.K2Poly
