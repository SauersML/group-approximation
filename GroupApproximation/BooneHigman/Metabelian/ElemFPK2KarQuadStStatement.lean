import GroupApproximation.BooneHigman.Metabelian.ElemFPK2KarQuadStCheap
import GroupApproximation.Meta.AxiomGuard

/-!
# The long four-conjugate case modulo the stably datum-cheap case

Lane `bh-met-93w`, statement module.  `P = k2DilateSt_pullback s`, `A` a domain, `s ≠ 0`.

* `k2KarQuadSt_CheapFreeAt s`: `k2KarQuadRel_LongAt s` for tuples whose product is NOT
  `k2KarQuadSt_DatumCheap`; it keeps all hypotheses of `LongAt` (including "not stably a product
  of `≤ 3` relative conjugates") and adds `¬ PairRankOne` for the pairs `(1,3)`, `(2,4)`
  (consequences of `¬ DatumCheap`, recorded for the user).
* **`k2KarQuadSt_longAt_of_cheapFree`**: `CheapFreeAt s → k2KarQuadRel_LongAt s` (the cheap
  tuples die by `k2KarQuadSt_stDies_of_datumCheap`); `k2KarQuadSt_cheapFree_of_longAt` is the
  converse (no domain hypothesis needed).
* `k2KarQuadSt_PosCheapFreeStatement`, **`k2KarQuadSt_posLong_of_posCheapFree`**
  (`→ k2KarQuadRel_PosLongStatement`), **`k2KarQuadSt_quad_of_posCheapFree`**
  (`→ k2KarTri_QuadStatement`) and `k2KarQuadSt_posCheapFree_of_pos`
  (`k2Karoubi_PosStatement →`).

## LOUD: status

* `CheapFreeAt` is logically EQUIVALENT to `LongAt` given the proved reductions (as `LongAt` was
  to `GenericAt`); it is strictly smaller in PROOF CONTENT only: the whole stably datum-cheap
  class is proved to die, in particular every tuple with ONE of `z₁ z₂`, `z₂ z₃`, `z₁ z₃`,
  `z₂ z₄` rank-one (the Hurwitz orbit of the `bh-met-93q` cases; `(1,3)`, `(2,4)` are new and
  meet the generic domain, `bh-met-93w/truth_check.py`), and everything in a conjugacy class
  of a padding of such a product.  Truth OPEN here (true if `R1` is).
* NOTE: every tuple that dies is stably `[].prod`, hence already excluded by the
  "not stably short" hypothesis of `LongAt`; so `LongAt` and `CheapFreeAt` both say that their
  hypotheses are never simultaneously satisfied.  "Strictly smaller" is about which part of that
  vacuity is proved.
* `snd` is used only through `padMat`.  Nothing here uses the non-rank-one calculus, `RankOneAt 3`,
  excision, dilation, homotopy invariance or literature inputs.
* `k2KarTri_QuadStatement` and `R1` are NOT closed.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral
open scoped Matrix commutatorElement

section KarQuadStStatementDef

/-- **The residual**: the long four-conjugate case for products that are not stably
datum-cheap. -/
def k2KarQuadSt_CheapFreeAt {A : Type*} [CommRing A] (s : A) : Prop :=
  ∀ (M : ℕ) (z₁ z₂ z₃ z₄ : SteinbergGroup (Fin M) (k2DilateSt_pullback s)),
    z₁ ∈ k2KarRel_gens s M → z₂ ∈ k2KarRel_gens s M → z₃ ∈ k2KarRel_gens s M →
      z₄ ∈ k2KarRel_gens s M → ringMap (k2PullRel_snd s) (z₁ * z₂ * z₃ * z₄) = 1 →
        ¬ k2KarQuad_PairRankOne (z₁ * z₂) → ¬ k2KarQuad_PairRankOne (z₂ * z₃) →
          ¬ k2KarQuad_PairRankOne (z₁ * z₃) → ¬ k2KarQuad_PairRankOne (z₂ * z₄) →
            ¬ k2KarQuadSt_DatumCheap (z₁ * z₂ * z₃ * z₄) →
              (∀ (M' : ℕ) (hM : M ≤ M')
                  (l : List (SteinbergGroup (Fin M') (k2DilateSt_pullback s))),
                l.length ≤ 3 → (∀ z ∈ l, z ∈ k2KarRel_gens s M') →
                  l.prod ≠ SteinbergGroup.indexMap (Fin.castLEEmb hM) (z₁ * z₂ * z₃ * z₄)) →
                cubeDiagDilate_StDies (z₁ * z₂ * z₃ * z₄)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarQuadSt_CheapFreeAt

/-- The long case gives the residual (it is a special case). -/
theorem k2KarQuadSt_cheapFree_of_longAt {A : Type*} [CommRing A] {s : A}
    (h : k2KarQuadRel_LongAt s) : k2KarQuadSt_CheapFreeAt s :=
  fun M z₁ z₂ z₃ z₄ h₁ h₂ h₃ h₄ hsnd hp hq _ _ _ hshort ↦
    h M z₁ z₂ z₃ z₄ h₁ h₂ h₃ h₄ hsnd hp hq hshort

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarQuadSt_cheapFree_of_longAt

end KarQuadStStatementDef

section KarQuadStStatement

variable {A : Type*} [CommRing A] [IsDomain A] {s : A}

/-- **The reduction**: the residual gives the long four-conjugate case. -/
theorem k2KarQuadSt_longAt_of_cheapFree (hs : s ≠ 0) (h : k2KarQuadSt_CheapFreeAt s) :
    k2KarQuadRel_LongAt s := by
  intro M z₁ z₂ z₃ z₄ h₁ h₂ h₃ h₄ hsnd hp hq hshort
  by_cases hc : k2KarQuadSt_DatumCheap (z₁ * z₂ * z₃ * z₄)
  · exact k2KarQuadSt_stDies_of_datumCheap hs hsnd hc
  · exact h M z₁ z₂ z₃ z₄ h₁ h₂ h₃ h₄ hsnd hp hq
      (fun hr ↦ hc (k2KarQuadSt_datumCheap_of_pair13 hs h₁ h₂ h₃ h₄ hr))
      (fun hr ↦ hc (k2KarQuadSt_datumCheap_of_pair24 hs h₁ h₂ h₃ h₄ hr)) hc hshort

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarQuadSt_longAt_of_cheapFree

end KarQuadStStatement

section KarQuadStEndpoint

/-- **The isolated residual (LOUD)**: `k2KarQuadSt_CheapFreeAt` over the rings of
`k2Karoubi_PosStatement`.  Equivalent to `k2KarQuadRel_PosLongStatement` given the proved
reduction; strictly smaller in proof content only (stably datum-cheap products are proved to
die).  Truth OPEN here (true if `R1` is). -/
def k2KarQuadSt_PosCheapFreeStatement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ k : ℕ, 1 ≤ k → ∀ s₀ : MvPolynomial (Fin k) (ZMod p),
    s₀ ≠ 0 → ¬ IsUnit s₀ →
      k2KarQuadSt_CheapFreeAt (Polynomial.C s₀ : Polynomial (MvPolynomial (Fin k) (ZMod p)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarQuadSt_PosCheapFreeStatement

/-- **Reduction**: the residual gives `k2KarQuadRel_PosLongStatement`. -/
theorem k2KarQuadSt_posLong_of_posCheapFree (h : k2KarQuadSt_PosCheapFreeStatement) :
    k2KarQuadRel_PosLongStatement :=
  fun p hp k hk s₀ h0 hu ↦ by
    haveI := Fact.mk hp
    exact k2KarQuadSt_longAt_of_cheapFree (Polynomial.C_ne_zero.2 h0) (h p hp k hk s₀ h0 hu)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarQuadSt_posLong_of_posCheapFree

/-- **Reduction**: the residual gives `k2KarTri_QuadStatement`. -/
theorem k2KarQuadSt_quad_of_posCheapFree (h : k2KarQuadSt_PosCheapFreeStatement) :
    k2KarTri_QuadStatement :=
  k2KarQuadRel_quad_of_posLong (k2KarQuadSt_posLong_of_posCheapFree h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarQuadSt_quad_of_posCheapFree

/-- `R1` implies the residual. -/
theorem k2KarQuadSt_posCheapFree_of_pos (h : k2Karoubi_PosStatement) :
    k2KarQuadSt_PosCheapFreeStatement :=
  fun p hp k hk s₀ h0 hu ↦
    k2KarQuadSt_cheapFree_of_longAt (k2KarQuadRel_posLong_of_pos h p hp k hk s₀ h0 hu)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarQuadSt_posCheapFree_of_pos

end KarQuadStEndpoint

end GroupApproximation.BooneHigman.Metabelian.ElemFP
