import GroupApproximation.BooneHigman.Metabelian.ElemFPK2KarQuadRelShape
import GroupApproximation.Meta.AxiomGuard

/-!
# The generic four-conjugate case modulo stably short products

Lane `bh-met-93t`, statement module.  `P = k2DilateSt_pullback s`, `A` a domain, `s ≠ 0`.

* `k2KarQuadRel_LongAt s`: `k2KarQuad_GenericAt s` with the extra hypothesis that NO padding of
  `z₁ z₂ z₃ z₄` (to any `M' ≥ M`) is a product of at most three elements of
  `k2KarRel_gens s M'`.
* **`k2KarQuadRel_genericAt_of_longAt`**: `LongAt s → k2KarQuad_GenericAt s` (the excluded
  tuples die by `k2KarQuadRel_stDies_of_short`).  `k2KarQuadRel_longAt_of_genericAt` is the
  trivial converse.
* `k2KarQuadRel_PosLongStatement`, **`k2KarQuadRel_posGeneric_of_posLong`**
  (`→ k2KarQuad_PosGenericStatement`), **`k2KarQuadRel_quad_of_posLong`**
  (`→ k2KarTri_QuadStatement`) and `k2KarQuadRel_posLong_of_pos` (`k2Karoubi_PosStatement →`).

## What is excluded (proved to die)

* Every tuple whose product is TRIVIAL in some `St(M', P)`, e.g. the whole `bh-met-93q`
  non-vacuity family `z₃ = g z₂⁻¹ g⁻¹`, `z₄ = g z₁⁻¹ g⁻¹`, `g = z₁ z₂` (free-group identity,
  `bh-met-93t/truth_check.py`): it is `[].prod`.  So the known witness that
  `k2KarQuad_GenericAt` is non-vacuous is NOT a witness for `LongAt`.
* Every tuple that stably equals a product of at most three relative conjugates, e.g. when
  some `zᵢ z_{i+1}` (or `z₁ ⋯ z₃`, …) is itself stably a relative conjugate, or when the
  product has a stably trivial middle factor `u d v` with `u v` a product of `≤ 3` of `gens`
  (pad until `d = 1`; `k2KarQuadRel_gens_indexMap`).

## LOUD: status

* `LongAt s` is a special case of `k2KarQuad_GenericAt s`; with the proved reduction it is
  **LOGICALLY EQUIVALENT** to it (and so to `k2KarRel_BoundedAt s 4`).  It is **strictly
  smaller in proof content only**: stably short products are proved to die.  It is not
  strictly weaker in logical strength, and it is not claimed to be.
* Truth: **OPEN** here; true if `R1 = k2Karoubi_InjAt s` is (`k2KarQuadRel_posLong_of_pos`).
  Whether `LongAt` is vacuous is also OPEN: a witness needs a stable-length invariant for
  `St(P)`, which is not available here.
* LOUD: the relative commutator shape `k2KarQuadRel_stDies_quad_comm` is proved, but at the
  matrix level it never lies in the generic domain (see `ElemFPK2KarQuadRelShape`).  A proof
  of `LongAt` must use the Steinberg-level information `St(snd) (z₁ z₂ z₃ z₄) = 1`, or the
  structure of `P`: the matrix-level statement for four conjugates is false in general
  (`bh-met-93q`).  `k2KarTri_QuadStatement` and `R1` are NOT closed.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral
open scoped Matrix commutatorElement

section KarQuadRelStatementDef

/-- **The residual**: the generic four-conjugate case, for products that are not stably
products of at most three relative conjugates. -/
def k2KarQuadRel_LongAt {A : Type*} [CommRing A] (s : A) : Prop :=
  ∀ (M : ℕ) (z₁ z₂ z₃ z₄ : SteinbergGroup (Fin M) (k2DilateSt_pullback s)),
    z₁ ∈ k2KarRel_gens s M → z₂ ∈ k2KarRel_gens s M → z₃ ∈ k2KarRel_gens s M →
      z₄ ∈ k2KarRel_gens s M → ringMap (k2PullRel_snd s) (z₁ * z₂ * z₃ * z₄) = 1 →
        ¬ k2KarQuad_PairRankOne (z₁ * z₂) → ¬ k2KarQuad_PairRankOne (z₂ * z₃) →
          (∀ (M' : ℕ) (hM : M ≤ M') (l : List (SteinbergGroup (Fin M') (k2DilateSt_pullback s))),
            l.length ≤ 3 → (∀ z ∈ l, z ∈ k2KarRel_gens s M') →
              l.prod ≠ SteinbergGroup.indexMap (Fin.castLEEmb hM) (z₁ * z₂ * z₃ * z₄)) →
            cubeDiagDilate_StDies (z₁ * z₂ * z₃ * z₄)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarQuadRel_LongAt

/-- The generic case gives the residual (it is a special case). -/
theorem k2KarQuadRel_longAt_of_genericAt {A : Type*} [CommRing A] {s : A}
    (h : k2KarQuad_GenericAt s) : k2KarQuadRel_LongAt s :=
  fun M z₁ z₂ z₃ z₄ h₁ h₂ h₃ h₄ hsnd hp hq _ ↦ h M z₁ z₂ z₃ z₄ h₁ h₂ h₃ h₄ hsnd hp hq

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarQuadRel_longAt_of_genericAt

end KarQuadRelStatementDef

section KarQuadRelStatement

variable {A : Type*} [CommRing A] [IsDomain A] {s : A}

/-- **The reduction**: the residual gives the generic four-conjugate case. -/
theorem k2KarQuadRel_genericAt_of_longAt (hs : s ≠ 0) (h : k2KarQuadRel_LongAt s) :
    k2KarQuad_GenericAt s := by
  intro M z₁ z₂ z₃ z₄ h₁ h₂ h₃ h₄ hsnd hp hq
  by_cases hshort : ∃ (M' : ℕ) (hM : M ≤ M')
      (l : List (SteinbergGroup (Fin M') (k2DilateSt_pullback s))),
      l.length ≤ 3 ∧ (∀ z ∈ l, z ∈ k2KarRel_gens s M') ∧
        l.prod = SteinbergGroup.indexMap (Fin.castLEEmb hM) (z₁ * z₂ * z₃ * z₄)
  · obtain ⟨M', hM, l, hlen, hl, he⟩ := hshort
    exact k2KarQuadRel_stDies_of_short hs hM l hlen hl he hsnd
  · exact h M z₁ z₂ z₃ z₄ h₁ h₂ h₃ h₄ hsnd hp hq fun M' hM l hlen hl he ↦
      hshort ⟨M', hM, l, hlen, hl, he⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarQuadRel_genericAt_of_longAt

end KarQuadRelStatement

section KarQuadRelEndpoint

/-- **The isolated residual (LOUD)**: `k2KarQuadRel_LongAt` over the rings of
`k2Karoubi_PosStatement`.  Equivalent to `k2KarQuad_PosGenericStatement` given the proved
reduction; strictly smaller in proof content only (stably short products are proved to die).
Truth OPEN here (true if `R1` is). -/
def k2KarQuadRel_PosLongStatement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ k : ℕ, 1 ≤ k → ∀ s₀ : MvPolynomial (Fin k) (ZMod p),
    s₀ ≠ 0 → ¬ IsUnit s₀ →
      k2KarQuadRel_LongAt (Polynomial.C s₀ : Polynomial (MvPolynomial (Fin k) (ZMod p)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarQuadRel_PosLongStatement

/-- **Reduction**: the residual gives `k2KarQuad_PosGenericStatement`. -/
theorem k2KarQuadRel_posGeneric_of_posLong (h : k2KarQuadRel_PosLongStatement) :
    k2KarQuad_PosGenericStatement :=
  fun p hp k hk s₀ h0 hu ↦ by
    haveI := Fact.mk hp
    exact k2KarQuadRel_genericAt_of_longAt (Polynomial.C_ne_zero.2 h0) (h p hp k hk s₀ h0 hu)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarQuadRel_posGeneric_of_posLong

/-- **Reduction**: the residual gives `k2KarTri_QuadStatement`. -/
theorem k2KarQuadRel_quad_of_posLong (h : k2KarQuadRel_PosLongStatement) :
    k2KarTri_QuadStatement :=
  k2KarQuad_quad_of_generic (k2KarQuadRel_posGeneric_of_posLong h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarQuadRel_quad_of_posLong

/-- `R1` implies the residual. -/
theorem k2KarQuadRel_posLong_of_pos (h : k2Karoubi_PosStatement) :
    k2KarQuadRel_PosLongStatement :=
  fun p hp k hk s₀ h0 hu ↦
    k2KarQuadRel_longAt_of_genericAt (k2KarQuad_generic_of_pos h p hp k hk s₀ h0 hu)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarQuadRel_posLong_of_pos

end KarQuadRelEndpoint

end GroupApproximation.BooneHigman.Metabelian.ElemFP
