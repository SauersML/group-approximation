import GroupApproximation.BooneHigman.Metabelian.ElemFPK2SurjStabFactorCore
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2SurjStabEndpoint
import GroupApproximation.Meta.AxiomGuard

/-!
# Surjective `K₂` stability: `P Q P` from a disjoint `P V U V H` factorization (bh-met-65c)

Target: `SurjStabConjTripleStatement`.  Every `x ∈ K₂(n+1, ℤ[1/m])` (`m > 0`, `n ≥ 4`) has a
conjugate in `P Q P`.  Here `P = stab St_n · padCol R^n` and `Q = stab St_n · padRow R^n`.

## Truth check

The target is TRUE.  `ℤ[1/m]` is Dedekind, so `sr ≤ 2`, and the Dennis / van der Kallen surjective
stability theorem gives `K₂(n) ↠ K₂(n+1)` for `n ≥ 3`.  This is equivalent to the target
(`surjStabConjTriple_of_surj`).  A proof outright would need the van der Kallen factorization
argument, which is not in the repo.  One cannot drop the conjugation: over `ℤ`,
`diag(1, …, 1, -1, -1)` is not in the matrix image of `P Q P`.

## What is proved (any unital ring `R`)

`surjStabFactor_conjTriple_of_disj`: if `x ∈ K₂(n+1)` and
`z x z⁻¹ = stab g₁ · padCol v · padRow w · padCol c · padRow w' · stab g₂` with `c`, `w` of
disjoint support, then `x` has a `P Q P` conjugate.

1. Conjugating by `stab g₂` gives `y = stab (g₂ g₁) · padCol v · padRow w · padCol c · padRow w'`,
   and `y ∈ K₂`.
2. The last row `e = (0, 1)` is fixed by `padMat y = 1`.  It passes through `stab`, `padCol v`,
   `padRow w` (giving `(w, 1)`), `padCol c` (fixed by disjointness), and `padRow w'` (giving
   `(w + w', 1)`).  Hence `w' = -w`.
3. The Steinberg core (`surjStabFactor_conj_row_padCol_mem`, from `⁅x_{i,L}, x_{L,j}⁆ = x_{ij}`)
   gives `padRow w · padCol c · padRow w⁻¹ ∈ P`.  So `y ∈ P`, a degenerate `P Q P` element.

## Remaining gap

`SurjStabFactorDisjStatement`: every such `x` has a conjugate
`stab g₁ · padCol v · padRow w · padCol c · padRow w' · stab g₂` with `c`, `w` disjointly
supported.

LOUD: this is logically EQUIVALENT to the target, and hence to `hsurj`.  The converse
`surjStabFactorDisjStatement_of_conjTriple` is proved below, through `hsurj`, with
`z = 1`, `g₂ = 1` and `v = w = c = w' = 0`.  Every candidate gap is equivalent in this sense,
because both sides are theorems.

It is strictly SMALLER in proof content.  The gap asks for a factorization with five free
factors and no `K₂` bookkeeping.  The target instead needs the resulting element to be
arranged as `P Q P`, which is exactly the last-row argument and the
`x_{L,j} x_{i,L} x_{L,j}⁻¹ = x_{ij}⁻¹ x_{i,L}` elimination proved here.  What is left is the
van der Kallen / `sr ≤ 2` Gauss step: write a conjugate of a relation as a product of the
elementary factors above, arranging the supports of `c` and `w` to be disjoint.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open scoped Matrix
open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral

variable {R : Type*} [Ring R] {n : ℕ}

/-- `x` has a conjugate `stab g₁ · padCol v · padRow w · padCol c · padRow w' · stab g₂` with
`c` and `w` of disjoint support. -/
def SurjStabFactorDisj (x : St (n + 1) R) : Prop :=
  ∃ (z : St (n + 1) R) (g₁ g₂ : St n R) (v w c w' : Fin n → R), (∀ i, c i = 0 ∨ w i = 0) ∧
    z * x * z⁻¹ = stab n R g₁ * padCol v * padRow w * padCol c * padRow w' * stab n R g₂

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.SurjStabFactorDisj

/-- Disjoint `P V U V H` conjugate of a `K₂` element gives a `P Q P` conjugate (any ring). -/
theorem surjStabFactor_conjTriple_of_disj {x : St (n + 1) R} (hx : x ∈ K2 (Fin (n + 1)) R)
    (h : SurjStabFactorDisj x) : SurjStabConjTriple x := by
  obtain ⟨z, g₁, g₂, v, w, c, w', hd, hz⟩ := h
  have hN : (K2 (Fin (n + 1)) R).Normal := inferInstance
  have hyK : z * x * z⁻¹ ∈ K2 (Fin (n + 1)) R := hN.conj_mem x hx z
  have e : stab n R g₂ * (z * x * z⁻¹) * (stab n R g₂)⁻¹ =
      stab n R (g₂ * g₁) * padCol v * padRow w * padCol c * padRow w' := by
    rw [hz, map_mul (stab n R) g₂ g₁]
    simp only [mul_assoc, mul_inv_cancel, mul_one]
  have hk : stab n R (g₂ * g₁) * padCol v * padRow w * padCol c * padRow w' ∈
      K2 (Fin (n + 1)) R := by
    rw [← e]
    exact hN.conj_mem _ hyK _
  have hrow : surjStabVec (0 : Fin n → R) (1 : R) ᵥ*
      padMat (stab n R (g₂ * g₁) * padCol v * padRow w * padCol c * padRow w') =
        surjStabVec 0 1 := by
    rw [padMat_of_mem_K2 hk, Matrix.vecMul_one]
  simp only [map_mul, ← Matrix.vecMul_vecMul] at hrow
  rw [surjStab_vecMul_stab, surjStab_vecMul_stab, surjStab_vecMul_padCol, surjStab_vecMul_padRow,
    zero_add, surjStabFactor_vecMul_padCol_disj c w hd, surjStab_vecMul_padRow] at hrow
  have hw : w + w' = 0 := surjStabVec_inj hrow
  have hinv : padRow w' = (padRow w)⁻¹ :=
    eq_inv_of_mul_eq_one_right (by rw [← padRow_add, hw, padRow_zero])
  have hy : stab n R (g₂ * g₁) * padCol v * padRow w * padCol c * padRow w' =
      stab n R (g₂ * g₁) * padCol v * (padRow w * padCol c * (padRow w)⁻¹) := by
    rw [hinv]
    simp only [mul_assoc]
  obtain ⟨g', v', hg'⟩ := surjStabFactor_inPar_mul (surjStabFactor_inPar_of (g₂ * g₁) v)
    (surjStabFactor_conj_row_padCol_mem w c hd)
  refine ⟨stab n R g₂ * z, g', 1, 1, v', 0, 0, ?_⟩
  simp only [map_one, padRow_zero, padCol_zero, mul_one]
  rw [← hg', ← hy, ← e]
  simp only [mul_inv_rev, mul_assoc]

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabFactor_conjTriple_of_disj

/-- Trivial converse: an element of `stab K₂(n)` has a disjoint factorization. -/
theorem surjStabFactor_disj_of_mem_map {x : St (n + 1) R}
    (hx : x ∈ (K2 (Fin n) R).map (stab n R)) : SurjStabFactorDisj x := by
  obtain ⟨k, _, rfl⟩ := Subgroup.mem_map.mp hx
  refine ⟨1, k, 1, 0, 0, 0, 0, fun _ => Or.inl rfl, ?_⟩
  simp only [padCol_zero, padRow_zero, map_one, mul_one, one_mul, inv_one]

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabFactor_disj_of_mem_map

/-- **Remaining gap**: every `K₂` element over `ℤ[1/m]` (`m > 0`, `n ≥ 4`) has a disjoint
`P V U V H` conjugate. -/
def SurjStabFactorDisjStatement : Prop :=
  ∀ m n : ℕ, 0 < m → 4 ≤ n → ∀ x ∈ K2 (Fin (n + 1)) (Localization.Away (m : ℤ)),
    SurjStabFactorDisj x

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.SurjStabFactorDisjStatement

/-- **Endpoint**: the `P Q P` statement from the disjoint factorization statement. -/
theorem surjStabConjTriple_of_surjStabFactorDisj (h : SurjStabFactorDisjStatement) :
    SurjStabConjTripleStatement :=
  fun m n hm hn x hx => surjStabFactor_conjTriple_of_disj hx (h m n hm hn x hx)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabConjTriple_of_surjStabFactorDisj

/-- LOUD equivalence: the gap follows back from the target, through `hsurj`. -/
theorem surjStabFactorDisjStatement_of_conjTriple (h : SurjStabConjTripleStatement) :
    SurjStabFactorDisjStatement :=
  fun m n hm hn _ hx =>
    surjStabFactor_disj_of_mem_map (charZeroK2SurjStab_of_conjTriple h m n hm hn hx)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabFactorDisjStatement_of_conjTriple

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
