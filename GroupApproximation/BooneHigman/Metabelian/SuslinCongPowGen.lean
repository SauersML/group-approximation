import GroupApproximation.BooneHigman.Metabelian.SuslinCongPowMennicke
import GroupApproximation.Meta.AxiomGuard

/-!
# The Mennicke-closed generator subgroup `suslinCongPow_gen S ≤ GL₂(S)`

Lane `bh-met-92r`.  For a commutative ring `S`, `suslinCongPow_gen S` is the smallest normal
subgroup of `GL₂(S)` that

* contains `E₂(S)`,
* contains every rank-one unipotent `1 + x yᵀ` with `y ⬝ᵥ x = 0`, and
* is **Mennicke closed** (`suslinCongPow_MennickeClosed`): whenever
  `σ₁ = [[a, b₁], [c₁, d₁]]`, `σ₂ = [[a, b₂], [c₂, d₂]]` lie in it and `a d₁ - b₁ c₁ = 1`, so
  does `σ₁₂ = [[a, b₁ b₂], [-c₁ c₂, d₂ - c₂ d₁ b₂]]`.

`suslinCongPow_gen_le` (unconditional, every commutative ring `S`): every element of
`suslinCongPow_gen S` stabilizes into `E₃(S)`.  The Mennicke clause is
`suslinCongPow_stab_mem_mennicke`; the other two clauses are as in `suslinCongLoc_gen_le`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

/-- **Mennicke closure** of a set of invertible `2 × 2` matrices. -/
def suslinCongPow_MennickeClosed {S : Type*} [CommRing S]
    (H : Subgroup (Matrix (Fin 2) (Fin 2) S)ˣ) : Prop :=
  ∀ (σ1 σ2 σ12 : (Matrix (Fin 2) (Fin 2) S)ˣ) (a b1 c1 d1 b2 c2 d2 : S),
    a * d1 - b1 * c1 = 1 →
    (σ1 : Matrix (Fin 2) (Fin 2) S) = !![a, b1; c1, d1] →
    (σ2 : Matrix (Fin 2) (Fin 2) S) = !![a, b2; c2, d2] →
    (σ12 : Matrix (Fin 2) (Fin 2) S) = !![a, b1 * b2; -(c1 * c2), d2 - c2 * d1 * b2] →
    σ1 ∈ H → σ2 ∈ H → σ12 ∈ H

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongPow_MennickeClosed

/-- The smallest normal, Mennicke-closed subgroup of `GL₂(S)` containing `E₂(S)` and the
rank-one unipotents `1 + x yᵀ` (`y ⬝ᵥ x = 0`). -/
def suslinCongPow_gen (S : Type*) [CommRing S] : Subgroup (Matrix (Fin 2) (Fin 2) S)ˣ :=
  sInf {H | H.Normal ∧ elementaryGroup (Fin 2) S ≤ H ∧
    (∀ (σ : (Matrix (Fin 2) (Fin 2) S)ˣ) (x y : Fin 2 → S), y ⬝ᵥ x = 0 →
      (σ : Matrix (Fin 2) (Fin 2) S) = 1 + Matrix.vecMulVec x y → σ ∈ H) ∧
    suslinCongPow_MennickeClosed H}

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongPow_gen

/-- **Every element of `suslinCongPow_gen S` stabilizes into `E₃(S)`**, for every commutative
ring `S` (no hypothesis). -/
theorem suslinCongPow_gen_le (S : Type*) [CommRing S] :
    suslinCongPow_gen S ≤
      (elementaryGroup (Fin 2 ⊕ Unit) S).comap (stabilizeUnit (R := S) (κ := Unit)) := by
  have hE : (elementaryGroup (Fin 2 ⊕ Unit) S).Normal :=
    suslinNormal_elementaryGroup_normal suslinCongLoc_three
  apply sInf_le
  rw [Set.mem_setOf_eq]
  refine ⟨hE.comap _, ?_, ?_, ?_⟩
  · intro σ hσ
    change stabilizeUnit (R := S) (κ := Unit) σ ∈ elementaryGroup (Fin 2 ⊕ Unit) S
    exact (elementaryStabilization (ι := Fin 2) (κ := Unit) (R := S) ⟨σ, hσ⟩).2
  · intro σ x y hyx hσ
    change stabilizeUnit (R := S) (κ := Unit) σ ∈ elementaryGroup (Fin 2 ⊕ Unit) S
    exact suslinCongLoc_stab_mem_rankOne σ x y hyx hσ
  · intro σ1 σ2 σ12 a b1 c1 d1 b2 c2 d2 h1 hσ1 hσ2 hσ12 hx hy
    change stabilizeUnit (R := S) (κ := Unit) σ12 ∈ elementaryGroup (Fin 2 ⊕ Unit) S
    exact suslinCongPow_stab_mem_mennicke σ1 σ2 σ12 h1 hσ1 hσ2 hσ12 hx hy

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongPow_gen_le

/-- Membership in `suslinCongPow_gen S` from membership in every Mennicke-closed subgroup
containing `E₂(S)`. -/
theorem suslinCongPow_mem_gen_of {S : Type*} [CommRing S] {σ : (Matrix (Fin 2) (Fin 2) S)ˣ}
    (h : ∀ H : Subgroup (Matrix (Fin 2) (Fin 2) S)ˣ, elementaryGroup (Fin 2) S ≤ H →
      suslinCongPow_MennickeClosed H → σ ∈ H) :
    σ ∈ suslinCongPow_gen S := by
  rw [suslinCongPow_gen, Subgroup.mem_sInf]
  rintro H ⟨_, hE, _, hM⟩
  exact h H hE hM

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongPow_mem_gen_of

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
