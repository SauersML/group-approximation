import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PullRelStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# The quotient of the relative subgroup by its dying elements

Lane `bh-met-91s`, quotient module.  Notation of lane `bh-met-91g`: `P = A ×_L L[X]`, `L = A_s`,
`K = k2PullRel_ker s M = ker (fst : St(M, P) → St(M, A))`.

* `k2PullAct_dieSt s M`: the elements of `St(M, P)` that die after padding.  A normal subgroup
  (`k2PullAct_dieSt_normal`), by the closure lemmas of `ElemFPK2CubeDiagDilateSt`.
* `k2PullAct_die s M = dieSt ∩ K`, a normal subgroup of `K`.
* `k2PullAct_faithful_mk`: the quotient map `K → K ⧸ die` is `k2PullRel_Faithful`,
  **unconditionally** (its kernel is exactly the dying elements).
* `k2PullAct_actionAt_of_quot`: an action `α` of `St(M, L)` on `K ⧸ die` satisfying
  `Compat`, `F1`, `F2`, `F3` at cofinal levels gives `k2PullRel_ActionAt s`.

This is the witness `H = K ⧸ die` of the action residual, as opposed to the canonical witness
`H = ker (ev₀ : St(M, L[X]) → St(M, L)) ⧸ die` whose faithfulness is `R1`.  Here faithfulness
is free and all the content sits in the construction of `α`.  **No truth claim is made for the
hypothesis of `k2PullAct_actionAt_of_quot` at a fixed level**: it needs `snd (K)` to be
normalised, modulo dying, by `C (St(M, L))` inside `St(M, L[X])` at the same level `M`, which is
a relative-Steinberg (Keune/Loday type) statement not proved here.  It is therefore NOT used as
the residual; it is recorded as infrastructure for a non-circular route.
-/

universe u

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup

section PullActQuot

variable {A : Type u} [CommRing A]

/-- The elements of `St(M, P)` that die after padding. -/
def k2PullAct_dieSt (s : A) (M : ℕ) :
    Subgroup (SteinbergGroup (Fin M) (k2DilateSt_pullback s)) where
  carrier := {g | cubeDiagDilate_StDies g}
  one_mem' := by
    show cubeDiagDilate_StDies (1 : SteinbergGroup (Fin M) (k2DilateSt_pullback s))
    exact cubeDiagDilate_stDies_one
  mul_mem' := by
    intro a b ha hb
    have ha' : cubeDiagDilate_StDies a := ha
    have hb' : cubeDiagDilate_StDies b := hb
    exact cubeDiagDilate_stDies_mul ha' hb'
  inv_mem' := by
    intro a ha
    have ha' : cubeDiagDilate_StDies a := ha
    exact cubeDiagDilate_stDies_inv ha'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullAct_dieSt

theorem k2PullAct_mem_dieSt {s : A} {M : ℕ}
    {g : SteinbergGroup (Fin M) (k2DilateSt_pullback s)} :
    g ∈ k2PullAct_dieSt s M ↔ cubeDiagDilate_StDies g :=
  Iff.rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullAct_mem_dieSt

/-- The dying elements form a normal subgroup. -/
instance k2PullAct_dieSt_normal (s : A) (M : ℕ) : (k2PullAct_dieSt s M).Normal :=
  ⟨fun _ hn g ↦ k2PullAct_mem_dieSt.mpr
    (cubeDiagDilate_stDies_conj g (k2PullAct_mem_dieSt.mp hn))⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullAct_dieSt_normal

/-- The dying elements of the relative subgroup `K`. -/
def k2PullAct_die (s : A) (M : ℕ) : Subgroup (k2PullRel_ker s M) :=
  (k2PullAct_dieSt s M).subgroupOf (k2PullRel_ker s M)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullAct_die

instance k2PullAct_die_normal (s : A) (M : ℕ) : (k2PullAct_die s M).Normal :=
  (k2PullAct_dieSt_normal s M).subgroupOf (k2PullRel_ker s M)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullAct_die_normal

theorem k2PullAct_mem_die {s : A} {M : ℕ} {y : k2PullRel_ker s M} :
    y ∈ k2PullAct_die s M ↔
      cubeDiagDilate_StDies (y : SteinbergGroup (Fin M) (k2DilateSt_pullback s)) :=
  Iff.rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullAct_mem_die

/-- **Faithfulness of the quotient witness**, unconditionally. -/
theorem k2PullAct_faithful_mk (s : A) (M : ℕ) :
    k2PullRel_Faithful (QuotientGroup.mk' (k2PullAct_die s M)) := by
  intro y hy
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hy
  exact k2PullAct_mem_die.mp hy

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullAct_faithful_mk

/-- **Reduction through the quotient witness**: an action on `K ⧸ die` with the root formulas,
at cofinal levels, gives the relative action residual. -/
theorem k2PullAct_actionAt_of_quot {s : A}
    (h : ∀ M₀ : ℕ, ∃ M : ℕ, M₀ ≤ M ∧
      ∃ α : SteinbergGroup (Fin M) (Localization.Away s) →*
          MulAut (↥(k2PullRel_ker s M) ⧸ k2PullAct_die s M),
        k2PullRel_Compat (QuotientGroup.mk' (k2PullAct_die s M)) α ∧
          k2PullRel_F1 (QuotientGroup.mk' (k2PullAct_die s M)) α ∧
            k2PullRel_F2 (QuotientGroup.mk' (k2PullAct_die s M)) α ∧
              k2PullRel_F3 (QuotientGroup.mk' (k2PullAct_die s M)) α) :
    k2PullRel_ActionAt s := by
  intro M₀
  obtain ⟨M, hM, α, hC, h1, h2, h3⟩ := h M₀
  exact ⟨M, hM, ↥(k2PullRel_ker s M) ⧸ k2PullAct_die s M, inferInstance,
    QuotientGroup.mk' (k2PullAct_die s M), α, k2PullAct_faithful_mk s M, hC, h1, h2, h3⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullAct_actionAt_of_quot

end PullActQuot

end GroupApproximation.BooneHigman.Metabelian.ElemFP
