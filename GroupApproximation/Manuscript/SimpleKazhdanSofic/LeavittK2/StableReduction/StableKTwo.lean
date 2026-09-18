import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.Endpoints
import GroupApproximation.BooneHigman.SteinbergBasic.Kernel
import GroupApproximation.Steinberg.Functoriality
import Mathlib.Data.Fin.Embedding
import GroupApproximation.Meta.AxiomGuard

/-!
# `K₂(5, L) = ⊥` from stable `K₂(L) = 0` and injective stability (lane sk-leavitt-17, part 1)

Let `L = L_{𝔽₂}(1,2)` (`BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)`).  The rank-five gap
`LeavittFP.BinaryLeavittSteinbergInjectiveStatement` (`K₂(Fin 5, L) = ⊥`,
`LeavittFP/Endpoints.lean`) splits into two ingredients of different nature:

* **stable `K₂(L) = 0`** (`BinaryLeavittStableK2TrivialStatement`): every element of an unstable
  `K₂(n, L)` dies in some `St_N(L)`, `N ≥ n`;
* **injective stability from rank five** (`BinaryLeavittK2FiveStabilityStatement`): an element
  of `K₂(5, L)` that dies in some `St_N(L)` is already trivial.

`binaryLeavittSteinbergInjective_of_stable` composes them.  The proof is formal: the element
dies stably, hence it is trivial.

## Interface of lane sk-leavitt-16, stated finitarily

Lane sk-leavitt-16 (running in parallel, not on disk) builds the stable Steinberg group
`St(L) = colim_n St_n(L)` along `stab` and `stableK2 L = ker (St(L) → E(L))`.  This module does
not depend on that colimit.  It uses the finite-stage form of the two statements, which is
equivalent:

* an element of a filtered colimit of groups is trivial iff some finite-stage image is trivial;
* every element of `St(L)` comes from some `St_n(L)`, and it lies in the stable kernel iff its
  projection to `E_n(L)` is trivial, because identity padding `E_n → E_N` is injective
  (`ElementaryPadding.elementaryPad_injective`).

So `stableK2 L = ⊥` is exactly `BinaryLeavittStableK2TrivialStatement`, and "the image of `k` in
`St(L)` is `1`" is exactly `∃ N (h : 5 ≤ N), indexMap (Fin.castLEEmb h) k = 1`.  The iterated
`stab` along `Fin.castSucc` and the single relabelling along `Fin.castLE` agree on the generators
`x_{ij}(a)` (both send them to `x_{ij}(a)` with the same indices), so nothing depends on the choice.

## Truth check

* Stable `K₂(L_k(1,2)) = 0` for every field `k`: Ara–Brustenga–Cortiñas (2009) give the long
  exact sequence `K_*(k) --(1 - 2)--> K_*(k) → K_*(L_k(1,2))`.  Multiplication by `-1` is an
  isomorphism, so `K_*(L) = 0`, in particular `K_2(L) = 0`.
* Injective stability from rank five is true, because `K₂(5, L) = ⊥` (Khanh, arXiv:2609.08428,
  Thm 5.4).  `binaryLeavittK2FiveStability_of_binaryLeavittSteinbergInjective` records the easy
  converse.

**WARNING (carto).**  The stability statement is itself of the depth of the gap: it follows from
the gap in one line.  The value of this module is only to name the two ingredients separately.
Neither is proved in Lean.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

/-- **Stable `K₂(L_{𝔽₂}(1,2)) = 0`**, in finite-stage form (lane sk-leavitt-16's
`stableK2 L = ⊥`).  Every `k ∈ K₂(n, L)` becomes trivial in some `St_N(L)`, `n ≤ N`, under the
relabelling along `Fin.castLE`.

*Why it is true.*  Ara–Brustenga–Cortiñas (2009): `K_*(L_k(1,2)) = 0`.  Not proved in Lean. -/
def BinaryLeavittStableK2TrivialStatement : Prop :=
  ∀ (n : ℕ)
    (k : GroupApproximation.SteinbergGroup (Fin n)
      (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))),
    k ∈ GroupApproximation.BooneHigman.SteinbergBasic.K2 (Fin n)
      (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) →
    ∃ (N : ℕ) (h : n ≤ N), GroupApproximation.SteinbergGroup.indexMap (Fin.castLEEmb h) k = 1

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BinaryLeavittStableK2TrivialStatement

/-- **Injective stability for `K₂` from rank five** over `L_{𝔽₂}(1,2)`, in finite-stage form.
An element of `K₂(5, L)` whose image in some `St_N(L)`, `5 ≤ N`, is trivial is itself trivial.

*Why it is true.*  `K₂(5, L) = ⊥` (Khanh, arXiv:2609.08428, Thm 5.4).  Not proved in Lean. -/
def BinaryLeavittK2FiveStabilityStatement : Prop :=
  ∀ k ∈ GroupApproximation.BooneHigman.SteinbergBasic.K2 (Fin 5)
      (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)),
    ∀ (N : ℕ) (h : 5 ≤ N), GroupApproximation.SteinbergGroup.indexMap (Fin.castLEEmb h) k = 1 →
      k = 1

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BinaryLeavittK2FiveStabilityStatement

/-- **`K₂(5, L) = ⊥` from the two stable ingredients.**  A kernel element dies stably by
`BinaryLeavittStableK2TrivialStatement`, so it is trivial by
`BinaryLeavittK2FiveStabilityStatement`. -/
theorem binaryLeavittSteinbergInjective_of_stable
    (hS : BinaryLeavittStableK2TrivialStatement)
    (hT : BinaryLeavittK2FiveStabilityStatement) :
    GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.BinaryLeavittSteinbergInjectiveStatement := by
  show GroupApproximation.BooneHigman.SteinbergBasic.K2 (Fin 5)
      (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) = ⊥
  refine (Subgroup.eq_bot_iff_forall _).mpr ?_
  intro k hk
  obtain ⟨N, h, hN⟩ := hS 5 k hk
  exact hT k hk N h hN

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.binaryLeavittSteinbergInjective_of_stable

/-- The converse direction for the stability ingredient: `K₂(5, L) = ⊥` gives injective
stability trivially.  This records the carto's warning that the stability statement is of the
depth of the gap. -/
theorem binaryLeavittK2FiveStability_of_binaryLeavittSteinbergInjective
    (h : GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.BinaryLeavittSteinbergInjectiveStatement) :
    BinaryLeavittK2FiveStabilityStatement := by
  have h' : GroupApproximation.BooneHigman.SteinbergBasic.K2 (Fin 5)
      (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) = ⊥ := h
  intro k hk _ _ _
  exact (Subgroup.eq_bot_iff_forall _).mp h' k hk

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.binaryLeavittK2FiveStability_of_binaryLeavittSteinbergInjective

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
