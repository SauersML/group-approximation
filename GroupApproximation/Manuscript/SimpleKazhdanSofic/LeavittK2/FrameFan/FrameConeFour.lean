import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone.Main
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.ZMod.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# The rank-four frame cone: truth check of `FrameConeFourStatement`

Lane `sk-frame-01`.  Khanh (arXiv:2609.08428v1), tex l.360 (`prop:frame-cone`): "For a finite
family of simplices of $X_r(R)$, each having at most $r-2$ frame vectors, there is a single vector
$v$ extending every frame in the family to a simplex of $X_r(R)$."  Tex l.539 uses it at `r = 4`
for `R = L`, the binary Leavitt algebra.

## Truth check (LOUD)

`FrameFan.FrameConeFourStatement A` (`FrameComplex.lean:152`) is quantified over an arbitrary
ring `A`, and **as a statement about an arbitrary ring it is FALSE**:

* `frameCone4_not_isFrameEdge_self`: over a nontrivial ring no ordered 2-frame `(u,u)` exists
  (if columns `0` and `1` of a unit `g` agree, then `(g⁻¹ g)_{00} = (g⁻¹ g)_{01}`, i.e. `1 = 0`).
* `frameCone4_not_statement_of_finite`: if `A` is finite and nontrivial, list *all* frame
  vertices as `vs`; the apex `c` is one of them, so `(c,c)` would be a 2-frame.  Contradiction.
* `frameCone4_not_statement_zmod_two`: the explicit instance `A = 𝔽₂`.

Khanh's proposition is only claimed for `R = L` (which is infinite), and there the statement is
TRUE and already proved unconditionally in the corpus as
`FrameCone.binaryLeavittFrameConeFour : FrameFan.BinaryLeavittFrameConeFourStatement`
(`FrameCone/Main.lean`, from lane 08's word multiplier `exists_word_multiplier`).

## Endpoints

* `frameCone4_binaryLeavitt`: `FrameConeFourStatement L`, unconditional (re-export).
* `frameCone4_binaryLeavitt_simplyConnected`: `X_4(L)` is simply connected, unconditional
  (the `_of_frameConeFour` fan of `FrameComplex.lean` fed with the cone).
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameFan

/-- Over a nontrivial ring no invertible `4 × 4` matrix has two equal first columns, so `(u,u)`
is never an ordered 2-frame. -/
theorem frameCone4_not_isFrameEdge_self {A : Type*} [Ring A] [Nontrivial A] (u : Fin 4 → A) :
    ¬ IsFrameEdge A u u := by
  rintro ⟨g, hg⟩
  have h1 : (((g⁻¹ : (Matrix (Fin 4) (Fin 4) A)ˣ) : Matrix (Fin 4) (Fin 4) A) *
        (g : Matrix (Fin 4) (Fin 4) A)) 0 0 =
      (((g⁻¹ : (Matrix (Fin 4) (Fin 4) A)ˣ) : Matrix (Fin 4) (Fin 4) A) *
        (g : Matrix (Fin 4) (Fin 4) A)) 0 1 := by
    simp only [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [(hg k).1, (hg k).2]
  rw [g.inv_mul, Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 4) ≠ 1)] at h1
  exact one_ne_zero h1

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameFan.frameCone4_not_isFrameEdge_self

/-- **The generic statement is false.**  Over a finite nontrivial ring, the cone apex of the list
of all frame vertices would be joined to itself by a 2-frame. -/
theorem frameCone4_not_statement_of_finite (A : Type*) [Ring A] [Finite A] [Nontrivial A] :
    ¬ FrameConeFourStatement A := by
  intro h
  haveI : Fintype (FrameVertex A) := Fintype.ofFinite _
  obtain ⟨c, hc, -⟩ := h (Finset.univ : Finset (FrameVertex A)).toList []
    (fun _ hx => by simp at hx)
  exact frameCone4_not_isFrameEdge_self c.1 (hc c (Finset.mem_toList.2 (Finset.mem_univ c)))

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameFan.frameCone4_not_statement_of_finite

/-- The explicit counterexample `A = 𝔽₂`. -/
theorem frameCone4_not_statement_zmod_two : ¬ FrameConeFourStatement (ZMod 2) := by
  haveI : Fact (1 < 2) := ⟨by decide⟩
  exact frameCone4_not_statement_of_finite (ZMod 2)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameFan.frameCone4_not_statement_zmod_two

/-- **Khanh Prop 4.2 at `r = 4` over `L = L_𝔽₂(1,2)`**, in the vertex/edge form, unconditional:
the corpus proof `FrameCone.binaryLeavittFrameConeFour` (lane 08 word multiplier). -/
theorem frameCone4_binaryLeavitt :
    FrameConeFourStatement (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) :=
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone.binaryLeavittFrameConeFour

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameFan.frameCone4_binaryLeavitt

/-- Tex l.539, unconditional: `X_4(L)` (on frame vertices) is connected and simply connected. -/
theorem frameCone4_binaryLeavitt_simplyConnected :
    (frameComplexFour
      (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))).SimplyConnected :=
  binaryLeavitt_frameComplexFour_simplyConnected_of_frameConeFour frameCone4_binaryLeavitt

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameFan.frameCone4_binaryLeavitt_simplyConnected

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameFan
