import Mathlib.Algebra.Field.ZMod
import GroupApproximation.BooneHigman.Metabelian.ElemFPFieldK2BruhatAct
import GroupApproximation.Meta.AxiomGuard

/-!
# `St_I(F_p)` acts faithfully, reduced to the big Bruhat cell

Lane `bh-met-55`.  Fix a finite index type `I` with `|I| ≥ 3` and a prime `p`.  For a finset
`K ⊆ I` write `G_K = rootSpan (i ∈ K ∧ j ∈ K)` for the span of the roots inside `K × K`.

**Isolated input (`BruhatBigCellStatement`).**  Take `L ∉ K` and `m ∈ K`.  Take an element
`g ∈ G_{K ∪ {L}}` whose projection has `(L, L)` entry `(g e_L)_L ≠ 0`.  Then
`g = u · s · v · h_mL(c)` with

* `u ∈ U = ⟨x_iL : i ∈ K⟩` (column roots),
* `s ∈ G_K`,
* `v ∈ V = ⟨x_Lj : j ∈ K⟩` (row roots),
* `c ∈ F_p^×`.

**Reduction proved here (`bruhat_eq_one_of_act`).**  If `g ∈ G_K` acts trivially on
`F_p^I`, then `g = 1`.  The proof is Finset induction on `K`.

* For `K = ∅` or `K = {L}` the span has no generating roots.
* Otherwise pick `m ∈ K`.  Then `(g e_L)_L = 1 ≠ 0`, so `g = u s v h_mL(c)`.  Now `h_mL(c) e_L = c⁻¹ e_L`,
  and `v` and `s` fix every vector vanishing on `K`.  Also `u` does not change coordinate `L`.
  Hence `1 = (g e_L)_L = c⁻¹` and `c = 1`.
* Then `u e_L = e_L`, so `u = 1` (`eq_one_of_col_fix_finset`).  Also `(v e_k)_L = (g e_k)_L = 0`
  for `k ≠ L`, so `v = 1` (`eq_one_of_row_zero_finset`).  Now `g = s ∈ G_K` acts trivially,
  and the induction hypothesis applies.

**Truth check of the isolated statement.**  It is true.  `K₂(I, F_p) = 0` for `|I| ≥ 3`
(Steinberg; symbols over finite fields vanish), so `G_{K ∪ {L}}` maps isomorphically onto the
block `SL_{K ∪ {L}}(F_p)`.  A block matrix with `d = g_LL ≠ 0` factors as

  `[[A, b], [c, d]] = [[1, b d⁻¹], [0, 1]] · [[A - b d⁻¹ c, 0], [0, d]] · [[1, 0], [d⁻¹ c, 1]]`.

The middle factor equals `s' · diag(d⁻¹ at m, d at L)` with `s' ∈ SL_K = E_K`.  Moving `h`
past the row factor keeps it inside `V`.  The hypothesis `|I| ≥ 3` is needed: for `|I| = 2`,
`St_2(F_p)` is a free product of two copies of `F_p`, and the factorization fails.

**Why this is strictly smaller.**  The statement asserts a factorization inside the
Steinberg group alone; it says nothing about the action.  The faithfulness argument above
(the diagonal computation, the two faithfulness lemmas of `FieldTwoInjective`, and the
induction on `K`) is the proof content added here.  Deriving the statement from `K₂ = 0` also
needs the matrix LDU factorization and `SL_K(F_p) = E_K(F_p)`, so it is not a restatement.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2

open GroupApproximation.SteinbergGroup
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (h)
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (rootSpan act unitVec
  unitVec_apply act_mul rootSpan_induction act_apply_of_rootSpan act_eq_self_of_rootSpan
  eq_one_of_col_fix_finset eq_one_of_row_zero_finset)

/-- **Big Bruhat cell.**  Take `L ∉ K` and `m ∈ K` in `I`, with `|I| ≥ 3`.  An element of
`G_{K ∪ {L}}` whose projection has `(L, L)` entry nonzero factors as `u · s · v · h_mL(c)`.
Here `u` lies in the column span `⟨x_iL : i ∈ K⟩`, `s ∈ G_K`, and `v` lies in the row span
`⟨x_Lj : j ∈ K⟩`. -/
def BruhatBigCellStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (I : Type) [Fintype I] [DecidableEq I], 3 ≤ Fintype.card I →
    ∀ (K : Finset I) (L m : I), L ∉ K → m ∈ K → ∀ (hmL : m ≠ L)
      (g : SteinbergGroup I (ZMod p)),
      g ∈ rootSpan (R := ZMod p) (fun i j => i ∈ insert L K ∧ j ∈ insert L K) →
      act g (unitVec L) L ≠ 0 →
      ∃ u ∈ rootSpan (R := ZMod p) (fun i j => j = L ∧ i ∈ K),
        ∃ s ∈ rootSpan (R := ZMod p) (fun i j => i ∈ K ∧ j ∈ K),
          ∃ v ∈ rootSpan (R := ZMod p) (fun i j => i = L ∧ j ∈ K),
            ∃ c : (ZMod p)ˣ, g = u * s * v * h m L hmL c

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.BruhatBigCellStatement

/-- A span with no generating roots is trivial: roots inside `{L} × {L}` do not exist. -/
theorem bruhat_rootSpan_singleton_eq_one {p : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (L : I) {g : SteinbergGroup I (ZMod p)}
    (hg : g ∈ rootSpan (R := ZMod p)
      (fun i j => i ∈ insert L (∅ : Finset I) ∧ j ∈ insert L (∅ : Finset I))) : g = 1 := by
  have key : ∀ y : I, y ∈ insert L (∅ : Finset I) → y = L := fun y hy =>
    (Finset.mem_insert.mp hy).resolve_right (Finset.notMem_empty y)
  exact rootSpan_induction (Q := fun g => g = 1)
    (fun i j hij _ hp => absurd ((key i hp.1).trans (key j hp.2).symm) hij) rfl
    (fun g₁ g₂ _ _ h1 h2 => show g₁ * g₂ = 1 by
      rw [show g₁ = 1 from h1, show g₂ = 1 from h2, mul_one]) hg

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhat_rootSpan_singleton_eq_one

/-- Coordinates of `e_L` inside `K` vanish when `L ∉ K`. -/
theorem bruhat_unitVec_eq_zero {p : ℕ} {I : Type} [Fintype I] [DecidableEq I] {K : Finset I}
    {L : I}
    (hLK : L ∉ K) (j : I) (hj : j ∈ K) : unitVec (R := ZMod p) L j = 0 := by
  rw [unitVec_apply, if_neg (fun e : j = L => hLK (by rw [← e]; exact hj))]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhat_unitVec_eq_zero

end GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2
