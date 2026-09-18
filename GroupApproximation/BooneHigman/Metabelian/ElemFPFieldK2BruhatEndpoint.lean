import GroupApproximation.BooneHigman.Metabelian.ElemFPFieldK2BruhatFaithful
import GroupApproximation.BooneHigman.Metabelian.ElemFPFieldK2Statement
import GroupApproximation.Meta.AxiomGuard

/-!
# Symbol generation and `K₂(N, F_p) = 0`, from the big Bruhat cell

Lane `bh-met-55`.  Endpoints, all assuming `BruhatBigCellStatement`
(`ElemFPFieldK2BruhatStatement`):

* `fieldK2_bot_of_bruhatBigCell`: `K2 (Fin N) (ZMod p) = ⊥` for `N ≥ 3`.  An element of `K₂`
  acts trivially on `F_p^N` and lies in the span of all roots `G_univ`.  Hence it is trivial
  (`bruhat_eq_one_of_act`).
* `symbolGeneration_of_bruhatBigCell`: `SymbolGenerationStatement n₀` for every `n₀ ≥ 3`, since
  `⊥` lies below the symbol closure.
* `fieldK2Vanishing_of_bruhatBigCell`: `FieldK2VanishingStatement`, through
  `fieldK2Vanishing_of_symbolGen` at `n₀ = 5`.

Truth check.  `SymbolGenerationStatement 5` is true: `K₂(N, F_p) = 0` for `N ≥ 3`.  Since every
symbol is trivial over `ZMod p` (`symbol_eq_one_zmod`), it is equivalent to `K₂(N, F_p) = 0` for
`N ≥ 5`.  The remaining input `BruhatBigCellStatement` is true for the reason recorded in its
file.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2

open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigman.SteinbergBasic (K2 mem_K2_iff)
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (rootSpan_mono
  mem_rootSpan_true act_of_projection_eq_one)

/-- **`K₂(N, F_p) = 0` for `N ≥ 3`**, from the big Bruhat cell statement. -/
theorem fieldK2_bot_of_bruhatBigCell (hstat : BruhatBigCellStatement) (p : ℕ) [Fact p.Prime]
    (N : ℕ) (hN : 3 ≤ N) : K2 (Fin N) (ZMod p) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  refine bruhat_eq_one_of_act hstat p (Fin N) (by rw [Fintype.card_fin]; exact hN)
    Finset.univ g ?_ (act_of_projection_eq_one ((mem_K2_iff g).mp hg))
  exact rootSpan_mono (p := fun _ _ : Fin N => True)
    (fun i j _ _ => ⟨Finset.mem_univ i, Finset.mem_univ j⟩) (mem_rootSpan_true g)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.fieldK2_bot_of_bruhatBigCell

/-- **Symbol generation** from rank `n₀ ≥ 3`, from the big Bruhat cell statement. -/
theorem symbolGeneration_of_bruhatBigCell (hstat : BruhatBigCellStatement) (n₀ : ℕ)
    (hn₀ : 3 ≤ n₀) : SymbolGenerationStatement n₀ := by
  intro p _ N hN
  have hN3 : 3 ≤ N := le_trans hn₀ hN
  refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, fun e => absurd (congrArg Fin.val e) (by simp), ?_⟩
  rw [fieldK2_bot_of_bruhatBigCell hstat p N hN3]
  exact bot_le

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.symbolGeneration_of_bruhatBigCell

/-- **Target of lane `bh-met-55`**: `SymbolGenerationStatement 5`, from the big Bruhat cell
statement. -/
theorem symbolGeneration_five_of_bruhatBigCell (hstat : BruhatBigCellStatement) :
    SymbolGenerationStatement 5 :=
  symbolGeneration_of_bruhatBigCell hstat 5 (by omega)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.symbolGeneration_five_of_bruhatBigCell

/-- **Bridge** to the field case of `ElemFPK2Split`. -/
theorem fieldK2Vanishing_of_bruhatBigCell (hstat : BruhatBigCellStatement) :
    FieldK2VanishingStatement :=
  fieldK2Vanishing_of_symbolGen (symbolGeneration_five_of_bruhatBigCell hstat)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.fieldK2Vanishing_of_bruhatBigCell

end GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2
