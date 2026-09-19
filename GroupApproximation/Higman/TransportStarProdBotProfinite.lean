import GroupApproximation.Higman.ProfiniteBenignWitness
import GroupApproximation.Higman.TransportStar
import GroupApproximation.Sofic.FreeGroupResiduallyFinite

/-!
# The profinite first-factor witness used by TransportStar

The subgroup `F₃ × 1` is the range of the split first-factor inclusion.
Consequently it is finitely generated and profinitely closed, and its
tautological benign witness carries the full profinite data needed by the
strengthened operation calculus.
-/

namespace GroupApproximation
namespace Higman
namespace Star

noncomputable section

open Conj

/-- The first direct factor, written in the form used by `sup_prod_bot_eq`. -/
abbrev ProdBot : Subgroup (F₃ × F₃) :=
  (⊤ : Subgroup F₃).prod (⊥ : Subgroup F₃)

theorem inl_range_eq_prodBot :
    (MonoidHom.inl F₃ F₃).range = ProdBot := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact Subgroup.mem_prod.mpr
      ⟨Subgroup.mem_top x, Subgroup.one_mem _⟩
  · intro hz
    obtain ⟨-, hz₂⟩ := Subgroup.mem_prod.mp hz
    refine ⟨z.1, ?_⟩
    exact Prod.ext rfl (Subgroup.mem_bot.mp hz₂).symm

/-- Projection onto the first coordinate retracts the first-factor
inclusion. -/
theorem fst_comp_inl :
    (MonoidHom.fst F₃ F₃).comp (MonoidHom.inl F₃ F₃) =
      MonoidHom.id F₃ := by
  ext x
  rfl

theorem prodBot_fg : ProdBot.FG := by
  letI : Group.FG F₃ :=
    ProductFinitePresentation.fg_of_isFinitelyPresented F₃
  exact fg_prod fg_top fg_bot

theorem profiniteClosure_prodBot :
    profiniteClosure ProdBot = ProdBot := by
  rw [← inl_range_eq_prodBot]
  exact profiniteClosure_range_eq_range_of_retraction
    (MonoidHom.inl F₃ F₃) (MonoidHom.fst F₃ F₃) fst_comp_inl

/-- The canonical strengthened benign witness for the fixed first factor. -/
def prodBotWitness : ProfiniteBenignWitness ProdBot :=
  ProfiniteBenignWitness.ofClosedFG prodBot_fg profiniteClosure_prodBot

/-- The particular subgroup joined with `ProdBot` in TransportStar is
exactly the product of the full first factor with the transported output.
This is the semantic reason the special join can be closed on the positive
branch even though no arbitrary join-closedness theorem is possible. -/
theorem special_sup_eq (T : Set ↥K) :
    (Star.graphSub ⊓
        ((Star.coordSub T).map Conj.cbHom).comap
          (MonoidHom.fst F₃ F₃)) ⊔ ProdBot =
      (⊤ : Subgroup F₃).prod ((Star.coordSub T).map Star.evalHom) := by
  rw [← Star.prod_top_eq_comap_fst, ← Star.map_graphHom_eq]
  exact Star.sup_prod_bot_eq T

/-- Closedness of the transported output makes the subgroup cut out by the
special join closed in the original double.  This supplies the necessary
source-side hypothesis for the remaining finite-cover proof of cutter
closedness. -/
theorem special_sup_closed_of_eval_closed (T : Set ↥K)
    (hclosed : profiniteClosure ((Star.coordSub T).map Star.evalHom) =
      (Star.coordSub T).map Star.evalHom) :
    profiniteClosure
        ((Star.graphSub ⊓
            ((Star.coordSub T).map Conj.cbHom).comap
              (MonoidHom.fst F₃ F₃)) ⊔ ProdBot) =
      (Star.graphSub ⊓
          ((Star.coordSub T).map Conj.cbHom).comap
            (MonoidHom.fst F₃ F₃)) ⊔ ProdBot := by
  rw [special_sup_eq]
  have hprod :
      (⊤ : Subgroup F₃).prod ((Star.coordSub T).map Star.evalHom) =
        ((Star.coordSub T).map Star.evalHom).comap
          (MonoidHom.snd F₃ F₃) := by
    ext z
    simp [Subgroup.mem_prod]
  rw [hprod]
  exact profiniteClosure_comap_eq_of_closed
    ((Star.coordSub T).map Star.evalHom) (MonoidHom.snd F₃ F₃) hclosed

/-- Closedness of the literal join cutter would force closedness of the
subgroup it cuts out in `F₃ × F₃`.  Thus a special join proof must use the
actual closed output subgroup; no theorem quantified over an arbitrary left
witness can be valid. -/
theorem sup_closed_of_join_cutterClosed {A : Subgroup (F₃ × F₃)}
    (u : ProfiniteBenignWitness A)
    (hclosed :
      ProfiniteBenignJoin.CutterClosedObligation u prodBotWitness) :
    profiniteClosure (A ⊔ ProdBot) = A ⊔ ProdBot := by
  have hcomap :
      (joinL u.witness prodBotWitness.witness).comap
          (joinEmb₂ u.witness prodBotWitness.witness) =
        A ⊔ ProdBot :=
    comap_joinL u.witness prodBotWitness.witness
  rw [← hcomap]
  exact profiniteClosure_comap_eq_of_closed
    (joinL u.witness prodBotWitness.witness)
    (joinEmb₂ u.witness prodBotWitness.witness) hclosed

end

end Star
end Higman
end GroupApproximation
