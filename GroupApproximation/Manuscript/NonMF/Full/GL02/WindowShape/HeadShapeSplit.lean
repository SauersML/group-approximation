import GroupApproximation.Manuscript.NonMF.Full.GL02.RotationTurns
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 04, window shapes: the head shape from a split window

*GL02 copy.*  Re-proof of the foreign module `Piece04.WindowShape.HeadShapeSplit`
(origin/main blob `2b830bed7`), moved to namespace `Piece04.GL02` since the modules it
imports include files last changed by commits marked WIP.  Only namespaces, the imports of
copied modules, and the qualification of foreign names differ from the original.

Two map-level facts behind `HeadShape.windowHeadShape_of_deps`.

* `darts_eq_of_reverseDarts_eq`: if `arc.reverseDarts = L`, then `arc.darts = (L.map α).reverse`.
  Indeed `arc.reverseDarts = arc.darts.reverse.map α`, and `α` is an involution.
* `headShape_of_split`: let `q = (L.map α).reverse`, `L = γc ++ t :: rest` and `T = t :: T'`.
  Then `q = q' ++ α t :: γ` with `q' = (rest.map α).reverse` and `γ = (γc.map α).reverse`.
  If `γc = []`, then `γ = []` and the shape condition is void.  Otherwise `γ.getLast = α w` for
  `w = γc.head`, and, given `σ w = α d` and `φ d = t`,
  `σ (φ (α w)) = σ (σ w) = σ (α d) = φ d = t`,
  using `φ = σ α` (`CombMap.facePerm`) and `α α = id`.  This is `WindowHeadShape M T q`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.WindowShape.HeadShape

universe v

open GroupApproximation.GGT.VanKampen.Embedded

variable {M : CombMap.{v}}

/-- The darts of an arc are its reversed darts, mapped by `α` and reversed. -/
theorem darts_eq_of_reverseDarts_eq {cycle : List M.Dart} (arc : CyclicArc cycle)
    {L : List M.Dart} (h : arc.reverseDarts = L) : arc.darts = (L.map M.alpha).reverse := by
  subst h
  show arc.darts = ((arc.darts.reverse.map M.alpha).map M.alpha).reverse
  rw [List.map_map, M.alpha_involutive.comp_self, List.map_id, List.reverse_reverse]

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.WindowShape.HeadShape.darts_eq_of_reverseDarts_eq

/-- `φ (α w) = σ w`. -/
theorem facePerm_alpha (w : M.Dart) : M.facePerm (M.alpha w) = M.sigma w := by
  rw [CombMap.facePerm, Equiv.Perm.mul_apply, M.alpha_involutive w]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.WindowShape.HeadShape.facePerm_alpha

/-- `σ (α d) = φ d`. -/
theorem sigma_alpha (d : M.Dart) : M.sigma (M.alpha d) = M.facePerm d := by
  rw [CombMap.facePerm, Equiv.Perm.mul_apply]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.WindowShape.HeadShape.sigma_alpha

/-- **The head shape from a split window.**  If `q` is the window `L` reversed and mapped by `α`,
`L = γc ++ t :: rest` and `T = t :: T'`, and either `γc = []` or `γc` starts with `w` where
`σ w = α d` and `φ d = t`, then `T` and `q` have the head shape. -/
theorem headShape_of_split {T L q γc rest T' : List M.Dart} {t : M.Dart}
    (hq : q = (L.map M.alpha).reverse) (hL : L = γc ++ t :: rest) (hT : T = t :: T')
    (hγ : γc = [] ∨ ∃ w d : M.Dart, γc.head? = some w ∧ M.sigma w = M.alpha d ∧
      M.facePerm d = t) :
    RotationTurns.WindowHeadShape M T q := by
  subst hq hL
  refine ⟨t, T', (rest.map M.alpha).reverse, (γc.map M.alpha).reverse, hT, ?_, ?_⟩
  · rw [List.map_append, List.map_cons, List.reverse_append, List.reverse_cons,
      List.append_assoc, List.singleton_append]
  · intro g hg
    rw [List.getLast?_reverse, List.head?_map] at hg
    rcases hγ with rfl | ⟨w, d, hw, hwd, hdt⟩
    · simp at hg
    · rw [hw, Option.map_some] at hg
      have hg' : M.alpha w = g := Option.some.inj hg
      subst hg'
      rw [facePerm_alpha, hwd, sigma_alpha, hdt]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.WindowShape.HeadShape.headShape_of_split

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.WindowShape.HeadShape
