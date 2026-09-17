import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.Refinement
import GroupApproximation.GGT.VanKampen.CombMapEdgeSteps
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 06: the rotation refinement of a same-corner edge insertion

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Doubling the only dart `d` of a monogon
face inserts an edge from the corner of `d` to itself (`EdgeInsertion.toCombMap M d d`).  The new
rotation `σ'` agrees with `σ` on old darts except at the predecessor `z` of `d`:

* `σ' (embed z) = some none` when `σ z = d` (`sameCorner_sigma_embed_of_eq`),
* `σ' (some none) = none` (`sameCorner_sigma_some_none`),
* `σ' none = embed d` (`sameCorner_sigma_none`),
* `σ' (embed z) = embed (σ z)` otherwise (`sameCorner_sigma_embed_of_ne`).

So an old step `z → σ z` is one new step, or three new steps past the two new darts
(`sameCorner_sigma_three`), and `embed` is a rotation refinement
(`RotationRefinement.sameCorner`).  `RotationRefinement.edgeInsertion` covers distinct corners.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06

universe v

open Equiv PermOrbitInsert

section SameCorner

variable {M : CombMap.{v}}

theorem sameCorner_sigma_embed_of_eq {a z : M.Dart} (ha : M.sigma z = a) :
    (EdgeInsertion.toCombMap M a a).sigma (EdgeInsertion.embed M z) = some none := by
  classical
  change insertBefore (insertBefore M.sigma a) (some a) (some (some z)) = some none
  rw [insertBefore_some, insertBefore_some, ite_cond_eq_true _ _ (eq_true ha)]
  exact ite_cond_eq_false _ _ (eq_false (Option.some_ne_none a).symm)

theorem sameCorner_sigma_embed_of_ne {a z : M.Dart} (ha : M.sigma z ≠ a) :
    (EdgeInsertion.toCombMap M a a).sigma (EdgeInsertion.embed M z) =
      EdgeInsertion.embed M (M.sigma z) := by
  classical
  change insertBefore (insertBefore M.sigma a) (some a) (some (some z)) =
    some (some (M.sigma z))
  rw [insertBefore_some, insertBefore_some, ite_cond_eq_false _ _ (eq_false ha)]
  exact ite_cond_eq_false _ _ (eq_false fun h => ha (Option.some.inj h))

theorem sameCorner_sigma_some_none (a : M.Dart) :
    (EdgeInsertion.toCombMap M a a).sigma (some none) = none := by
  classical
  change insertBefore (insertBefore M.sigma a) (some a) (some none) = none
  rw [insertBefore_some, insertBefore_none]
  exact ite_cond_eq_true _ _ (eq_true rfl)

theorem sameCorner_sigma_none (a : M.Dart) :
    (EdgeInsertion.toCombMap M a a).sigma none = EdgeInsertion.embed M a := by
  change insertBefore (insertBefore M.sigma a) (some a) none = some (some a)
  exact insertBefore_none _ _

/-- **Three new steps at the corner of `a`.** -/
theorem sameCorner_sigma_three {a z : M.Dart} (ha : M.sigma z = a) :
    ((EdgeInsertion.toCombMap M a a).sigma ^ 3) (EdgeInsertion.embed M z) =
      EdgeInsertion.embed M (M.sigma z) := by
  rw [pow_three, Perm.mul_apply, Perm.mul_apply, sameCorner_sigma_embed_of_eq ha,
    sameCorner_sigma_some_none, sameCorner_sigma_none, ha]

theorem sameCorner_sigma_two {a z : M.Dart} (ha : M.sigma z = a) :
    ((EdgeInsertion.toCombMap M a a).sigma ^ 2) (EdgeInsertion.embed M z) = none := by
  rw [pow_two, Perm.mul_apply, sameCorner_sigma_embed_of_eq ha, sameCorner_sigma_some_none]

theorem sameCorner_sigma_one {a z : M.Dart} (ha : M.sigma z = a) :
    ((EdgeInsertion.toCombMap M a a).sigma ^ 1) (EdgeInsertion.embed M z) = some none := by
  rw [pow_one, sameCorner_sigma_embed_of_eq ha]

end SameCorner

namespace RotationRefinement

variable {M : CombMap.{v}}

/-- **An edge from a corner to itself refines the rotation.** -/
noncomputable def sameCorner (a : M.Dart) :
    RotationRefinement M (EdgeInsertion.toCombMap M a a) where
  map := EdgeInsertion.embed M
  injective d e h := Option.some.inj (Option.some.inj h)
  alpha_map _ := rfl
  step z := by
    by_cases ha : M.sigma z = a
    · refine ⟨3, by omega, sameCorner_sigma_three ha, fun t ht ht3 w hw => ?_⟩
      rcases (by omega : t = 1 ∨ t = 2) with rfl | rfl
      · rw [sameCorner_sigma_one ha] at hw
        exact Option.noConfusion (Option.some.inj hw)
      · rw [sameCorner_sigma_two ha] at hw
        exact Option.noConfusion hw
    · refine ⟨1, Nat.one_pos, ?_, fun t ht ht1 => absurd ht1 (by omega)⟩
      rw [pow_one]
      exact sameCorner_sigma_embed_of_ne ha

theorem sameCorner_map (a : M.Dart) :
    (sameCorner a).map = EdgeInsertion.embed M :=
  rfl

end RotationRefinement

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.sameCorner_sigma_three
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.RotationRefinement.sameCorner
