import GroupApproximation.Higman.OmegaHalfLineFiniteHNN
import GroupApproximation.Higman.TorsionFreeImageClosure

/-!
# The finite semantic graph gate for the one-sided Omega construction

The literal right-tail edge is initially written on the infinite free label
group.  This file moves the *restricted graph subgroup itself* into the
finite-rank semantic base `SlimPi m × F₃`.

The key point is that the restriction is taken before the image step.  In the
finitely generated group `F₃ × F₃`, `Star.map_graphHom_eq` identifies it
with the intersection of the fixed paired-return graph and the first-coordinate
right-tail cutter.  Only then do we use `BenignTF.mapEmb`, along the injective
map `(slimPiF3Hom m).prodMap id` whose source is finite rank.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Conj
open GroupApproximation.Higman.Seq

/-- The apparently new tail predicate is the standard support half-line. -/
theorem rightTailSeq_eq_vanishBelow (m : ℕ) :
    rightTailSeq m = vanishBelow (m : ℤ) := by
  ext l
  constructor
  · intro hl i hi
    by_contra hli
    exact (not_le_of_gt hi) (hl i hli)
  · intro hl i hi
    by_contra him
    exact hi (hl i (not_le.mp him))

/-- The exact smaller leaf exposed by the finite-rank semantic reduction. -/
structure RightTailASubInput : Prop where
  benign : ∀ m : ℕ, BenignTF (ASub (rightTailSeq m))

/-- The finite-rank map from the paired-return base to the semantic slim base. -/
noncomputable def slimGraphBaseEmb (m : ℕ) :
    F₃ × F₃ →* SlimPi m × F₃ :=
  (slimPiF3Hom m).prodMap (MonoidHom.id F₃)

@[simp] theorem slimGraphBaseEmb_apply (m : ℕ) (p : F₃ × F₃) :
    slimGraphBaseEmb m p = (slimPiF3Hom m p.1, p.2) := rfl

theorem slimGraphBaseEmb_injective (m : ℕ) :
    Function.Injective (slimGraphBaseEmb m) := by
  intro p q hpq
  change (slimPiF3Hom m p.1, p.2) = (slimPiF3Hom m q.1, q.2) at hpq
  apply Prod.ext
  · apply slimPiF3Hom_injective m
    exact congrArg (fun z : SlimPi m × F₃ => z.1) hpq
  · exact congrArg (fun z : SlimPi m × F₃ => z.2) hpq

/-- The graph map into the semantic base factors through the finite-rank paired
base. -/
theorem slimGraphBaseEmb_comp_graphHom (m : ℕ) :
    (slimGraphBaseEmb m).comp Star.graphHom = slimGraphHom m := by
  ext w <;> rfl

/-- The source graph is the image of an intersection already formed in the
finite-rank paired base. -/
theorem slimRightGraph_eq_map_finiteIntersection (m : ℕ) :
    slimRightGraph m =
      (Star.graphSub ⊓
        (ASub (rightTailSeq m)).prod (⊤ : Subgroup F₃)).map
          (slimGraphBaseEmb m) := by
  rw [← Star.coordSub_bK_map_cbHom (rightTailSeq m),
    ← Star.map_graphHom_eq]
  unfold slimRightGraph
  rw [Subgroup.map_map, slimGraphBaseEmb_comp_graphHom]

/-- **Finite semantic source gate.**  Once the elementary fixed right-tail
conjugate subgroup is supplied, the restricted graph in `SlimPi m × F₃` has
a torsion-free benign witness obtained entirely through finite-rank
intersections and one finite-rank image step. -/
theorem benignTF_finiteRightGraphIntersection_of_rightTail
    (m : ℕ) (hTail : BenignTF (ASub (rightTailSeq m))) :
    BenignTF
      (Star.graphSub ⊓
        (ASub (rightTailSeq m)).prod (⊤ : Subgroup F₃)) := by
  letI : Group.FG (F₃ × F₃) :=
    ProductFinitePresentation.fg_of_isFinitelyPresented (F₃ × F₃)
  have hprod :
      BenignTF ((ASub (rightTailSeq m)).prod (⊤ : Subgroup F₃)) := by
    rw [Star.prod_top_eq_comap_fst]
    exact BenignTF.comap Star.doubleOvergroup (MonoidHom.fst F₃ F₃) hTail
  exact BenignTF.inf PairedReturnCutter.graph_benignTF hprod

end Omega
end Higman
end GroupApproximation
