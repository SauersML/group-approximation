import GroupApproximation.GGT.VanKampen.PermFirstReturnComposition
import GroupApproximation.GGT.VanKampen.CombMapEdgeDeletionConnected
import GroupApproximation.GGT.VanKampen.SurgeryReclosedVertices

/-!
# Actual restrictions of combinatorial maps

Keep complete edge pairs and take first return in the vertex rotation. Every
edge-invariant dart subset admits this construction. Restrictions compose and
factor through intermediate retained sets. Both single-edge deletion and the
genuine region reclosure satisfy this interface by their existing proofs;
no connectedness, Euler, or planarity field is added.
-/

namespace GroupApproximation.GGT.VanKampen.CombMap

open Equiv
universe u v w

/-- An embedded map retains whole edges and their actual cyclic vertex order. -/
structure IsRestriction (M : CombMap.{u}) (N : CombMap.{v})
    (e : N.Dart ↪ M.Dart) : Prop where
  alpha_map : ∀ d, e (N.alpha d) = M.alpha (e d)
  sigma_firstReturn : PermFirstReturn.IsFirstReturn M.sigma N.sigma e

namespace IsRestriction

variable {M : CombMap.{u}} {N : CombMap.{v}} {K : CombMap.{w}}
  {e : N.Dart ↪ M.Dart} {f : K.Dart ↪ N.Dart}

theorem trans (hMN : M.IsRestriction N e) (hNK : N.IsRestriction K f) :
    M.IsRestriction K (f.trans e) where
  alpha_map d := (congrArg e (hNK.alpha_map d)).trans (hMN.alpha_map (f d))
  sigma_firstReturn := PermFirstReturn.trans _ _ _ _ _
    hMN.sigma_firstReturn hNK.sigma_firstReturn

/-- If two maps restrict the same ambient rotation and the smaller embeds
in the larger, its rotation is also first return from that intermediate map. -/
theorem of_trans (hMN : M.IsRestriction N e) (hMK : M.IsRestriction K (f.trans e)) :
    N.IsRestriction K f where
  alpha_map d := e.injective ((hMK.alpha_map d).trans (hMN.alpha_map (f d)).symm)
  sigma_firstReturn := PermFirstReturn.of_trans _ _ _ _ _
    hMN.sigma_firstReturn hMK.sigma_firstReturn

theorem vertexOf_eq_iff (h : M.IsRestriction N e) (d d' : N.Dart) :
    N.vertexOf d = N.vertexOf d' ↔ M.vertexOf (e d) = M.vertexOf (e d') := by
  rw [N.vertexOf_eq_iff, M.vertexOf_eq_iff]
  exact PermFirstReturn.sameCycle_iff _ _ _ h.sigma_firstReturn d d'

end IsRestriction

namespace PredicateRestriction

variable (M : CombMap.{u}) (keep : M.Dart → Prop)
  (hkeep : ∀ d, keep (M.alpha d) ↔ keep d)

/-- Edge reversal on the actual retained subtype. -/
def alpha : Perm {d : M.Dart // keep d} where
  toFun d := ⟨M.alpha d.1, (hkeep d.1).mpr d.2⟩
  invFun d := ⟨M.alpha d.1, (hkeep d.1).mpr d.2⟩
  left_inv d := Subtype.ext (M.alpha_involutive d.1)
  right_inv d := Subtype.ext (M.alpha_involutive d.1)

/-- The first-return existence theorem constructs vertex rotation even
when retained points do not form invariant old rotation cycles. -/
noncomputable def sigma : Perm {d : M.Dart // keep d} :=
  Classical.choose (PermFirstReturn.exists_firstReturn M.sigma (Function.Embedding.subtype keep))

theorem sigma_firstReturn : PermFirstReturn.IsFirstReturn M.sigma
    (sigma M keep) (Function.Embedding.subtype keep) :=
  Classical.choose_spec (PermFirstReturn.exists_firstReturn M.sigma (Function.Embedding.subtype keep))

/-- The actual map on any union of edge pairs. -/
noncomputable def toCombMap : CombMap.{u} where
  Dart := {d : M.Dart // keep d}
  dartFintype := Fintype.ofFinite _
  alpha := alpha M keep hkeep
  sigma := sigma M keep
  alpha_involutive d := Subtype.ext (M.alpha_involutive d.1)
  alpha_fixedPointFree d h := M.alpha_fixedPointFree d.1 (congrArg Subtype.val h)

/-- The constructed map supplies both defining conditions of restriction. -/
theorem isRestriction :
    M.IsRestriction (toCombMap M keep hkeep) (Function.Embedding.subtype keep) where
  alpha_map _ := rfl
  sigma_firstReturn := sigma_firstReturn M keep

end PredicateRestriction

end GroupApproximation.GGT.VanKampen.CombMap

namespace GroupApproximation.GGT.VanKampen.EdgeDeletion

open Equiv PermOrbitErasePoint
universe u
variable (M : CombMap.{u}) [DecidableEq M.Dart] (a : M.Dart)

def dartEmbedding : (toCombMap M a).Dart ↪ M.Dart :=
  ⟨value M a, value_injective M a⟩

/-- Actual two-dart deletion is a restriction in the full cyclic-order sense. -/
theorem isRestriction : M.IsRestriction (toCombMap M a) (dartEmbedding M a) where
  alpha_map := alpha_val M a
  sigma_firstReturn := PermFirstReturn.trans M.sigma (erase M.sigma a)
    (erase (erase M.sigma a) (reverseDart M a))
    (Function.Embedding.subtype _) (Function.Embedding.subtype _)
    (firstReturn M.sigma a) (firstReturn (erase M.sigma a) (reverseDart M a))

end GroupApproximation.GGT.VanKampen.EdgeDeletion

namespace GroupApproximation.GGT.VanKampen.Surgery.MapCollapse

universe u

/-- The existing genuine boundary walk makes the reclosed map an actual
restriction; its cyclic order is derived, with no new topology hypothesis. -/
theorem reclosed_isRestriction (M : CombMap.{u}) (faces : Finset M.Face)
    (boundary : BoundaryCycle M faces) (hwalk : boundary.FollowsBoundary) :
    M.IsRestriction (reclosedMap M faces boundary) (Function.Embedding.subtype _) where
  alpha_map _ := rfl
  sigma_firstReturn := reclosed_sigma_firstReturn M faces boundary hwalk

end GroupApproximation.GGT.VanKampen.Surgery.MapCollapse

#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.IsRestriction.of_trans
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.PredicateRestriction.isRestriction
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.isRestriction
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.reclosed_isRestriction
