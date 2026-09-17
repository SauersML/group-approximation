import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.KeepUnion
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, inner pocket: the keep-union connectivity statement (lane gl-p07-01)

The interface consumed by the assembly lane gl-p07-15: the map on the edges of three vertex-chained
walks, the second and third touching the first at a vertex, is connected.

* `KeepUnionConnectedStatement`, proved unconditionally by `keepUnionConnectedStatement`
  (from `unionMap_connected`, `KeepUnion.lean`).
* `keepUnion_connected`: the lane-shaped form, with the keep predicate written out and the
  planarity and nonemptiness hypotheses of the lane text.  Those two hypotheses are not needed
  (see the proof in `KeepUnion.lean`) and are carried as unused arguments so that callers written
  against the lane text apply verbatim.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

open SimpleClosedWalkSides

universe u

/-- **Keep-union connectivity.**  For three vertex-chained dart walks of a combinatorial map,
the second and third each starting a dart at a vertex where the first starts a dart, the map on
the union of their edges is connected. -/
def KeepUnionConnectedStatement : Prop :=
  ∀ (M : CombMap.{u}) (c₁ c₂ c₃ : List M.Dart),
    c₁.IsChain (fun d e => M.vertexOf (M.alpha d) = M.vertexOf e) →
    c₂.IsChain (fun d e => M.vertexOf (M.alpha d) = M.vertexOf e) →
    c₃.IsChain (fun d e => M.vertexOf (M.alpha d) = M.vertexOf e) →
    (∃ d ∈ c₂, ∃ e ∈ c₁, M.vertexOf d = M.vertexOf e) →
    (∃ d ∈ c₃, ∃ e ∈ c₁, M.vertexOf d = M.vertexOf e) →
    (CombMap.PredicateRestriction.toCombMap M
      (fun d => walkKeep M c₁ d ∨ walkKeep M c₂ d ∨ walkKeep M c₃ d)
      (keepUnion_alpha M c₁ c₂ c₃)).IsConnected

/-- `KeepUnionConnectedStatement` holds. -/
theorem keepUnionConnectedStatement : KeepUnionConnectedStatement.{u} :=
  fun _ _ _ _ hch₁ hch₂ hch₃ h₂ h₃ => unionMap_connected hch₁ hch₂ hch₃ h₂ h₃

/-- **Lane-shaped form.**  The map on the edges of three touching vertex-chained walks is
connected; planarity and nonemptiness are not used. -/
theorem keepUnion_connected {M : CombMap.{u}} (_hM : M.IsPlanar) {c₁ c₂ c₃ : List M.Dart}
    (_hne : c₁ ≠ [] ∧ c₂ ≠ [] ∧ c₃ ≠ [])
    (hch₁ : c₁.IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e)
    (hch₂ : c₂.IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e)
    (hch₃ : c₃.IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e)
    (h₂ : ∃ d ∈ c₂, ∃ e ∈ c₁, M.vertexOf d = M.vertexOf e)
    (h₃ : ∃ d ∈ c₃, ∃ e ∈ c₁, M.vertexOf d = M.vertexOf e) :
    (CombMap.PredicateRestriction.toCombMap M
      (fun d => walkKeep M c₁ d ∨ walkKeep M c₂ d ∨ walkKeep M c₃ d)
      (keepUnion_alpha M c₁ c₂ c₃)).IsConnected :=
  unionMap_connected hch₁ hch₂ hch₃ h₂ h₃

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.keepUnionConnectedStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.keepUnion_connected
