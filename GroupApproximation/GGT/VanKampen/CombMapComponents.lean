import GroupApproximation.GGT.VanKampen.CombMapInvariantRestrict
import GroupApproximation.GGT.VanKampen.CombMapRestriction
import GroupApproximation.Meta.AxiomGuard

/-!
# The components of a combinatorial map

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Gluing a copy of a pocket back into a
diagram can split the glued map into several components (`OsinPocketFullArcLakeGlueModel`), and
the transports then remove a spherical component.  This file names the component of a dart and
reads its counts off the invariant restriction `CombMap.restrict` (`CombMapInvariantRestrict`).

The darts joined to `x` by elementary moves form a set closed under edge reversal and vertex
rotation (`componentOf_alpha`, `componentOf_sigma`), so they carry the restricted map
`component M x`, which is connected (`component_connected`).  On an invariant set the first return
of the vertex rotation is the rotation itself, so every invariant restriction is a restriction in
the sense of `CombMap.IsRestriction` (`restrict_isRestriction`).  The vertices, edges, faces and
Euler characteristic of the map are those of a component and of the rest added
(`vertexCount_component_add`, `edgeCount_component_add`, `faceCount_component_add`,
`eulerCharacteristic_component_add`), and a map of Euler characteristic four with a connected rest
has a planar component (`component_planar_of_euler_four`).

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, "Hull's small cancellation theorem", through Osin's
Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.CombMap

universe u

variable (M : CombMap.{u})

/-- **The component of a dart**: the darts joined to it by elementary moves. -/
def componentOf (x : M.Dart) : M.Dart → Prop := Relation.EqvGen M.Adjacent x

theorem componentOf_alpha (x y : M.Dart) : M.componentOf x (M.alpha y) ↔ M.componentOf x y := by
  have h : Relation.EqvGen M.Adjacent y (M.alpha y) := Relation.EqvGen.rel _ _ (Or.inl rfl)
  exact ⟨fun hy => Relation.EqvGen.trans _ _ _ hy (Relation.EqvGen.symm _ _ h),
    fun hy => Relation.EqvGen.trans _ _ _ hy h⟩

theorem componentOf_sigma (x y : M.Dart) : M.componentOf x (M.sigma y) ↔ M.componentOf x y := by
  have h : Relation.EqvGen M.Adjacent y (M.sigma y) := Relation.EqvGen.rel _ _ (Or.inr rfl)
  exact ⟨fun hy => Relation.EqvGen.trans _ _ _ hy (Relation.EqvGen.symm _ _ h),
    fun hy => Relation.EqvGen.trans _ _ _ hy h⟩

theorem componentOf_self (x : M.Dart) : M.componentOf x x := Relation.EqvGen.refl x

/-- **The map on the component of a dart.** -/
noncomputable def component (x : M.Dart) : CombMap.{u} :=
  M.restrict (M.componentOf x) (M.componentOf_alpha x) (M.componentOf_sigma x)

/-- **The map on the darts off the component of a dart.** -/
noncomputable abbrev componentCompl (x : M.Dart) : CombMap.{u} :=
  M.restrict (fun y => ¬ M.componentOf x y) (M.compl_alpha (M.componentOf x) (M.componentOf_alpha x))
    (M.compl_sigma (M.componentOf x) (M.componentOf_sigma x))

/-- **A component is connected.** -/
theorem component_connected (x : M.Dart) : (M.component x).IsConnected :=
  M.restrict_connected (M.componentOf x) (M.componentOf_alpha x) (M.componentOf_sigma x)
    (M.componentOf_self x) fun _ hy => hy

/-- **An invariant restriction is a restriction**: on an invariant set, the first return of the
vertex rotation is the rotation itself. -/
theorem restrict_isRestriction (S : M.Dart → Prop) (hα : ∀ x, S (M.alpha x) ↔ S x)
    (hσ : ∀ x, S (M.sigma x) ↔ S x) :
    M.IsRestriction (M.restrict S hα hσ) (Function.Embedding.subtype S) where
  alpha_map _ := rfl
  sigma_firstReturn b := ⟨1, Nat.one_pos, by rw [pow_one]; rfl, fun k hk hk1 => absurd hk1 (by omega)⟩

/-- **Vertices add up over a component and the rest.** -/
theorem vertexCount_component_add (x : M.Dart) :
    (M.component x).vertexCount + (M.componentCompl x).vertexCount = M.vertexCount :=
  M.vertexCount_restrict_add (M.componentOf x) (M.componentOf_alpha x) (M.componentOf_sigma x)

/-- **Edges add up over a component and the rest.** -/
theorem edgeCount_component_add (x : M.Dart) :
    (M.component x).edgeCount + (M.componentCompl x).edgeCount = M.edgeCount :=
  M.edgeCount_restrict_add (M.componentOf x) (M.componentOf_alpha x) (M.componentOf_sigma x)

/-- **Faces add up over a component and the rest.** -/
theorem faceCount_component_add (x : M.Dart) :
    (M.component x).faceCount + (M.componentCompl x).faceCount = M.faceCount :=
  M.faceCount_restrict_add (M.componentOf x) (M.componentOf_alpha x) (M.componentOf_sigma x)

/-- **Euler characteristics add up over a component and the rest.** -/
theorem eulerCharacteristic_component_add (x : M.Dart) :
    (M.component x).eulerCharacteristic + (M.componentCompl x).eulerCharacteristic =
      M.eulerCharacteristic :=
  M.eulerCharacteristic_restrict_add (M.componentOf x) (M.componentOf_alpha x)
    (M.componentOf_sigma x)

/-- **A component of a map of Euler characteristic four, with a connected rest, is planar.** -/
theorem component_planar_of_euler_four (x : M.Dart) (h4 : M.eulerCharacteristic = 4)
    (hrest : (M.componentCompl x).IsConnected) : (M.component x).IsPlanar :=
  M.restrict_planar_of_euler_four (M.componentOf x) (M.componentOf_alpha x) (M.componentOf_sigma x)
    h4 (M.component_connected x) hrest

end GroupApproximation.GGT.VanKampen.CombMap

#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.componentOf_alpha
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.componentOf_sigma
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.component_connected
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.restrict_isRestriction
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.vertexCount_component_add
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.edgeCount_component_add
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.faceCount_component_add
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.eulerCharacteristic_component_add
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.component_planar_of_euler_four
