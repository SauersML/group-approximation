import GroupApproximation.GGT.VanKampen.Estimating.Deletion
import GroupApproximation.Meta.AxiomGuard

/-!
# Euler's edge bound for simple planar maps, including trees

A connected simple map can have a face of degree two: the map consisting of
one edge. Requiring every face to have degree at least three therefore excludes
a legitimate component of an estimating graph (#203). We prove the Euler bound
from the actual absence of loops and multiple edges, handling that exception
directly. Isolated vertices are still outside the dart-only map representation
and must be counted separately when assembling components.
-/

namespace GroupApproximation.GGT.VanKampen.CombMap

universe v

/-- The two darts of each edge belong to different vertices. -/
def IsLoopless (M : CombMap.{v}) : Prop :=
  ∀ d : M.Dart, M.vertexOf d ≠ M.vertexOf (M.alpha d)

/-- Two oriented edges with the same endpoints represent the same edge. -/
def HasNoMultipleEdges (M : CombMap.{v}) : Prop :=
  ∀ d e : M.Dart, M.vertexOf d = M.vertexOf e →
    M.vertexOf (M.alpha d) = M.vertexOf (M.alpha e) →
      M.edgeOf d = M.edgeOf e

variable (M : CombMap.{v})

/-- A planar dart map has a vertex. An empty vertex quotient would make its
dart, edge, and face types empty, contradicting Euler characteristic two. -/
theorem vertexCount_pos_of_planar (hplanar : M.IsPlanar) :
    0 < M.vertexCount := by
  classical
  by_contra hpos
  have hz : M.vertexCount = 0 := by omega
  haveI : IsEmpty M.Vertex := Fintype.card_eq_zero_iff.mp (by
    simpa only [vertexCount, Nat.card_eq_fintype_card] using hz)
  haveI : IsEmpty M.Dart := ⟨fun d => isEmptyElim (M.vertexOf d)⟩
  have h := hplanar.2
  simp [eulerCharacteristic, vertexCount, edgeCount, faceCount] at h

/-- A one-step face cycle would be a loop. -/
theorem facePerm_ne_self_of_loopless (hloop : M.IsLoopless) (d : M.Dart) :
    M.facePerm d ≠ d := by
  intro h
  apply hloop d
  calc
    M.vertexOf d = M.vertexOf (M.facePerm d) := congrArg M.vertexOf h.symm
    _ = M.vertexOf (M.alpha d) := M.vertexOf_sigma _

/-- A two-step face cycle in a simple map traverses one edge out and back;
both of its endpoint rotations are fixed. -/
theorem sigma_fixed_of_facePerm_twoCycle
    (hloop : M.IsLoopless) (hmulti : M.HasNoMultipleEdges)
    (d : M.Dart) (htwo : M.facePerm (M.facePerm d) = d) :
    M.sigma d = d ∧ M.sigma (M.alpha d) = M.alpha d := by
  have hne := M.facePerm_ne_self_of_loopless hloop d
  have hedge : M.edgeOf (M.facePerm d) = M.edgeOf (M.alpha d) := by
    apply hmulti
    · exact M.vertexOf_sigma _
    · calc
        M.vertexOf (M.alpha (M.facePerm d)) =
            M.vertexOf (M.facePerm (M.facePerm d)) := (M.vertexOf_sigma _).symm
        _ = M.vertexOf d := congrArg M.vertexOf htwo
        _ = M.vertexOf (M.alpha (M.alpha d)) := by rw [M.alpha_involutive]
  have hface : M.facePerm d = M.alpha d := by
    rcases (M.edgeOf_eq_iff _ _).mp hedge with h | h
    · exact h
    · exact (hne (M.alpha.injective h)).elim
  constructor
  · have h := htwo
    rw [hface] at h
    change M.sigma (M.alpha (M.alpha d)) = d at h
    rw [M.alpha_involutive] at h
    exact h
  · exact hface

/-- In a connected map, an edge whose two endpoints have degree one is the
whole map. This is the exceptional tree component in the face-degree proof. -/
theorem dart_eq_or_alpha_of_fixed_endpoints
    (hconnected : M.IsConnected) (d : M.Dart)
    (hd : M.sigma d = d) (ha : M.sigma (M.alpha d) = M.alpha d)
    (x : M.Dart) : x = d ∨ x = M.alpha d := by
  let P : M.Dart → Prop := fun y => y = d ∨ y = M.alpha d
  have halpha : ∀ y, P (M.alpha y) ↔ P y := by
    intro y
    constructor
    · rintro (h | h)
      · right
        exact (M.alpha_involutive y).symm.trans (congrArg M.alpha h)
      · left
        exact M.alpha.injective h
    · rintro (rfl | rfl)
      · exact Or.inr rfl
      · exact Or.inl (M.alpha_involutive d)
  have hsigma : ∀ y, P (M.sigma y) ↔ P y := by
    intro y
    constructor
    · rintro (h | h)
      · exact Or.inl (M.sigma.injective (h.trans hd.symm))
      · exact Or.inr (M.sigma.injective (h.trans ha.symm))
    · rintro (rfl | rfl)
      · exact Or.inl hd
      · exact Or.inr ha
  have hmove : ∀ a b, M.Adjacent a b → (P a ↔ P b) := by
    intro a b h
    rcases h with rfl | rfl
    · exact (halpha a).symm
    · exact (hsigma a).symm
  have hclosure : ∀ a b, Relation.EqvGen M.Adjacent a b → (P a ↔ P b) := by
    intro a b h
    induction h with
    | rel a b h => exact hmove a b h
    | refl a => rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  exact (hclosure d x (hconnected d x)).mp (Or.inl rfl)

/-- If the first three darts of a face orbit are distinct, the face has
degree at least three. -/
theorem faceDegree_ge_three_of_not_twoCycle
    (hloop : M.IsLoopless) (d : M.Dart)
    (htwo : M.facePerm (M.facePerm d) ≠ d) :
    3 ≤ M.faceDegree (M.faceOf d) := by
  classical
  let fibre : Finset M.Dart := Finset.univ.filter (fun x => M.faceOf x = M.faceOf d)
  have hsub : ({d, M.facePerm d, M.facePerm (M.facePerm d)} : Finset M.Dart) ⊆
      fibre := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;>
      simp [fibre, M.faceOf_facePerm]
  have hne := M.facePerm_ne_self_of_loopless hloop d
  have hne' := M.facePerm_ne_self_of_loopless hloop (M.facePerm d)
  have hcard : ({d, M.facePerm d, M.facePerm (M.facePerm d)} : Finset M.Dart).card = 3 := by
    simp [hne.symm, htwo.symm, hne'.symm]
  have hle := Finset.card_le_card hsub
  rw [hcard] at hle
  have hfibre : fibre.card = M.faceDegree (M.faceOf d) := by
    simp [fibre, faceDegree, orbitDegree, Nat.card_eq_fintype_card,
      Fintype.card_subtype, faceOf]
  exact hfibre ▸ hle

/-- Euler's bound from actual simplicity. A two-dart face forces a one-edge
component, handled directly; all other components satisfy the usual
three-darts-per-face argument. -/
theorem edgeCount_le_three_mul_vertex_sub_one_of_simple
    (hplanar : M.IsPlanar) (hloop : M.IsLoopless)
    (hmulti : M.HasNoMultipleEdges) :
    M.edgeCount ≤ 3 * (M.vertexCount - 1) := by
  classical
  by_cases htwo : ∃ d : M.Dart, M.facePerm (M.facePerm d) = d
  · obtain ⟨d, hd⟩ := htwo
    obtain ⟨hsigma, halpha⟩ := M.sigma_fixed_of_facePerm_twoCycle hloop hmulti d hd
    have hsub : (Finset.univ : Finset M.Dart) ⊆ {d, M.alpha d} := by
      intro x _
      simpa only [Finset.mem_insert, Finset.mem_singleton] using
        M.dart_eq_or_alpha_of_fixed_endpoints hplanar.1 d hsigma halpha x
    have hdarts : M.dartCount ≤ 2 := by
      have h := (Finset.card_le_card hsub).trans Finset.card_le_two
      simpa only [Finset.card_univ, dartCount, Nat.card_eq_fintype_card] using h
    have hvertices : 2 ≤ M.vertexCount := by
      have h := Finset.card_le_card
        (Finset.subset_univ ({M.vertexOf d, M.vertexOf (M.alpha d)} : Finset M.Vertex))
      simpa [hloop d, vertexCount, Nat.card_eq_fintype_card] using h
    have hcount := M.dartCount_eq_two_mul_edgeCount
    omega
  · apply M.edgeCount_le_three_mul_vertex_sub_one hplanar
    intro f
    refine Quotient.inductionOn' f ?_
    intro d
    exact M.faceDegree_ge_three_of_not_twoCycle hloop d (fun h => htwo ⟨d, h⟩)

end GroupApproximation.GGT.VanKampen.CombMap

#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.sigma_fixed_of_facePerm_twoCycle
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.vertexCount_pos_of_planar
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.dart_eq_or_alpha_of_fixed_endpoints
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.faceDegree_ge_three_of_not_twoCycle
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.edgeCount_le_three_mul_vertex_sub_one_of_simple
