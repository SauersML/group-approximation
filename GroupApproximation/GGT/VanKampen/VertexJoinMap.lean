import GroupApproximation.GGT.VanKampen.CombMapEdgeInsertion
import GroupApproximation.GGT.VanKampen.PermOrbitJoin
import GroupApproximation.Meta.AxiomGuard

/-!
# Joining two vertices at corners of a common face

Vertex rotation is composed with the transposition of two darts `x` and `y`:
after `x` the rotation continues with the successor of `y`, and after `y` with
the successor of `x`.  When `x` and `y` lie at different vertices the two
rotation cycles become one.  On faces this is the right transposition of
`alpha x` and `alpha y` (`facePerm_eq`), which splits the face through both
corners into two faces.

So the map loses one vertex, keeps its edges and gains one face, and
connectedness and planarity are preserved.  In the literal van Kampen
construction, joining the two ends of a cancelling pair `u u⁻¹` of consecutive
boundary darts closes that pair off into a digon.
-/

namespace GroupApproximation.GGT.VanKampen.VertexJoin

open Equiv

universe u

variable (M : CombMap.{u}) [DecidableEq M.Dart] (x y : M.Dart)

/-- The map with the vertices of `x` and `y` joined after these darts. -/
abbrev toCombMap : CombMap.{u} := { M with sigma := M.sigma * Equiv.swap x y }

theorem sigma_apply (z : M.Dart) :
    (toCombMap M x y).sigma z = M.sigma (Equiv.swap x y z) := rfl

/-- **Face rotation.**  The joined map transposes the successors of `alpha x`
and `alpha y` along faces. -/
theorem facePerm_eq :
    (toCombMap M x y).facePerm = M.facePerm * Equiv.swap (M.alpha x) (M.alpha y) := by
  refine Equiv.ext fun (z : M.Dart) => ?_
  change M.sigma (Equiv.swap x y (M.alpha z)) =
    M.sigma (M.alpha (Equiv.swap (M.alpha x) (M.alpha y) z))
  congr 1
  by_cases hx : z = M.alpha x
  · rw [hx, M.alpha_involutive, Equiv.swap_apply_left, Equiv.swap_apply_left,
      M.alpha_involutive]
  · by_cases hy : z = M.alpha y
    · rw [hy, M.alpha_involutive, Equiv.swap_apply_right, Equiv.swap_apply_right,
        M.alpha_involutive]
    · have hx' : M.alpha z ≠ x := fun h => hx (by rw [← h, M.alpha_involutive])
      have hy' : M.alpha z ≠ y := fun h => hy (by rw [← h, M.alpha_involutive])
      rw [Equiv.swap_apply_of_ne_of_ne hx' hy', Equiv.swap_apply_of_ne_of_ne hx hy]

/-- **Two distinct vertices become one.** -/
theorem vertexCount_add_one (hxy : ¬ M.sigma.SameCycle x y) :
    (toCombMap M x y).vertexCount + 1 = M.vertexCount := by
  change Nat.card (CombMap.Orbit (M.sigma * Equiv.swap x y)) + 1 =
    Nat.card (CombMap.Orbit M.sigma)
  rw [PermCycleCoordinates.orbit_card_mul_swap_eq]
  exact PermCycleCoordinates.orbit_card_swap_mul_of_not_sameCycle M.sigma x y hxy

/-- The edges are untouched. -/
theorem edgeCount_eq : (toCombMap M x y).edgeCount = M.edgeCount := rfl

/-- **The common face splits into two.** -/
theorem faceCount_eq (hne : M.alpha x ≠ M.alpha y)
    (hface : M.facePerm.SameCycle (M.alpha x) (M.alpha y)) :
    (toCombMap M x y).faceCount = M.faceCount + 1 := by
  have h : Nat.card (CombMap.Orbit (M.facePerm * Equiv.swap (M.alpha x) (M.alpha y))) =
      Nat.card (CombMap.Orbit M.facePerm) + 1 := by
    rw [PermCycleCoordinates.orbit_card_mul_swap_eq]
    exact PermCycleCoordinates.orbit_card_swap_mul M.facePerm (M.alpha x) (M.alpha y) hne hface
  change Nat.card (CombMap.Orbit (toCombMap M x y).facePerm) =
    Nat.card (CombMap.Orbit M.facePerm) + 1
  rw [facePerm_eq]
  exact h

/-- After joining, `x` and `y` lie at the same vertex. -/
theorem sameCycle_joined (hxy : ¬ M.sigma.SameCycle x y) :
    (toCombMap M x y).sigma.SameCycle x y := by
  have hconj : M.sigma * Equiv.swap x y =
      Equiv.swap x y * (Equiv.swap x y * M.sigma * (Equiv.swap x y)⁻¹) := by
    rw [Equiv.swap_inv, ← mul_assoc, Equiv.swap_mul_self_mul]
  have hτ : ¬ (Equiv.swap x y * M.sigma * (Equiv.swap x y)⁻¹).SameCycle x y := by
    rw [Equiv.Perm.sameCycle_conj, Equiv.swap_inv, Equiv.swap_apply_left,
      Equiv.swap_apply_right]
    exact fun h => hxy h.symm
  change (M.sigma * Equiv.swap x y).SameCycle x y
  rw [hconj]
  exact PermCycleCoordinates.sameCycle_swap_mul_of_not_sameCycle _ x y hτ

/-- One old elementary move is reached in the joined map. -/
theorem reachable_step (hxy : ¬ M.sigma.SameCycle x y) (u v : M.Dart)
    (huv : M.Adjacent u v) : Relation.EqvGen (toCombMap M x y).Adjacent u v := by
  have hjoin : Relation.EqvGen (toCombMap M x y).Adjacent x y :=
    CombMap.eqvGen_of_sameCycle_sigma _ (sameCycle_joined M x y hxy)
  rcases huv with h | h
  · exact Relation.EqvGen.rel _ _ (Or.inl h)
  · rw [← h]
    by_cases hux : u = x
    · rw [hux]
      have h1 : (toCombMap M x y).sigma y = M.sigma x := by
        change M.sigma (Equiv.swap x y y) = M.sigma x
        rw [Equiv.swap_apply_right]
      exact Relation.EqvGen.trans _ y _ hjoin (Relation.EqvGen.rel _ _ (Or.inr h1))
    · by_cases huy : u = y
      · rw [huy]
        have h2 : (toCombMap M x y).sigma x = M.sigma y := by
          change M.sigma (Equiv.swap x y x) = M.sigma y
          rw [Equiv.swap_apply_left]
        exact Relation.EqvGen.trans _ x _ (Relation.EqvGen.symm _ _ hjoin)
          (Relation.EqvGen.rel _ _ (Or.inr h2))
      · apply Relation.EqvGen.rel
        right
        change M.sigma (Equiv.swap x y u) = M.sigma u
        rw [Equiv.swap_apply_of_ne_of_ne hux huy]

/-- **Joining two distinct vertices keeps the map connected.** -/
theorem connected (hM : M.IsConnected) (hxy : ¬ M.sigma.SameCycle x y) :
    (toCombMap M x y).IsConnected := by
  intro d e
  have hlift : ∀ u v : M.Dart, Relation.EqvGen M.Adjacent u v →
      Relation.EqvGen (toCombMap M x y).Adjacent u v := by
    intro u v huv
    induction huv with
    | rel u v h => exact reachable_step M x y hxy u v h
    | refl u => exact Relation.EqvGen.refl _
    | symm u v _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans u v w _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
  exact hlift d e (hM d e)

/-- **Joining two distinct vertices on a common face keeps the map planar.** -/
theorem planar (hM : M.IsPlanar) (hxy : ¬ M.sigma.SameCycle x y)
    (hne : M.alpha x ≠ M.alpha y)
    (hface : M.facePerm.SameCycle (M.alpha x) (M.alpha y)) :
    (toCombMap M x y).IsPlanar := by
  refine ⟨connected M x y hM.1 hxy, ?_⟩
  have h := hM.2
  have hv := vertexCount_add_one M x y hxy
  have hf := faceCount_eq M x y hne hface
  unfold CombMap.eulerCharacteristic at h ⊢
  rw [edgeCount_eq, hf]
  omega

end GroupApproximation.GGT.VanKampen.VertexJoin

#audit_axioms GroupApproximation.GGT.VanKampen.VertexJoin.facePerm_eq
#audit_axioms GroupApproximation.GGT.VanKampen.VertexJoin.vertexCount_add_one
#audit_axioms GroupApproximation.GGT.VanKampen.VertexJoin.faceCount_eq
#audit_axioms GroupApproximation.GGT.VanKampen.VertexJoin.sameCycle_joined
#audit_axioms GroupApproximation.GGT.VanKampen.VertexJoin.connected
#audit_axioms GroupApproximation.GGT.VanKampen.VertexJoin.planar
