import GroupApproximation.GGT.VanKampen.CombMapEulerUpperBound
import GroupApproximation.GGT.VanKampen.CactusTopology
import GroupApproximation.GGT.VanKampen.CombMapEdgeSubdivision
import GroupApproximation.Meta.AxiomGuard

set_option linter.unusedSectionVars false

/-!
# The map on an invariant set of darts

A set of darts closed under edge reversal and vertex rotation carries the restricted
permutations, and these form a combinatorial map (`CombMap.restrict`).  The set and its
complement split the vertices, edges and faces of the ambient map, so Euler
characteristics add (`CombMap.eulerCharacteristic_restrict_add`).  Paths of the ambient
map between darts of the set stay in the set, so reachability inside the set gives
connectedness (`CombMap.restrict_connected`).

When the ambient map has Euler characteristic `4` and both parts are connected, both are
planar (`CombMap.restrict_planar_of_euler_four`).  This is how a disc diagram pinched at a
vertex is cut into its two pieces.
-/

namespace GroupApproximation.GGT.VanKampen.CombMap

open Equiv

universe u

/-! ## Orbits of an invariant set -/

section Orbits

variable {D : Type u} [Finite D]

theorem iff_of_sameCycle (f : Perm D) (S : D → Prop) (hS : ∀ x, S (f x) ↔ S x) {x y : D}
    (h : f.SameCycle x y) : S x ↔ S y := by
  have hc := OrbitClassifier.eq_of_sameCycle f S (fun d => propext (hS d)) h
  rw [hc]

/-- **Orbits split along an invariant set.** -/
theorem card_orbit_subtypePerm_add (f : Perm D) (S : D → Prop) (hS : ∀ x, S (f x) ↔ S x) :
    Nat.card (Orbit (f.subtypePerm hS)) +
      Nat.card (Orbit (f.subtypePerm (p := fun x => ¬ S x) (fun x => not_congr (hS x)))) =
        Nat.card (Orbit f) := by
  classical
  let g : D → Orbit (f.subtypePerm hS) ⊕
      Orbit (f.subtypePerm (p := fun x => ¬ S x) (fun x => not_congr (hS x))) :=
    fun x => if hx : S x then Sum.inl (Quotient.mk'' ⟨x, hx⟩) else Sum.inr (Quotient.mk'' ⟨x, hx⟩)
  have hg : ∀ x y, f.SameCycle x y → g x = g y := by
    intro x y hxy
    have hSy := iff_of_sameCycle f S hS hxy
    by_cases hx : S x
    · have hy : S y := hSy.mp hx
      simp only [g, dif_pos hx, dif_pos hy]
      exact congrArg Sum.inl (Quotient.sound (Equiv.Perm.sameCycle_subtypePerm.mpr hxy))
    · have hy : ¬ S y := fun hy => hx (hSy.mpr hy)
      simp only [g, dif_neg hx, dif_neg hy]
      exact congrArg Sum.inr (Quotient.sound (Equiv.Perm.sameCycle_subtypePerm.mpr hxy))
  let e : Orbit f ≃ Orbit (f.subtypePerm hS) ⊕
      Orbit (f.subtypePerm (p := fun x => ¬ S x) (fun x => not_congr (hS x))) :=
    { toFun := Quotient.lift g hg
      invFun := Sum.elim
        (Quotient.lift (fun x => (Quotient.mk'' x.1 : Orbit f))
          (fun _ _ h => Quotient.sound (Equiv.Perm.sameCycle_subtypePerm.mp h)))
        (Quotient.lift (fun x => (Quotient.mk'' x.1 : Orbit f))
          (fun _ _ h => Quotient.sound (Equiv.Perm.sameCycle_subtypePerm.mp h)))
      left_inv := by
        intro q
        induction q using Quotient.inductionOn' with
        | h x =>
          show Sum.elim _ _ (g x) = Quotient.mk'' x
          by_cases hx : S x
          · have hgx : g x = Sum.inl (Quotient.mk'' ⟨x, hx⟩) := dif_pos hx
            rw [hgx]
            rfl
          · have hgx : g x = Sum.inr (Quotient.mk'' ⟨x, hx⟩) := dif_neg hx
            rw [hgx]
            rfl
      right_inv := by
        intro s
        rcases s with q | q
        · induction q using Quotient.inductionOn' with
          | h x =>
            show g x.1 = Sum.inl (Quotient.mk'' x)
            exact dif_pos x.2
        · induction q using Quotient.inductionOn' with
          | h x =>
            show g x.1 = Sum.inr (Quotient.mk'' x)
            exact dif_neg x.2 }
  rw [← Nat.card_sum]
  exact Nat.card_congr e.symm

end Orbits

/-! ## The restricted map -/

variable (M : CombMap.{u}) (S : M.Dart → Prop)
  (hα : ∀ x, S (M.alpha x) ↔ S x) (hσ : ∀ x, S (M.sigma x) ↔ S x)

/-- **The map on an invariant set of darts.** -/
noncomputable def restrict : CombMap.{u} where
  Dart := {x // S x}
  dartFintype := Fintype.ofFinite _
  alpha := M.alpha.subtypePerm hα
  sigma := M.sigma.subtypePerm hσ
  alpha_involutive x := Subtype.ext (M.alpha_involutive x.1)
  alpha_fixedPointFree x h := M.alpha_fixedPointFree x.1 (congrArg Subtype.val h)

theorem restrict_alpha_val (x : (M.restrict S hα hσ).Dart) :
    ((M.restrict S hα hσ).alpha x).1 = M.alpha x.1 := rfl

theorem restrict_sigma_val (x : (M.restrict S hα hσ).Dart) :
    ((M.restrict S hα hσ).sigma x).1 = M.sigma x.1 := rfl

theorem restrict_facePerm_val (x : (M.restrict S hα hσ).Dart) :
    ((M.restrict S hα hσ).facePerm x).1 = M.facePerm x.1 := rfl

include hα hσ in
theorem facePerm_invariant (x : M.Dart) : S (M.facePerm x) ↔ S x :=
  (hσ (M.alpha x)).trans (hα x)

include hα in
/-- The complement of an invariant set is invariant. -/
theorem compl_alpha (x : M.Dart) : ¬ S (M.alpha x) ↔ ¬ S x := not_congr (hα x)

include hσ in
theorem compl_sigma (x : M.Dart) : ¬ S (M.sigma x) ↔ ¬ S x := not_congr (hσ x)

theorem restrict_facePerm_eq :
    (M.restrict S hα hσ).facePerm = M.facePerm.subtypePerm (M.facePerm_invariant S hα hσ) :=
  Equiv.ext fun _ => Subtype.ext rfl

/-- **Vertices add up.** -/
theorem vertexCount_restrict_add :
    (M.restrict S hα hσ).vertexCount +
      (M.restrict (fun x => ¬ S x) (M.compl_alpha S hα) (M.compl_sigma S hσ)).vertexCount =
      M.vertexCount :=
  card_orbit_subtypePerm_add M.sigma S hσ

/-- **Faces add up.** -/
theorem faceCount_restrict_add :
    (M.restrict S hα hσ).faceCount +
      (M.restrict (fun x => ¬ S x) (M.compl_alpha S hα) (M.compl_sigma S hσ)).faceCount =
      M.faceCount := by
  have h := card_orbit_subtypePerm_add M.facePerm S (M.facePerm_invariant S hα hσ)
  have h1 : (M.restrict S hα hσ).faceCount =
      Nat.card (Orbit (M.facePerm.subtypePerm (M.facePerm_invariant S hα hσ))) :=
    Nat.card_congr (EdgeSubdivision.orbitEquivOfEq (M.restrict_facePerm_eq S hα hσ))
  have h2 : (M.restrict (fun x => ¬ S x) (M.compl_alpha S hα) (M.compl_sigma S hσ)).faceCount =
      Nat.card (Orbit (M.facePerm.subtypePerm (p := fun x => ¬ S x)
        (fun x => not_congr (M.facePerm_invariant S hα hσ x)))) :=
    Nat.card_congr (EdgeSubdivision.orbitEquivOfEq
      (M.restrict_facePerm_eq (fun x => ¬ S x) (M.compl_alpha S hα) (M.compl_sigma S hσ)))
  rw [h1, h2]
  exact h

/-- **Edges add up.** -/
theorem edgeCount_restrict_add :
    (M.restrict S hα hσ).edgeCount +
      (M.restrict (fun x => ¬ S x) (M.compl_alpha S hα) (M.compl_sigma S hσ)).edgeCount =
      M.edgeCount := by
  classical
  have hd : (M.restrict S hα hσ).dartCount +
      (M.restrict (fun x => ¬ S x) (M.compl_alpha S hα) (M.compl_sigma S hσ)).dartCount =
      M.dartCount := by
    change Nat.card {x // S x} + Nat.card {x // ¬ S x} = Nat.card M.Dart
    rw [← Nat.card_sum, Nat.card_congr (Equiv.sumCompl S)]
  rw [(M.restrict S hα hσ).dartCount_eq_two_mul_edgeCount,
    (M.restrict (fun x => ¬ S x) (M.compl_alpha S hα) (M.compl_sigma S hσ)).dartCount_eq_two_mul_edgeCount,
    M.dartCount_eq_two_mul_edgeCount] at hd
  omega

/-- **Euler characteristics add up.** -/
theorem eulerCharacteristic_restrict_add :
    (M.restrict S hα hσ).eulerCharacteristic +
      (M.restrict (fun x => ¬ S x) (M.compl_alpha S hα) (M.compl_sigma S hσ)).eulerCharacteristic =
      M.eulerCharacteristic := by
  have hv := M.vertexCount_restrict_add S hα hσ
  have he := M.edgeCount_restrict_add S hα hσ
  have hf := M.faceCount_restrict_add S hα hσ
  unfold CombMap.eulerCharacteristic
  omega

include hα hσ in
/-- Elementary moves preserve membership in an invariant set. -/
theorem iff_of_eqvGen {x y : M.Dart} (h : Relation.EqvGen M.Adjacent x y) : S x ↔ S y := by
  induction h with
  | rel x y h =>
      rcases h with h | h
      · rw [← h, hα]
      · rw [← h, hσ]
  | refl x => exact Iff.rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Paths between darts of an invariant set lift to the restricted map. -/
theorem exists_eqvGen_restrict {x y : M.Dart} (h : Relation.EqvGen M.Adjacent x y) (hx : S x) :
    ∃ hy : S y, Relation.EqvGen (M.restrict S hα hσ).Adjacent ⟨x, hx⟩ ⟨y, hy⟩ := by
  induction h with
  | rel x y h =>
      rcases h with h | h
      · exact ⟨h ▸ (hα x).mpr hx, Relation.EqvGen.rel _ _ (Or.inl (Subtype.ext h))⟩
      · exact ⟨h ▸ (hσ x).mpr hx, Relation.EqvGen.rel _ _ (Or.inr (Subtype.ext h))⟩
  | refl x => exact ⟨hx, Relation.EqvGen.refl _⟩
  | symm x y hxy ih =>
      have hy : S x := (M.iff_of_eqvGen S hα hσ hxy).mpr hx
      obtain ⟨_, hk⟩ := ih hy
      exact ⟨hy, Relation.EqvGen.symm _ _ hk⟩
  | trans x y z _ _ ih₁ ih₂ =>
      obtain ⟨hy, hk₁⟩ := ih₁ hx
      obtain ⟨hz, hk₂⟩ := ih₂ hy
      exact ⟨hz, Relation.EqvGen.trans _ _ _ hk₁ hk₂⟩

/-- **Reachability from one dart of the set makes the restricted map connected.** -/
theorem restrict_connected {x₀ : M.Dart} (hx₀ : S x₀)
    (hreach : ∀ x, S x → Relation.EqvGen M.Adjacent x₀ x) :
    (M.restrict S hα hσ).IsConnected := by
  intro x y
  obtain ⟨_, hx⟩ := M.exists_eqvGen_restrict S hα hσ (hreach x.1 x.2) hx₀
  obtain ⟨_, hy⟩ := M.exists_eqvGen_restrict S hα hσ (hreach y.1 y.2) hx₀
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hx) hy

/-- **Two connected pieces of Euler characteristic four are planar.** -/
theorem restrict_planar_of_euler_four (h4 : M.eulerCharacteristic = 4)
    (hK : (M.restrict S hα hσ).IsConnected)
    (hK' : (M.restrict (fun x => ¬ S x) (M.compl_alpha S hα) (M.compl_sigma S hσ)).IsConnected) :
    (M.restrict S hα hσ).IsPlanar := by
  refine ⟨hK, ?_⟩
  have hadd := M.eulerCharacteristic_restrict_add S hα hσ
  have h1 := (M.restrict S hα hσ).eulerCharacteristic_le_two hK
  have h2 := (M.restrict (fun x => ¬ S x) (M.compl_alpha S hα)
    (M.compl_sigma S hσ)).eulerCharacteristic_le_two hK'
  omega

end GroupApproximation.GGT.VanKampen.CombMap

#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.card_orbit_subtypePerm_add
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.vertexCount_restrict_add
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.faceCount_restrict_add
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.edgeCount_restrict_add
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.eulerCharacteristic_restrict_add
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.restrict_connected
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.restrict_planar_of_euler_four
