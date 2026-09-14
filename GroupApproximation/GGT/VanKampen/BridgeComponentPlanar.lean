import GroupApproximation.GGT.VanKampen.BridgeComponentMap
import GroupApproximation.Meta.AxiomGuard

/-!
# Deleting a same-face bridge: the far component is planar

Let `a` be a dart of a planar map whose reverse lies on the same face, where neither endpoint of
the edge has degree one.  Delete the edge.
* `reach_or`: every dart of the deleted map is joined to `σ (α a)` or to `σ a`.
* `euler_four`: the deleted map has Euler characteristic four.
* `Side`: the darts joined to `σ (α a)`; `near1_not_side`: `σ a` is not among them, since otherwise
  the deleted map would be connected with Euler characteristic at most two.
* `component`, `component_planar`: the map on the far side is planar.

## Manuscript status

Infrastructure for `thm:hull` ("Hull's small cancellation theorem", through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u

namespace BridgeComponent

variable (M : CombMap.{u}) [DecidableEq M.Dart] (a : M.Dart)
  (hface : M.faceOf a = M.faceOf (M.alpha a)) (hstart : M.sigma (M.alpha a) ≠ M.alpha a)
  (htail : M.sigma a ≠ a)

/-- The darts of the deleted map joined to `σ (α a)` or to `σ a`. -/
def Reached (x : EdgeDeletion.Dart M a) : Prop :=
  Relation.EqvGen (EdgeDeletion.toCombMap M a).Adjacent (near0 M a hface hstart) x ∨
    Relation.EqvGen (EdgeDeletion.toCombMap M a).Adjacent (near1 M a hface htail) x

theorem reached_iff_of_adjacent {x y : EdgeDeletion.Dart M a}
    (h : (EdgeDeletion.toCombMap M a).Adjacent x y) :
    Reached M a hface hstart htail x ↔ Reached M a hface hstart htail y := by
  have hxy := Relation.EqvGen.rel _ _ h
  constructor
  · rintro (h0 | h1)
    · exact Or.inl (Relation.EqvGen.trans _ _ _ h0 hxy)
    · exact Or.inr (Relation.EqvGen.trans _ _ _ h1 hxy)
  · rintro (h0 | h1)
    · exact Or.inl (Relation.EqvGen.trans _ _ _ h0 (Relation.EqvGen.symm _ _ hxy))
    · exact Or.inr (Relation.EqvGen.trans _ _ _ h1 (Relation.EqvGen.symm _ _ hxy))

/-- **Every dart of the deleted map is joined to `σ (α a)` or to `σ a`.** -/
theorem reach_or (hM : M.IsConnected) (x : EdgeDeletion.Dart M a) :
    Reached M a hface hstart htail x := by
  have hbase : ∀ (y : M.Dart) (hy : y ≠ a) (hy' : y ≠ M.alpha a),
      (M.sigma y = a ∨ M.sigma y = M.alpha a) →
        Reached M a hface hstart htail (EdgeDeletion.ofValue M a y hy hy') := by
    intro y hy hy' hsy
    have hadj : (EdgeDeletion.toCombMap M a).Adjacent (EdgeDeletion.ofValue M a y hy hy')
        ((EdgeDeletion.toCombMap M a).sigma (EdgeDeletion.ofValue M a y hy hy')) := Or.inr rfl
    refine (reached_iff_of_adjacent M a hface hstart htail hadj).mpr ?_
    have hv := value_sigma M a (EdgeDeletion.ofValue M a y hy hy')
    have hval : EdgeDeletion.value M a (EdgeDeletion.ofValue M a y hy hy') = y := rfl
    rw [hval] at hv
    rcases hsy with hsy | hsy
    · rw [if_pos hsy, if_neg (sigma_ne_alpha M a hface)] at hv
      have e : (EdgeDeletion.toCombMap M a).sigma (EdgeDeletion.ofValue M a y hy hy') =
          near1 M a hface htail := EdgeDeletion.value_injective M a (hv.trans (by rfl))
      rw [e]
      exact Or.inr (Relation.EqvGen.refl _)
    · have hne : M.sigma y ≠ a := by
        rw [hsy]
        exact M.alpha_fixedPointFree a
      rw [if_neg hne, if_pos hsy, if_neg (sigma_alpha_ne M a hface)] at hv
      have e : (EdgeDeletion.toCombMap M a).sigma (EdgeDeletion.ofValue M a y hy hy') =
          near0 M a hface hstart := EdgeDeletion.value_injective M a (hv.trans (by rfl))
      rw [e]
      exact Or.inl (Relation.EqvGen.refl _)
  have hsigma : ∀ (y z : M.Dart) (hy : y ≠ a) (hy' : y ≠ M.alpha a) (hz : z ≠ a)
      (hz' : z ≠ M.alpha a), M.sigma y = z →
        (EdgeDeletion.toCombMap M a).Adjacent (EdgeDeletion.ofValue M a y hy hy')
          (EdgeDeletion.ofValue M a z hz hz') := by
    intro y z hy hy' hz hz' h
    have hv := value_sigma M a (EdgeDeletion.ofValue M a y hy hy')
    have hval : EdgeDeletion.value M a (EdgeDeletion.ofValue M a y hy hy') = y := rfl
    rw [hval, h, if_neg hz, if_neg hz'] at hv
    exact Or.inr (EdgeDeletion.value_injective M a (hv.trans (by rfl)))
  have halpha : ∀ (y z : M.Dart) (hy : y ≠ a) (hy' : y ≠ M.alpha a) (hz : z ≠ a)
      (hz' : z ≠ M.alpha a), M.alpha y = z →
        (EdgeDeletion.toCombMap M a).Adjacent (EdgeDeletion.ofValue M a y hy hy')
          (EdgeDeletion.ofValue M a z hz hz') := fun y z hy hy' hz hz' h =>
    Or.inl (EdgeDeletion.value_injective M a ((EdgeDeletion.alpha_val M a _).trans h))
  let P : M.Dart → Prop := fun y => ∀ (hy : y ≠ a) (hy' : y ≠ M.alpha a),
    Reached M a hface hstart htail (EdgeDeletion.ofValue M a y hy hy')
  have hstep : ∀ y z, M.Adjacent y z → P y → P z := by
    intro y z hyz hPy hz hz'
    by_cases hy : y = a
    · rcases hyz with h | h
      · exact absurd (show z = M.alpha a by rw [← h, hy]) hz'
      · subst hy
        subst h
        exact Or.inr (Relation.EqvGen.refl _)
    by_cases hy' : y = M.alpha a
    · rcases hyz with h | h
      · exact absurd (show z = a by rw [← h, hy', M.alpha_involutive]) hz
      · subst hy'
        subst h
        exact Or.inl (Relation.EqvGen.refl _)
    rcases hyz with h | h
    · exact (reached_iff_of_adjacent M a hface hstart htail
        (halpha y z hy hy' hz hz' h)).mp (hPy hy hy')
    · exact (reached_iff_of_adjacent M a hface hstart htail
        (hsigma y z hy hy' hz hz' h)).mp (hPy hy hy')
  have hstep' : ∀ y z, M.Adjacent y z → P z → P y := by
    intro y z hyz hPz hy hy'
    rcases hyz with h | h
    · by_cases hz : z = a
      · exact absurd (show y = M.alpha a by rw [← hz, ← h, M.alpha_involutive]) hy'
      by_cases hz' : z = M.alpha a
      · exact absurd (M.alpha.injective (show M.alpha y = M.alpha a by rw [h, hz'])) hy
      exact (reached_iff_of_adjacent M a hface hstart htail
        (halpha y z hy hy' hz hz' h)).mpr (hPz hz hz')
    · by_cases hz : z = a
      · exact hbase y hy hy' (Or.inl (h.trans hz))
      by_cases hz' : z = M.alpha a
      · exact hbase y hy hy' (Or.inr (h.trans hz'))
      exact (reached_iff_of_adjacent M a hface hstart htail
        (hsigma y z hy hy' hz hz' h)).mpr (hPz hz hz')
  have hkey : ∀ y z, Relation.EqvGen M.Adjacent y z → (P y ↔ P z) := by
    intro y z h
    induction h with
    | rel y z h => exact ⟨hstep y z h, hstep' y z h⟩
    | refl y => exact Iff.rfl
    | symm y z _ ih => exact ih.symm
    | trans y z w _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  have hPa : P a := fun hy => absurd rfl hy
  exact (hkey a (EdgeDeletion.value M a x) (hM a _)).mp hPa (EdgeDeletion.value_ne M a x)
    (EdgeDeletion.value_ne_reverse M a x)

include hface hstart htail in
/-- **The deleted map has Euler characteristic four.** -/
theorem euler_four (hM : M.IsPlanar) :
    (EdgeDeletion.toCombMap M a).eulerCharacteristic = 4 := by
  have hv := EdgeDeletion.vertexCount_eq_of_sigma_ne M a hM.1 (near0 M a hface hstart) htail hstart
  have hb := EdgeDeletion.euler_balance_of_sameFace M a hface
  rw [hv] at hb
  have h2 := hM.2
  linarith

/-- The far side: the darts of the deleted map joined to `σ (α a)`. -/
def Side (x : EdgeDeletion.Dart M a) : Prop :=
  Relation.EqvGen (EdgeDeletion.toCombMap M a).Adjacent (near0 M a hface hstart) x

theorem side_alpha (x : EdgeDeletion.Dart M a) :
    Side M a hface hstart ((EdgeDeletion.toCombMap M a).alpha x) ↔ Side M a hface hstart x := by
  have h : Relation.EqvGen (EdgeDeletion.toCombMap M a).Adjacent x
      ((EdgeDeletion.toCombMap M a).alpha x) := Relation.EqvGen.rel _ _ (Or.inl rfl)
  exact ⟨fun hs => Relation.EqvGen.trans _ _ _ hs (Relation.EqvGen.symm _ _ h),
    fun hs => Relation.EqvGen.trans _ _ _ hs h⟩

theorem side_sigma (x : EdgeDeletion.Dart M a) :
    Side M a hface hstart ((EdgeDeletion.toCombMap M a).sigma x) ↔ Side M a hface hstart x := by
  have h : Relation.EqvGen (EdgeDeletion.toCombMap M a).Adjacent x
      ((EdgeDeletion.toCombMap M a).sigma x) := Relation.EqvGen.rel _ _ (Or.inr rfl)
  exact ⟨fun hs => Relation.EqvGen.trans _ _ _ hs (Relation.EqvGen.symm _ _ h),
    fun hs => Relation.EqvGen.trans _ _ _ hs h⟩

/-- **The map on the far side.** -/
noncomputable def component : CombMap.{u} :=
  (EdgeDeletion.toCombMap M a).restrict (Side M a hface hstart) (side_alpha M a hface hstart)
    (side_sigma M a hface hstart)

/-- **`σ a` is on the other side.** -/
theorem near1_not_side (hM : M.IsPlanar) :
    ¬ Side M a hface hstart (near1 M a hface htail) := by
  intro h1
  have hall : ∀ x, Side M a hface hstart x := fun x => by
    rcases reach_or M a hface hstart htail hM.1 x with h | h
    · exact h
    · exact Relation.EqvGen.trans _ _ _ h1 h
  have hconn : (EdgeDeletion.toCombMap M a).IsConnected := fun x y =>
    Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (hall x)) (hall y)
  have hle := (EdgeDeletion.toCombMap M a).eulerCharacteristic_le_two hconn
  have h4 := euler_four M a hface hstart htail hM
  omega

include htail in
/-- **The far component is planar.** -/
theorem component_planar (hM : M.IsPlanar) : (component M a hface hstart).IsPlanar := by
  refine (EdgeDeletion.toCombMap M a).restrict_planar_of_euler_four (Side M a hface hstart)
    (side_alpha M a hface hstart) (side_sigma M a hface hstart)
    (euler_four M a hface hstart htail hM)
    ((EdgeDeletion.toCombMap M a).restrict_connected _ _ _ (Relation.EqvGen.refl _)
      fun _ hx => hx)
    ((EdgeDeletion.toCombMap M a).restrict_connected _ _ _
      (near1_not_side M a hface hstart htail hM) fun x hx => ?_)
  rcases reach_or M a hface hstart htail hM.1 x with h | h
  · exact absurd h hx
  · exact h

end BridgeComponent

#audit_axioms GroupApproximation.GGT.VanKampen.BridgeComponent.reached_iff_of_adjacent
#audit_axioms GroupApproximation.GGT.VanKampen.BridgeComponent.reach_or
#audit_axioms GroupApproximation.GGT.VanKampen.BridgeComponent.euler_four
#audit_axioms GroupApproximation.GGT.VanKampen.BridgeComponent.side_alpha
#audit_axioms GroupApproximation.GGT.VanKampen.BridgeComponent.side_sigma
#audit_axioms GroupApproximation.GGT.VanKampen.BridgeComponent.near1_not_side
#audit_axioms GroupApproximation.GGT.VanKampen.BridgeComponent.component_planar

end GroupApproximation.GGT.VanKampen
