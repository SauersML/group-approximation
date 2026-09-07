import GroupApproximation.GGT.VanKampen.CombMapRestrictionPaths

/-!
# Grow a retained map by one actual ambient edge

Adjoin both darts of a missing edge at a vertex of the retained core. The
new map uses the ambient first-return rotation, remains connected, and
deleting the adjoined edge recovers the original core up to its actual dart
equivalence. This constructs the step needed for a finite growth order.
-/

namespace GroupApproximation.GGT.VanKampen.CombMap.RestrictionGrowth

universe u v
variable {M : CombMap.{u}} {N : CombMap.{v}} {e : N.Dart ↪ M.Dart}
  (h : M.IsRestriction N e) (a : M.Dart)

def keep (x : M.Dart) : Prop := x ∈ Set.range e ∨ x = a ∨ x = M.alpha a

include h in
theorem keep_alpha (x : M.Dart) : keep (e := e) a (M.alpha x) ↔ keep (e := e) a x := by
  constructor
  · rintro (hx | hx | hx)
    · exact Or.inl ((h.range_alpha_iff x).mp hx)
    · exact Or.inr (Or.inr ((M.alpha_involutive x).symm.trans (congrArg M.alpha hx)))
    · exact Or.inr (Or.inl (M.alpha.injective hx))
  · rintro (hx | rfl | rfl)
    · exact Or.inl ((h.range_alpha_iff x).mpr hx)
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl (M.alpha_involutive a))

noncomputable def toCombMap : CombMap.{u} :=
  PredicateRestriction.toCombMap M (keep (e := e) a) (keep_alpha h a)

def ambientEmbedding : (toCombMap h a).Dart ↪ M.Dart := Function.Embedding.subtype _

def oldEmbedding : N.Dart ↪ (toCombMap h a).Dart :=
  ⟨fun d => ⟨e d, Or.inl ⟨d, rfl⟩⟩, fun _ _ hd => e.injective (congrArg Subtype.val hd)⟩

def newDart : (toCombMap h a).Dart := ⟨a, Or.inr (Or.inl rfl)⟩

theorem ambientRestriction : M.IsRestriction (toCombMap h a) (ambientEmbedding h a) :=
  PredicateRestriction.isRestriction M (keep (e := e) a) (keep_alpha h a)

theorem oldRestriction : (toCombMap h a).IsRestriction N (oldEmbedding h a) :=
  (ambientRestriction h a).of_trans h

/-- The added edge meets the old connected core at its prescribed vertex. -/
theorem connected (hN : N.IsConnected) (b : N.Dart)
    (hv : M.vertexOf a = M.vertexOf (e b)) : (toCombMap h a).IsConnected := by
  let K := toCombMap h a
  let f := oldEmbedding h a
  let z := newDart h a
  have hz : Relation.EqvGen K.Adjacent z (f b) := by
    apply K.eqvGen_of_sameCycle_sigma
    apply (K.vertexOf_eq_iff _ _).mp
    exact ((ambientRestriction h a).vertexOf_eq_iff z (f b)).mpr hv
  have hall (x : K.Dart) : Relation.EqvGen K.Adjacent x (f b) := by
    rcases x.2 with ⟨d, hd⟩ | hd | hd
    · have hx : x = f d := Subtype.ext hd.symm
      rw [hx]
      exact (oldRestriction h a).reachable (hN d b)
    · have hx : x = z := Subtype.ext hd
      rw [hx]
      exact hz
    · have hx : x = K.alpha z := Subtype.ext hd
      rw [hx]
      have hedge : Relation.EqvGen K.Adjacent z (K.alpha z) := .rel _ _ (Or.inl rfl)
      exact Relation.EqvGen.trans _ _ _ hedge.symm hz
  intro x y
  exact Relation.EqvGen.trans _ _ _ (hall x) (hall y).symm

theorem old_ne_new (ha : a ∉ Set.range e) (d : N.Dart) :
    oldEmbedding h a d ≠ newDart h a := by
  intro hd
  exact ha ⟨d, congrArg Subtype.val hd⟩

theorem old_ne_reverse (ha : a ∉ Set.range e) (d : N.Dart) :
    oldEmbedding h a d ≠ (toCombMap h a).alpha (newDart h a) := by
  intro hd
  exact ha ((h.range_alpha_iff a).mp ⟨d, congrArg Subtype.val hd⟩)

variable [DecidableEq M.Dart]

local instance : DecidableEq (toCombMap h a).Dart :=
  inferInstanceAs (DecidableEq {x : M.Dart // keep (e := e) a x})

/-- Deleting the new pair retains every original core dart. -/
noncomputable def deletedEmbedding (ha : a ∉ Set.range e) :
    N.Dart ↪ (EdgeDeletion.toCombMap (toCombMap h a) (newDart h a)).Dart :=
  ⟨fun d => EdgeDeletion.ofValue (toCombMap h a) (newDart h a) (oldEmbedding h a d)
      (old_ne_new h a ha d) (old_ne_reverse h a ha d),
    fun _ _ hd => (oldEmbedding h a).injective
      (congrArg (EdgeDeletion.value (toCombMap h a) (newDart h a)) hd)⟩

theorem deletedEmbedding_surjective (ha : a ∉ Set.range e) :
    Function.Surjective (deletedEmbedding h a ha) := by
  intro x
  let k := EdgeDeletion.value (toCombMap h a) (newDart h a) x
  rcases k.2 with ⟨d, hd⟩ | hd | hd
  · refine ⟨d, ?_⟩
    apply EdgeDeletion.value_injective (toCombMap h a) (newDart h a)
    exact Subtype.ext hd
  · exact (EdgeDeletion.value_ne (toCombMap h a) (newDart h a) x (Subtype.ext hd)).elim
  · exact (EdgeDeletion.value_ne_reverse (toCombMap h a) (newDart h a) x
      (Subtype.ext hd)).elim

theorem deleted_isRestriction (ha : a ∉ Set.range e) :
    (EdgeDeletion.toCombMap (toCombMap h a) (newDart h a)).IsRestriction N
      (deletedEmbedding h a ha) :=
  (EdgeDeletion.isRestriction (toCombMap h a) (newDart h a)).of_trans (oldRestriction h a)

/-- Exactly the two new ambient darts have been added. -/
theorem dartCount_add_two (ha : a ∉ Set.range e) :
    (toCombMap h a).dartCount = N.dartCount + 2 := by
  have hd : (EdgeDeletion.toCombMap (toCombMap h a) (newDart h a)).dartCount =
      N.dartCount := (Nat.card_congr (Equiv.ofBijective (deletedEmbedding h a ha)
        ⟨(deletedEmbedding h a ha).injective, deletedEmbedding_surjective h a ha⟩)).symm
  have hcount := EdgeDeletion.dartCount_add_two (toCombMap h a) (newDart h a)
  rw [hd] at hcount
  exact hcount.symm

/-- Growing a connected core at one of its vertices cannot increase its
Euler characteristic. The second endpoint may be a new vertex. -/
theorem euler_le (ha : a ∉ Set.range e) (hN : N.IsConnected) (b : N.Dart)
    (hv : M.vertexOf a = M.vertexOf (e b)) :
    (toCombMap h a).eulerCharacteristic ≤ N.eulerCharacteristic := by
  have hc := connected h a hN b hv
  have hle := EdgeDeletion.eulerCharacteristic_le_deleted (toCombMap h a)
    (newDart h a) hc (deletedEmbedding h a ha b)
  have heq := (deleted_isRestriction h a ha).euler_eq_of_surjective
    (deletedEmbedding_surjective h a ha)
  exact hle.trans_eq heq.symm

end GroupApproximation.GGT.VanKampen.CombMap.RestrictionGrowth

#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.RestrictionGrowth.connected
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.RestrictionGrowth.deleted_isRestriction
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.RestrictionGrowth.dartCount_add_two
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.RestrictionGrowth.euler_le
