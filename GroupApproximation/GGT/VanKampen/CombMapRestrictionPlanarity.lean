import GroupApproximation.GGT.VanKampen.CombMapRestrictionGrowth
import GroupApproximation.GGT.VanKampen.CombMapEulerUpperBound

/-!
# Planarity of connected restrictions

Grow a nonempty connected retained core by actual ambient edges. A frontier
edge always exists until every dart is retained. Each growth step preserves
connectedness, adds exactly two darts, and cannot increase Euler characteristic.
Finite induction therefore supplies the comparison for an arbitrary connected
restriction; no sequence of connected deletions is assumed.
-/

namespace GroupApproximation.GGT.VanKampen.CombMap.IsRestriction

universe u
variable {M N : CombMap.{u}} {e : N.Dart ↪ M.Dart}

/-- A connected nonempty restriction has at least the ambient Euler
characteristic. The ambient map need not be planar. -/
theorem euler_le (h : M.IsRestriction N e) (hM : M.IsConnected)
    (hN : N.IsConnected) (d : N.Dart) : M.eulerCharacteristic ≤ N.eulerCharacteristic := by
  classical
  have hall : ∀ n : ℕ, ∀ (K : CombMap.{u}) (f : K.Dart ↪ M.Dart),
      M.dartCount - K.dartCount = n → M.IsRestriction K f → K.IsConnected →
      Nonempty K.Dart → M.eulerCharacteristic ≤ K.eulerCharacteristic := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro K f hcount hf hK hne
        by_cases hsurj : Function.Surjective f
        · exact le_of_eq (hf.euler_eq_of_surjective hsurj).symm
        · obtain ⟨d₀⟩ := hne
          obtain ⟨b, hb⟩ := hf.exists_sigma_frontier hM d₀ hsurj
          let a := M.sigma (f b)
          let L := RestrictionGrowth.toCombMap hf a
          let g := RestrictionGrowth.ambientEmbedding hf a
          have hL : M.IsRestriction L g := RestrictionGrowth.ambientRestriction hf a
          have hconn : L.IsConnected := RestrictionGrowth.connected hf a hK b
            (M.vertexOf_sigma (f b))
          have hcard : L.dartCount = K.dartCount + 2 :=
            RestrictionGrowth.dartCount_add_two hf a hb
          have hle : L.dartCount ≤ M.dartCount :=
            Nat.card_le_card_of_injective g g.injective
          have hlt : M.dartCount - L.dartCount < n := by omega
          have hbound := ih _ hlt L g rfl hL hconn
            ⟨RestrictionGrowth.oldEmbedding hf a b⟩
          exact hbound.trans (RestrictionGrowth.euler_le hf a hb hK b
            (M.vertexOf_sigma (f b)))
  exact hall _ N e rfl h hN ⟨d⟩

/-- Retaining any connected nonempty submap with the actual induced cyclic
order preserves planarity. -/
theorem planar (h : M.IsRestriction N e) (hM : M.IsPlanar)
    (hN : N.IsConnected) (d : N.Dart) : N.IsPlanar := by
  refine ⟨hN, le_antisymm (N.eulerCharacteristic_le_two hN) ?_⟩
  have hle := h.euler_le hM.1 hN d
  rw [hM.2] at hle
  exact hle

end GroupApproximation.GGT.VanKampen.CombMap.IsRestriction

#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.IsRestriction.euler_le
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.IsRestriction.planar
