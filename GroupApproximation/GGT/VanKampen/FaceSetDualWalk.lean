import GroupApproximation.GGT.VanKampen.FaceSetDualLeaf

/-!
# From equivalence-closure connectivity to bounded walks

The dual connectivity available for a selected face set is stated as an
equivalence closure, while the removable-point theorem needs bounded
reachability inside the carrier.  This file bridges the two for a symmetric
relation whose steps have both endpoints in the carrier, which is exactly the
shape of the selected-face dual.

Everything here is generic finite combinatorics: walks concatenate, a step
prepends to a walk, and a walk reverses when the relation is symmetric.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen
namespace Embedded

universe u

/-- Walks concatenate. -/
theorem ReachIn.trans {α : Type u} {s : Finset α} {r : α → α → Prop}
    {a b : α} {n : ℕ} (hab : ReachIn s r n a b) :
    ∀ (m : ℕ) (c : α), ReachIn s r m b c → ReachIn s r (n + m) a c := by
  intro m
  induction m with
  | zero =>
      intro c h
      have hbc : b = c := reachIn_zero_iff.mp h
      rw [← hbc]
      exact hab
  | succ m ih =>
      intro c h
      rcases reachIn_succ_iff.mp h with h | h
      · exact (ih c h).mono (n + (m + 1)) (by omega)
      · obtain ⟨d, hd, hbd, hdc⟩ := h
        exact reachIn_succ_iff.mpr (Or.inr ⟨d, hd, ih d hbd, hdc⟩)

/-- A step prepends to a walk. -/
theorem ReachIn.head {α : Type u} {s : Finset α} {r : α → α → Prop}
    {a c : α} (ha : a ∈ s) (hac : r a c) :
    ∀ (n : ℕ) (b : α), ReachIn s r n c b → ReachIn s r (n + 1) a b := by
  intro n
  induction n with
  | zero =>
      intro b h
      have hcb : c = b := reachIn_zero_iff.mp h
      refine reachIn_succ_iff.mpr (Or.inr ⟨a, ha, reachIn_refl s r a, ?_⟩)
      rw [← hcb]
      exact hac
  | succ n ih =>
      intro b h
      rcases reachIn_succ_iff.mp h with h | h
      · exact (ih b h).mono (n + 1 + 1) (by omega)
      · obtain ⟨d, hd, hcd, hdb⟩ := h
        exact reachIn_succ_iff.mpr (Or.inr ⟨d, hd, ih d hcd, hdb⟩)

/-- Walks reverse when the relation is symmetric. -/
theorem ReachIn.reverse {α : Type u} {s : Finset α} {r : α → α → Prop}
    (hsymm : ∀ x y : α, r x y → r y x) {a : α} :
    ∀ (n : ℕ) (b : α), b ∈ s → ReachIn s r n a b →
      ∃ m, ReachIn s r m b a := by
  intro n
  induction n with
  | zero =>
      intro b _ h
      exact ⟨0, reachIn_zero_iff.mpr (reachIn_zero_iff.mp h).symm⟩
  | succ n ih =>
      intro b hb h
      rcases reachIn_succ_iff.mp h with h | h
      · exact ih b hb h
      · obtain ⟨c, hc, hac, hcb⟩ := h
        obtain ⟨m, hm⟩ := ih c hc hac
        exact ⟨m + 1, ReachIn.head hb (hsymm c b hcb) m a hm⟩

/-- A nontrivial equivalence-closure connection has both endpoints in the
carrier. -/
theorem eqvGen_endpoints {α : Type u} {s : Finset α} {r : α → α → Prop}
    (hmemL : ∀ x y : α, r x y → x ∈ s) (hmemR : ∀ x y : α, r x y → y ∈ s)
    {a b : α} (h : Relation.EqvGen r a b) : a = b ∨ (a ∈ s ∧ b ∈ s) := by
  induction h with
  | rel x y hxy => exact Or.inr ⟨hmemL x y hxy, hmemR x y hxy⟩
  | refl x => exact Or.inl rfl
  | symm x y _ ih =>
      rcases ih with h | h
      · exact Or.inl h.symm
      · exact Or.inr ⟨h.2, h.1⟩
  | trans x y z _ _ ihxy ihyz =>
      rcases ihxy with h1 | h1
      · rcases ihyz with h2 | h2
        · exact Or.inl (h1.trans h2)
        · refine Or.inr ⟨?_, h2.2⟩
          rw [h1]
          exact h2.1
      · rcases ihyz with h2 | h2
        · refine Or.inr ⟨h1.1, ?_⟩
          rw [← h2]
          exact h1.2
        · exact Or.inr ⟨h1.1, h2.2⟩

/-- Equivalence-closure connectivity gives bounded reachability inside the
carrier, for a symmetric relation whose steps stay in the carrier. -/
theorem reachIn_of_eqvGen {α : Type u} {s : Finset α} {r : α → α → Prop}
    (hsymm : ∀ x y : α, r x y → r y x)
    (hmemL : ∀ x y : α, r x y → x ∈ s) (hmemR : ∀ x y : α, r x y → y ∈ s) :
    ∀ {a b : α}, Relation.EqvGen r a b → a ∈ s → ∃ n, ReachIn s r n a b := by
  intro a b h
  induction h with
  | rel x y hxy =>
      intro hx
      exact ⟨1, reachIn_succ_iff.mpr
        (Or.inr ⟨x, hx, reachIn_refl s r x, hxy⟩)⟩
  | refl x => exact fun _ => ⟨0, reachIn_refl s r x⟩
  | symm x y hxy ih =>
      intro hy
      rcases eqvGen_endpoints hmemL hmemR hxy with heq | hmem
      · exact ⟨0, reachIn_zero_iff.mpr heq.symm⟩
      · obtain ⟨n, hn⟩ := ih hmem.1
        exact ReachIn.reverse hsymm n y hy hn
  | trans x y z hxy _ ihxy ihyz =>
      intro hx
      obtain ⟨n, hn⟩ := ihxy hx
      have hy : y ∈ s := by
        rcases eqvGen_endpoints hmemL hmemR hxy with heq | hmem
        · rw [← heq]
          exact hx
        · exact hmem.2
      obtain ⟨m, hm⟩ := ihyz hy
      exact ⟨n + m, hn.trans m z hm⟩

/-- The removable-point theorem, stated for a symmetric relation given by an
equivalence closure.  This is the form the selected-face dual supplies. -/
theorem exists_erase_eqvGen {α : Type u} [DecidableEq α]
    (s : Finset α) (r : α → α → Prop)
    (hsymm : ∀ x y : α, r x y → r y x)
    (hmemL : ∀ x y : α, r x y → x ∈ s) (hmemR : ∀ x y : α, r x y → y ∈ s)
    (root : α) (hroot : root ∈ s)
    (hconn : ∀ b ∈ s, Relation.EqvGen r root b)
    (hcard : 1 < s.card) :
    ∃ f, f ∈ s ∧ f ≠ root ∧
      ∀ b ∈ s, b ≠ f → ∃ n, ReachIn (s.erase f) r n root b := by
  refine exists_erase_reachable s r root hroot ?_ hcard
  intro b hb
  exact reachIn_of_eqvGen hsymm hmemL hmemR (hconn b hb) hroot

end Embedded
end VanKampen
end GGT
end GroupApproximation
