import GroupApproximation.BooneHigman.Join.DBase

/-!
# The lexicographic order on streams over `Fin d` (lane bh-pal-met-join)

`DLt x y`: `x` and `y` agree below some index where `x` is smaller.  It is a strict total
order (`dlt_irrefl`, `dlt_trans`, `dlt_total`), and prefixing preserves and reflects it.
`DBefore u v`: every stream of the cone of `u` lies below every stream of the cone of `v`.
Incomparable words are `DBefore`-comparable (`dbefore_or_dbefore`).
`DMono f`: `f` preserves `DLt`.  These are closed under inverses and products.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace GroupApproximation.BooneHigman.Join

open GroupApproximation.BooneHigman.Metabelian.Envelope

variable {d : ℕ}

/-- The lexicographic order on streams. -/
def DLt (x y : Cantor (Fin d)) : Prop :=
  ∃ k, (∀ i < k, x i = y i) ∧ x k < y k

#audit_axioms GroupApproximation.BooneHigman.Join.DLt

theorem dlt_irrefl (x : Cantor (Fin d)) : ¬ DLt x x := by
  rintro ⟨k, -, h⟩
  exact lt_irrefl _ h

#audit_axioms GroupApproximation.BooneHigman.Join.dlt_irrefl

theorem dlt_trans {x y z : Cantor (Fin d)} (h1 : DLt x y) (h2 : DLt y z) : DLt x z := by
  obtain ⟨k, hk, hx⟩ := h1
  obtain ⟨m, hm, hy⟩ := h2
  rcases lt_trichotomy k m with h | h | h
  · exact ⟨k, fun i hi => (hk i hi).trans (hm i (by omega)), by rw [← hm k h]; exact hx⟩
  · subst h
    exact ⟨k, fun i hi => (hk i hi).trans (hm i hi), hx.trans hy⟩
  · exact ⟨m, fun i hi => (hk i (by omega)).trans (hm i hi), by rw [hk m h]; exact hy⟩

#audit_axioms GroupApproximation.BooneHigman.Join.dlt_trans

theorem dlt_asymm {x y : Cantor (Fin d)} (h1 : DLt x y) (h2 : DLt y x) : False :=
  dlt_irrefl x (dlt_trans h1 h2)

#audit_axioms GroupApproximation.BooneHigman.Join.dlt_asymm

theorem dlt_total {x y : Cantor (Fin d)} (h : x ≠ y) : DLt x y ∨ DLt y x := by
  classical
  have hex : ∃ k, x k ≠ y k := by
    by_contra hc
    exact h (funext fun k => by_contra fun hk => hc ⟨k, hk⟩)
  have hne : x (Nat.find hex) ≠ y (Nat.find hex) := Nat.find_spec hex
  have hlt : ∀ i < Nat.find hex, x i = y i := fun i hi => by
    by_contra hc
    exact Nat.find_min hex hi hc
  rcases lt_or_gt_of_ne hne with h' | h'
  · exact Or.inl ⟨_, hlt, h'⟩
  · exact Or.inr ⟨_, fun i hi => (hlt i hi).symm, h'⟩

#audit_axioms GroupApproximation.BooneHigman.Join.dlt_total

theorem dlt_prepend (w : List (Fin d)) {x y : Cantor (Fin d)} (h : DLt x y) :
    DLt (prepend w x) (prepend w y) := by
  obtain ⟨k, hk, hxy⟩ := h
  refine ⟨k + w.length, fun i hi => ?_, ?_⟩
  · by_cases hw : i < w.length
    · rw [prepend_getElem _ _ hw, prepend_getElem _ _ hw]
    · rw [prepend_of_length_le _ _ hw, prepend_of_length_le _ _ hw]
      exact hk _ (by omega)
  · have hw : ¬ k + w.length < w.length := by omega
    rw [prepend_of_length_le _ _ hw, prepend_of_length_le _ _ hw, Nat.add_sub_cancel]
    exact hxy

#audit_axioms GroupApproximation.BooneHigman.Join.dlt_prepend

theorem dlt_of_prepend (w : List (Fin d)) {x y : Cantor (Fin d)}
    (h : DLt (prepend w x) (prepend w y)) : DLt x y := by
  obtain ⟨k, hk, hxy⟩ := h
  have hw : ¬ k < w.length := by
    intro hlt
    rw [prepend_getElem _ _ hlt, prepend_getElem _ _ hlt] at hxy
    exact lt_irrefl _ hxy
  refine ⟨k - w.length, fun i hi => ?_, ?_⟩
  · have h := hk (i + w.length) (by omega)
    have hw' : ¬ i + w.length < w.length := by omega
    rwa [prepend_of_length_le _ _ hw', prepend_of_length_le _ _ hw', Nat.add_sub_cancel] at h
  · rwa [prepend_of_length_le _ _ hw, prepend_of_length_le _ _ hw] at hxy

#audit_axioms GroupApproximation.BooneHigman.Join.dlt_of_prepend

/-- Every stream of the cone of `u` lies below every stream of the cone of `v`. -/
def DBefore (u v : List (Fin d)) : Prop :=
  ∀ y z : Cantor (Fin d), DLt (prepend u y) (prepend v z)

#audit_axioms GroupApproximation.BooneHigman.Join.DBefore

theorem dbefore_of (w u v : List (Fin d)) {a b : Fin d} (hab : a < b) :
    DBefore (w ++ a :: u) (w ++ b :: v) := by
  intro y z
  rw [prepend_append, prepend_append]
  refine ⟨w.length, fun i hi => ?_, ?_⟩
  · rw [prepend_getElem _ _ hi, prepend_getElem _ _ hi]
  · rw [prepend_of_length_le _ _ (Nat.lt_irrefl _), prepend_of_length_le _ _ (Nat.lt_irrefl _),
      Nat.sub_self, prepend_getElem (a :: u) y (Nat.succ_pos _),
      prepend_getElem (b :: v) z (Nat.succ_pos _)]
    exact hab

#audit_axioms GroupApproximation.BooneHigman.Join.dbefore_of

theorem dbefore_irrefl [NeZero d] (u : List (Fin d)) : ¬ DBefore u u := fun h =>
  dlt_irrefl _ (h (fun _ => 0) (fun _ => 0))

#audit_axioms GroupApproximation.BooneHigman.Join.dbefore_irrefl

theorem dbefore_trans [NeZero d] {a b c : List (Fin d)} (h1 : DBefore a b) (h2 : DBefore b c) :
    DBefore a c :=
  fun y z => dlt_trans (h1 y (fun _ => 0)) (h2 (fun _ => 0) z)

#audit_axioms GroupApproximation.BooneHigman.Join.dbefore_trans

theorem dsplit_of_incomp : ∀ (u v : List (Fin d)), ¬ u <+: v → ¬ v <+: u →
    ∃ w u' v' : List (Fin d), ∃ a b : Fin d, a ≠ b ∧ u = w ++ a :: u' ∧ v = w ++ b :: v'
  | [], _, h1, _ => absurd List.nil_prefix h1
  | _ :: _, [], _, h2 => absurd List.nil_prefix h2
  | a :: u, b :: v, h1, h2 => by
    by_cases hab : a = b
    · subst hab
      have h1' : ¬ u <+: v := fun h => h1 ((List.prefix_cons_inj a).mpr h)
      have h2' : ¬ v <+: u := fun h => h2 ((List.prefix_cons_inj a).mpr h)
      obtain ⟨w, u', v', c, e, hce, rfl, rfl⟩ := dsplit_of_incomp u v h1' h2'
      exact ⟨a :: w, u', v', c, e, hce, rfl, rfl⟩
    · exact ⟨[], u, v, a, b, hab, rfl, rfl⟩

#audit_axioms GroupApproximation.BooneHigman.Join.dsplit_of_incomp

theorem dbefore_or_dbefore {u v : List (Fin d)} (h1 : ¬ u <+: v) (h2 : ¬ v <+: u) :
    DBefore u v ∨ DBefore v u := by
  obtain ⟨w, u', v', a, b, hab, rfl, rfl⟩ := dsplit_of_incomp u v h1 h2
  rcases lt_or_gt_of_ne hab with h | h
  · exact Or.inl (dbefore_of w u' v' h)
  · exact Or.inr (dbefore_of w v' u' h)

#audit_axioms GroupApproximation.BooneHigman.Join.dbefore_or_dbefore

/-- `f` preserves the lexicographic order. -/
def DMono (f : Equiv.Perm (Cantor (Fin d))) : Prop :=
  ∀ x y, DLt x y → DLt (f x) (f y)

#audit_axioms GroupApproximation.BooneHigman.Join.DMono

theorem DMono.inv {f : Equiv.Perm (Cantor (Fin d))} (hf : DMono f) : DMono f⁻¹ := by
  intro x y h
  have hne : f⁻¹ x ≠ f⁻¹ y := fun e => dlt_irrefl y (by rwa [(f⁻¹).injective e] at h)
  rcases dlt_total hne with h' | h'
  · exact h'
  · have h'' := hf _ _ h'
    simp only [perm_apply_inv_self] at h''
    exact (dlt_asymm h h'').elim

#audit_axioms GroupApproximation.BooneHigman.Join.DMono.inv

theorem DMono.mul {f g : Equiv.Perm (Cantor (Fin d))} (hf : DMono f) (hg : DMono g) :
    DMono (f * g) := fun x y h => hf _ _ (hg _ _ h)

#audit_axioms GroupApproximation.BooneHigman.Join.DMono.mul

end GroupApproximation.BooneHigman.Join
