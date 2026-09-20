import GroupApproximation.BooneHigman.Join.FModelV

/-!
# The lexicographic order on the binary Cantor set (lane bh-pal-met-join)

* `CLt x y`: at the first index where `x` and `y` differ, `x` has `0` and `y` has `1`.  It is
  irreflexive, transitive and total on distinct streams.
* `Before u v`: every stream of the cone of `u` is `CLt` below every stream of the cone of `v`.
  Two incomparable words are always ordered one way or the other (`before_or_before`).
* `IsMono f`: `f` preserves `CLt`.  These permutations form a subgroup `MonoSub`, closed under
  `localize` (`isMono_localize`).
* `isMono_of_three`: a permutation carrying the cones of a three-word complete code rigidly and in
  order onto the cones of another three-word code is monotone.  This gives `IsMono x₀`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace GroupApproximation.BooneHigman.Join

open GroupApproximation.BooneHigman.Metabelian.Envelope

/-- The lexicographic order on streams of binary digits. -/
def CLt (x y : Cantor (Fin 2)) : Prop :=
  ∃ n, (∀ i < n, x i = y i) ∧ x n = 0 ∧ y n = 1

#audit_axioms GroupApproximation.BooneHigman.Join.CLt

theorem fin2_cases (a : Fin 2) : a = 0 ∨ a = 1 := by
  rcases a with ⟨_ | _ | n, hn⟩
  · exact Or.inl rfl
  · exact Or.inr rfl
  · omega

#audit_axioms GroupApproximation.BooneHigman.Join.fin2_cases

theorem fin2_zero_ne_one : (0 : Fin 2) ≠ 1 := by decide

#audit_axioms GroupApproximation.BooneHigman.Join.fin2_zero_ne_one

theorem clt_irrefl (x : Cantor (Fin 2)) : ¬ CLt x x := by
  rintro ⟨n, -, h0, h1⟩
  exact fin2_zero_ne_one (h0.symm.trans h1)

#audit_axioms GroupApproximation.BooneHigman.Join.clt_irrefl

theorem clt_trans {x y z : Cantor (Fin 2)} (h1 : CLt x y) (h2 : CLt y z) : CLt x z := by
  obtain ⟨n, hn, hx, hy⟩ := h1
  obtain ⟨m, hm, hy', hz⟩ := h2
  rcases lt_trichotomy n m with h | h | h
  · exact ⟨n, fun i hi => (hn i hi).trans (hm i (by omega)), hx, (hm n h).symm.trans hy⟩
  · subst h
    exact absurd (hy'.symm.trans hy) fin2_zero_ne_one
  · exact ⟨m, fun i hi => (hn i (by omega)).trans (hm i hi), (hn m h).trans hy', hz⟩

#audit_axioms GroupApproximation.BooneHigman.Join.clt_trans

theorem clt_asymm {x y : Cantor (Fin 2)} (h1 : CLt x y) (h2 : CLt y x) : False :=
  clt_irrefl x (clt_trans h1 h2)

#audit_axioms GroupApproximation.BooneHigman.Join.clt_asymm

theorem clt_total {x y : Cantor (Fin 2)} (h : x ≠ y) : CLt x y ∨ CLt y x := by
  classical
  have hex : ∃ n, x n ≠ y n := by
    by_contra hc
    exact h (funext fun k => by_contra fun hk => hc ⟨k, hk⟩)
  let n := Nat.find hex
  have hne : x n ≠ y n := Nat.find_spec hex
  have hlt : ∀ i < n, x i = y i := fun i hi => by
    by_contra hc
    exact Nat.find_min hex hi hc
  rcases fin2_cases (x n) with h0 | h0 <;> rcases fin2_cases (y n) with h1 | h1
  · exact absurd (h0.trans h1.symm) hne
  · exact Or.inl ⟨n, hlt, h0, h1⟩
  · exact Or.inr ⟨n, fun i hi => (hlt i hi).symm, h1, h0⟩
  · exact absurd (h0.trans h1.symm) hne

#audit_axioms GroupApproximation.BooneHigman.Join.clt_total

theorem clt_prepend (w : List (Fin 2)) {x y : Cantor (Fin 2)} (h : CLt x y) :
    CLt (prepend w x) (prepend w y) := by
  obtain ⟨n, hn, hx, hy⟩ := h
  refine ⟨n + w.length, fun i hi => ?_, ?_, ?_⟩
  · by_cases hw : i < w.length
    · rw [prepend_getElem _ _ hw, prepend_getElem _ _ hw]
    · rw [prepend_of_length_le _ _ hw, prepend_of_length_le _ _ hw]
      exact hn _ (by omega)
  · have hw : ¬ n + w.length < w.length := by omega
    rw [prepend_of_length_le _ _ hw, Nat.add_sub_cancel]
    exact hx
  · have hw : ¬ n + w.length < w.length := by omega
    rw [prepend_of_length_le _ _ hw, Nat.add_sub_cancel]
    exact hy

#audit_axioms GroupApproximation.BooneHigman.Join.clt_prepend

theorem clt_of_prepend (w : List (Fin 2)) {x y : Cantor (Fin 2)}
    (h : CLt (prepend w x) (prepend w y)) : CLt x y := by
  obtain ⟨n, hn, hx, hy⟩ := h
  have hw : ¬ n < w.length := by
    intro hlt
    rw [prepend_getElem _ _ hlt] at hx
    rw [prepend_getElem _ _ hlt] at hy
    exact fin2_zero_ne_one (hx.symm.trans hy)
  refine ⟨n - w.length, fun i hi => ?_, ?_, ?_⟩
  · have h := hn (i + w.length) (by omega)
    have hw' : ¬ i + w.length < w.length := by omega
    rwa [prepend_of_length_le _ _ hw', prepend_of_length_le _ _ hw', Nat.add_sub_cancel] at h
  · rwa [prepend_of_length_le _ _ hw] at hx
  · rwa [prepend_of_length_le _ _ hw] at hy

#audit_axioms GroupApproximation.BooneHigman.Join.clt_of_prepend

/-- Every stream of the cone of `u` lies below every stream of the cone of `v`. -/
def Before (u v : List (Fin 2)) : Prop :=
  ∀ y z : Cantor (Fin 2), CLt (prepend u y) (prepend v z)

#audit_axioms GroupApproximation.BooneHigman.Join.Before

theorem before_of (w u v : List (Fin 2)) : Before (w ++ 0 :: u) (w ++ 1 :: v) := by
  intro y z
  rw [prepend_append, prepend_append]
  refine ⟨w.length, fun i hi => ?_, ?_, ?_⟩
  · rw [prepend_getElem _ _ hi, prepend_getElem _ _ hi]
  · rw [prepend_of_length_le _ _ (Nat.lt_irrefl _), Nat.sub_self,
      prepend_getElem (0 :: u) y (Nat.succ_pos _)]
    all_goals rfl
  · rw [prepend_of_length_le _ _ (Nat.lt_irrefl _), Nat.sub_self,
      prepend_getElem (1 :: v) z (Nat.succ_pos _)]
    all_goals rfl

#audit_axioms GroupApproximation.BooneHigman.Join.before_of

theorem before_irrefl (u : List (Fin 2)) : ¬ Before u u := fun h =>
  clt_irrefl _ (h (fun _ => 0) (fun _ => 0))

#audit_axioms GroupApproximation.BooneHigman.Join.before_irrefl

theorem before_trans {a b c : List (Fin 2)} (h1 : Before a b) (h2 : Before b c) : Before a c :=
  fun y z => clt_trans (h1 y (fun _ => 0)) (h2 (fun _ => 0) z)

#audit_axioms GroupApproximation.BooneHigman.Join.before_trans

theorem before_asymm {a b : List (Fin 2)} (h1 : Before a b) (h2 : Before b a) : False :=
  before_irrefl a (before_trans h1 h2)

#audit_axioms GroupApproximation.BooneHigman.Join.before_asymm

/-- Two incomparable words split after a common prefix. -/
theorem split_of_incomp' : ∀ (u v : List (Fin 2)), ¬ u <+: v → ¬ v <+: u →
    ∃ w u' v' : List (Fin 2), ∃ a b : Fin 2, a ≠ b ∧ u = w ++ a :: u' ∧ v = w ++ b :: v'
  | [], _, h1, _ => absurd List.nil_prefix h1
  | _ :: _, [], _, h2 => absurd List.nil_prefix h2
  | a :: u, b :: v, h1, h2 => by
    by_cases hab : a = b
    · subst hab
      have h1' : ¬ u <+: v := fun h => h1 ((List.prefix_cons_inj a).mpr h)
      have h2' : ¬ v <+: u := fun h => h2 ((List.prefix_cons_inj a).mpr h)
      obtain ⟨w, u', v', c, e, hce, rfl, rfl⟩ := split_of_incomp' u v h1' h2'
      exact ⟨a :: w, u', v', c, e, hce, rfl, rfl⟩
    · exact ⟨[], u, v, a, b, hab, rfl, rfl⟩

#audit_axioms GroupApproximation.BooneHigman.Join.split_of_incomp'

theorem split_of_incomp {u v : List (Fin 2)} (h1 : ¬ u <+: v) (h2 : ¬ v <+: u) :
    ∃ w u' v' : List (Fin 2), ∃ a b : Fin 2, a ≠ b ∧ u = w ++ a :: u' ∧ v = w ++ b :: v' :=
  split_of_incomp' u v h1 h2

#audit_axioms GroupApproximation.BooneHigman.Join.split_of_incomp

theorem before_or_before {u v : List (Fin 2)} (h1 : ¬ u <+: v) (h2 : ¬ v <+: u) :
    Before u v ∨ Before v u := by
  obtain ⟨w, u', v', a, b, hab, rfl, rfl⟩ := split_of_incomp h1 h2
  rcases fin2_cases a with rfl | rfl <;> rcases fin2_cases b with rfl | rfl
  · exact absurd rfl hab
  · exact Or.inl (before_of w u' v')
  · exact Or.inr (before_of w v' u')
  · exact absurd rfl hab

#audit_axioms GroupApproximation.BooneHigman.Join.before_or_before

/-- `f` preserves the lexicographic order. -/
def IsMono (f : Equiv.Perm (Cantor (Fin 2))) : Prop :=
  ∀ x y, CLt x y → CLt (f x) (f y)

#audit_axioms GroupApproximation.BooneHigman.Join.IsMono

theorem IsMono.inv {f : Equiv.Perm (Cantor (Fin 2))} (hf : IsMono f) : IsMono f⁻¹ := by
  intro x y h
  have hne : f⁻¹ x ≠ f⁻¹ y := fun e => clt_irrefl y (by rwa [(f⁻¹).injective e] at h)
  rcases clt_total hne with h' | h'
  · exact h'
  · have h'' := hf _ _ h'
    simp only [perm_apply_inv_self] at h''
    exact (clt_asymm h h'').elim

#audit_axioms GroupApproximation.BooneHigman.Join.IsMono.inv

/-- The monotone permutations. -/
def MonoSub : Subgroup (Equiv.Perm (Cantor (Fin 2))) where
  carrier := {f | IsMono f}
  mul_mem' := by
    intro a b ha hb
    show IsMono (a * b)
    intro x y h
    exact (show IsMono a from ha) _ _ ((show IsMono b from hb) x y h)
  one_mem' := by
    show IsMono 1
    intro x y h
    exact h
  inv_mem' := by
    intro a ha
    show IsMono a⁻¹
    exact IsMono.inv ha

#audit_axioms GroupApproximation.BooneHigman.Join.MonoSub

theorem mem_MonoSub {f : Equiv.Perm (Cantor (Fin 2))} : f ∈ MonoSub ↔ IsMono f := Iff.rfl

#audit_axioms GroupApproximation.BooneHigman.Join.mem_MonoSub

/-- A stream in the cone of `w` agrees with every stream of that cone below `|w|`. -/
theorem prefix_agree {w : List (Fin 2)} {x : Cantor (Fin 2)} (hx : IsStreamPrefix w x)
    (t : Cantor (Fin 2)) : ∀ i < w.length, prepend w t i = x i := fun i hi => by
  rw [prepend_getElem _ _ hi, hx i hi]

#audit_axioms GroupApproximation.BooneHigman.Join.prefix_agree

/-- If `x` is in the cone of `w` and `y` is not, their first difference is inside `w`. -/
theorem clt_index_lt {w : List (Fin 2)} {x y : Cantor (Fin 2)} (hx : IsStreamPrefix w x)
    (hy : ¬ IsStreamPrefix w y) {n : ℕ} (hn : ∀ i < n, x i = y i) : n < w.length := by
  by_contra hc
  exact hy fun k hk => (hn k (by omega)).symm.trans (hx k hk)

#audit_axioms GroupApproximation.BooneHigman.Join.clt_index_lt

theorem isMono_localize (w : List (Fin 2)) {g : Equiv.Perm (Cantor (Fin 2))} (hg : IsMono g) :
    IsMono (localize w g) := by
  intro x y h
  by_cases hx : IsStreamPrefix w x <;> by_cases hy : IsStreamPrefix w y
  · obtain ⟨x', rfl⟩ := mem_cone_iff.mp (mem_cone.mpr hx)
    obtain ⟨y', rfl⟩ := mem_cone_iff.mp (mem_cone.mpr hy)
    rw [localize_apply_prepend, localize_apply_prepend]
    exact clt_prepend w (hg _ _ (clt_of_prepend w h))
  · rw [localize_apply_of_not hy]
    obtain ⟨n, hn, h0, h1⟩ := h
    have hlt := clt_index_lt hx hy hn
    obtain ⟨x', rfl⟩ := mem_cone_iff.mp (mem_cone.mpr hx)
    rw [localize_apply_prepend]
    have ha := prefix_agree hx (g x')
    exact ⟨n, fun i hi => (ha i (by omega)).trans (hn i hi), (ha n hlt).trans h0, h1⟩
  · rw [localize_apply_of_not hx]
    obtain ⟨n, hn, h0, h1⟩ := h
    have hlt := clt_index_lt hy hx (fun i hi => (hn i hi).symm)
    obtain ⟨y', rfl⟩ := mem_cone_iff.mp (mem_cone.mpr hy)
    rw [localize_apply_prepend]
    have ha := prefix_agree hy (g y')
    exact ⟨n, fun i hi => (hn i hi).trans (ha i (by omega)).symm, h0, (ha n hlt).trans h1⟩
  · rw [localize_apply_of_not hx, localize_apply_of_not hy]
    exact h

#audit_axioms GroupApproximation.BooneHigman.Join.isMono_localize

/-- Monotonicity of a map between two ordered cones. -/
theorem clt_image_of_cones {f : Equiv.Perm (Cantor (Fin 2))} {c c' e e' : List (Fin 2)}
    {x y : Cantor (Fin 2)} (hx : IsStreamPrefix c x) (hy : IsStreamPrefix c' y)
    (hm : MapsCone f c e) (hm' : MapsCone f c' e') (himg : c = c' ∧ e = e' ∨ Before e e')
    (h : CLt x y) : CLt (f x) (f y) := by
  obtain ⟨x', rfl⟩ := mem_cone_iff.mp (mem_cone.mpr hx)
  obtain ⟨y', rfl⟩ := mem_cone_iff.mp (mem_cone.mpr hy)
  rw [hm x', hm' y']
  rcases himg with ⟨rfl, rfl⟩ | hb
  · exact clt_prepend _ (clt_of_prepend _ h)
  · exact hb x' y'

#audit_axioms GroupApproximation.BooneHigman.Join.clt_image_of_cones

/-- Streams of later cones are not below streams of earlier cones. -/
theorem clt_cross {c c' : List (Fin 2)} {x y : Cantor (Fin 2)} (hx : IsStreamPrefix c x)
    (hy : IsStreamPrefix c' y) (hb : Before c' c) (h : CLt x y) : False := by
  obtain ⟨x', rfl⟩ := mem_cone_iff.mp (mem_cone.mpr hx)
  obtain ⟨y', rfl⟩ := mem_cone_iff.mp (mem_cone.mpr hy)
  exact clt_asymm h (hb y' x')

#audit_axioms GroupApproximation.BooneHigman.Join.clt_cross

/-- **Monotonicity from a three-cone tree pair.** -/
theorem isMono_of_three {f : Equiv.Perm (Cantor (Fin 2))} {c1 c2 c3 e1 e2 e3 : List (Fin 2)}
    (hcov : ∀ x, IsStreamPrefix c1 x ∨ IsStreamPrefix c2 x ∨ IsStreamPrefix c3 x)
    (m1 : MapsCone f c1 e1) (m2 : MapsCone f c2 e2) (m3 : MapsCone f c3 e3)
    (b12 : Before c1 c2) (b13 : Before c1 c3) (b23 : Before c2 c3)
    (d12 : Before e1 e2) (d13 : Before e1 e3) (d23 : Before e2 e3) : IsMono f := by
  intro x y h
  rcases hcov x with hx | hx | hx <;> rcases hcov y with hy | hy | hy
  · exact clt_image_of_cones hx hy m1 m1 (Or.inl ⟨rfl, rfl⟩) h
  · exact clt_image_of_cones hx hy m1 m2 (Or.inr d12) h
  · exact clt_image_of_cones hx hy m1 m3 (Or.inr d13) h
  · exact (clt_cross hx hy b12 h).elim
  · exact clt_image_of_cones hx hy m2 m2 (Or.inl ⟨rfl, rfl⟩) h
  · exact clt_image_of_cones hx hy m2 m3 (Or.inr d23) h
  · exact (clt_cross hx hy b13 h).elim
  · exact (clt_cross hx hy b23 h).elim
  · exact clt_image_of_cones hx hy m3 m3 (Or.inl ⟨rfl, rfl⟩) h

#audit_axioms GroupApproximation.BooneHigman.Join.isMono_of_three

theorem cover_X0_code (x : Cantor (Fin 2)) :
    IsStreamPrefix [0] x ∨ IsStreamPrefix [1, 0] x ∨ IsStreamPrefix [1, 1] x := by
  rcases fin2_cases (x 0) with h0 | h0
  · left
    intro k hk
    match k, hk with
    | 0, _ => exact h0
    | k + 1, hk => simp at hk
  · right
    rcases fin2_cases (x 1) with h1 | h1
    · left
      intro k hk
      match k, hk with
      | 0, _ => exact h0
      | 1, _ => exact h1
      | k + 2, hk => simp at hk
    · right
      intro k hk
      match k, hk with
      | 0, _ => exact h0
      | 1, _ => exact h1
      | k + 2, hk => simp at hk

#audit_axioms GroupApproximation.BooneHigman.Join.cover_X0_code

theorem isMono_X0 : IsMono (jperm 2 X0) :=
  isMono_of_three cover_X0_code mapsCone_X0_zero mapsCone_X0_one_zero mapsCone_X0_one_one
    (before_of [] [] [0]) (before_of [] [] [1]) (before_of [1] [] [])
    (before_of [0] [] []) (before_of [] [0] []) (before_of [] [1] [])

#audit_axioms GroupApproximation.BooneHigman.Join.isMono_X0

/-- **The lift of `F` acts monotonically.** -/
theorem W_le_MonoSub : W ≤ MonoSub := by
  rintro _ ⟨q, ⟨g, rfl⟩, rfl⟩
  have hK : Subgroup.closure (Set.range (PresentedGroup.of (rels := ThompsonOre.thompsonRels))) ≤
      MonoSub.comap (jEp.comp psi) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    show jEp (psi (PresentedGroup.of i)) ∈ MonoSub
    rw [← ThompsonOre.xn_of, psi_xn]
    rcases i with ⟨_ | _ | n, hn⟩
    · show jEp (Y 0) ∈ MonoSub
      rw [Y_zero]
      exact mem_MonoSub.mpr isMono_X0
    · show jEp (jPhi 2 [1] X0) ∈ MonoSub
      rw [jEp_apply, jperm_jPhi]
      exact mem_MonoSub.mpr (isMono_localize [1] isMono_X0)
    · omega
  rw [PresentedGroup.closure_range_of] at hK
  exact hK (Subgroup.mem_top g)

#audit_axioms GroupApproximation.BooneHigman.Join.W_le_MonoSub

theorem isMono_of_mem_Phi {q : higmanVCCommon_Q 2} (hq : q ∈ Phi) : IsMono (jperm 2 q) :=
  mem_MonoSub.mp (W_le_MonoSub (jEp_mem_W hq))

#audit_axioms GroupApproximation.BooneHigman.Join.isMono_of_mem_Phi

end GroupApproximation.BooneHigman.Join
