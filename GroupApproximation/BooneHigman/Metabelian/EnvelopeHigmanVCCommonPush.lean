import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCCommonSplit
import GroupApproximation.Meta.AxiomGuard

/-!
# All-swaps presentation: pushing deep letters through a word (lane bh-met-77d)

For a word `g` of the all-swaps free group, let `σ_g` (`higmanVCCommon_perm d g`) be its
permutation of the boundary.  `HigmanVCCommonPush d g N` says: for incomparable `x`, `y` with
`|x|, |y| ≥ N`, `σ_g` carries the cones of `x`, `y` onto the cones of some `x'`, `y'` by prefix
substitution, with `|x| ≤ |x'| + N` and `|y| ≤ |y'| + N`, and modulo the standard relators
`g (x, y) g⁻¹ = (x', y')`.

`higmanVCCommon_push`: every word has such an `N`.  For a letter `(u, v)` take
`N = max |u| |v|`; the conjugation relator gives the identity when `u`, `v` are incomparable, and
the letter is trivial otherwise.  The inverse of a letter acts as the letter.  Thresholds add
under products.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- The permutation of the boundary induced by a word of the all-swaps free group. -/
noncomputable def higmanVCCommon_perm (d : ℕ) (g : FreeGroup (List (Fin d) × List (Fin d))) :
    Equiv.Perm (Cantor (Fin d)) :=
  (higmanVC_evalAll d g : ↥(higmanThompsonV (Fin d)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCCommon_perm

theorem higmanVCCommon_perm_one (d : ℕ) : higmanVCCommon_perm d 1 = 1 :=
  congrArg Subtype.val (map_one (higmanVC_evalAll d))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCCommon_perm_one

theorem higmanVCCommon_perm_mul {d : ℕ} (g₁ g₂ : FreeGroup (List (Fin d) × List (Fin d))) :
    higmanVCCommon_perm d (g₁ * g₂) = higmanVCCommon_perm d g₁ * higmanVCCommon_perm d g₂ :=
  congrArg Subtype.val (map_mul (higmanVC_evalAll d) g₁ g₂)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCCommon_perm_mul

theorem higmanVCCommon_perm_of {d : ℕ} (u v : List (Fin d)) :
    higmanVCCommon_perm d (FreeGroup.of (u, v)) =
      ((vgenSwapOrOne u v : ↥(higmanThompsonV (Fin d))) : Equiv.Perm (Cantor (Fin d))) :=
  congrArg Subtype.val (higmanVC_evalAll_of u v)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCCommon_perm_of

/-- The inverse of a letter induces the same permutation as the letter. -/
theorem higmanVCCommon_perm_inv_of {d : ℕ} (u v : List (Fin d)) :
    higmanVCCommon_perm d (FreeGroup.of (u, v))⁻¹ =
      higmanVCCommon_perm d (FreeGroup.of (u, v)) := by
  have h : higmanVC_evalAll d (FreeGroup.of (u, v))⁻¹ =
      higmanVC_evalAll d (FreeGroup.of (u, v)) := by
    rw [map_inv, higmanVC_evalAll_of]
    exact inv_eq_of_mul_eq_one_right (higmanVFP_swapOrOne_mul_self u v)
  exact congrArg Subtype.val h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCCommon_perm_inv_of

/-- A permutation carrying the cones of incomparable words onto cones carries them onto the
cones of incomparable words. -/
theorem higmanVCCommon_incomp_image {d : ℕ} (hd : 0 < d) {f : Equiv.Perm (Cantor (Fin d))}
    {x y x' y' : List (Fin d)} (hx : MapsCone f x x') (hy : MapsCone f y y')
    (hxy : ¬ x <+: y) (hyx : ¬ y <+: x) : ¬ x' <+: y' := by
  rintro ⟨c, rfl⟩
  have s : Cantor (Fin d) := fun _ => ⟨0, hd⟩
  have e : prepend y s = prepend x (prepend c s) := by
    apply f.injective
    rw [hy s, hx (prepend c s), prepend_append]
  have h1 : IsStreamPrefix y (prepend y s) := isStreamPrefix_prepend y s
  have h2 : IsStreamPrefix x (prepend y s) := by
    rw [e]
    exact isStreamPrefix_prepend x (prepend c s)
  rcases prefix_or_prefix_of_isStreamPrefix h1 h2 with h | h
  · exact hyx h
  · exact hxy h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCCommon_incomp_image

/-- A permutation of depth `N` carries the cone of a word `x` of length `≥ N` onto the cone of a
word `x'` with `|x| ≤ |x'| + N`. -/
theorem higmanVCCommon_hasDepth_len {d N : ℕ} {f : Equiv.Perm (Cantor (Fin d))}
    (h : HasDepth f N) {x : List (Fin d)} (hx : N ≤ x.length) :
    ∃ x', MapsCone f x x' ∧ x.length ≤ x'.length + N := by
  obtain ⟨v, hv⟩ := h (x.take N) (List.length_take_of_le hx)
  refine ⟨v ++ x.drop N, ?_, ?_⟩
  · have h' := hv.append (x.drop N)
    rw [List.take_append_drop] at h'
    exact h'
  · rw [List.length_append, List.length_drop]
    omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCCommon_hasDepth_len

/-- **Push property** of a word `g` at threshold `N`. -/
def HigmanVCCommonPush (d : ℕ) (g : FreeGroup (List (Fin d) × List (Fin d))) (N : ℕ) : Prop :=
  ∀ x y : List (Fin d), N ≤ x.length → N ≤ y.length → ¬ x <+: y → ¬ y <+: x →
    ∃ x' y' : List (Fin d), MapsCone (higmanVCCommon_perm d g) x x' ∧
      MapsCone (higmanVCCommon_perm d g) y y' ∧ x.length ≤ x'.length + N ∧
      y.length ≤ y'.length + N ∧
      higmanVCCommon_mk d (g * FreeGroup.of (x, y) * g⁻¹) =
        higmanVCCommon_mk d (FreeGroup.of (x', y'))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.HigmanVCCommonPush

theorem higmanVCCommon_push_one (d : ℕ) : HigmanVCCommonPush d 1 0 := by
  intro x y _ _ _ _
  refine ⟨x, y, ?_, ?_, Nat.le_add_right _ _, Nat.le_add_right _ _, ?_⟩
  · rw [higmanVCCommon_perm_one]
    exact mapsCone_one x
  · rw [higmanVCCommon_perm_one]
    exact mapsCone_one y
  · rw [inv_one, mul_one, one_mul]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCCommon_push_one

/-- The conjugation relator, as a membership. -/
theorem higmanVCCommon_conj_mem {d : ℕ} {p q x y x' y' : List (Fin d)} (hpq : ¬ p <+: q)
    (hqp : ¬ q <+: p) (hmx : MapsCone (coneSwap p q hpq hqp) x x')
    (hmy : MapsCone (coneSwap p q hpq hqp) y y') (hxy : ¬ x <+: y) (hyx : ¬ y <+: x)
    (hxy' : ¬ x' <+: y') (hyx' : ¬ y' <+: x') :
    FreeGroup.of (p, q) * FreeGroup.of (x, y) * (FreeGroup.of (p, q))⁻¹ *
      (FreeGroup.of (x', y'))⁻¹ ∈ higmanVC_rels d fun _ => True := by
  rw [higmanVC_rels, Set.mem_setOf_eq]
  exact Or.inr (Or.inr (Or.inl ⟨p, q, x, y, x', y', trivial, trivial, trivial, trivial, trivial,
    trivial, hpq, hqp, hmx, hmy, hxy, hyx, hxy', hyx', rfl⟩))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCCommon_conj_mem

/-- **Push for a letter** `(u, v)`, at threshold `max |u| |v|`. -/
theorem higmanVCCommon_push_of {d : ℕ} (hd : 1 < d) (u v : List (Fin d)) :
    HigmanVCCommonPush d (FreeGroup.of (u, v)) (max u.length v.length) := by
  intro x y hx hy hxy hyx
  by_cases h : ¬ u <+: v ∧ ¬ v <+: u
  · have e : higmanVCCommon_perm d (FreeGroup.of (u, v)) = coneSwap u v h.1 h.2 :=
      (higmanVCCommon_perm_of u v).trans (congrArg Subtype.val (vgenSwapOrOne_eq h.1 h.2))
    have hD : HasDepth (higmanVCCommon_perm d (FreeGroup.of (u, v)))
        (max u.length v.length) := by
      rw [e]
      exact coneSwap_hasDepth h.1 h.2
    obtain ⟨x', hx', hlx⟩ := higmanVCCommon_hasDepth_len hD hx
    obtain ⟨y', hy', hly⟩ := higmanVCCommon_hasDepth_len hD hy
    refine ⟨x', y', hx', hy', hlx, hly, ?_⟩
    have hmx : MapsCone (coneSwap u v h.1 h.2) x x' := by
      rw [← e]
      exact hx'
    have hmy : MapsCone (coneSwap u v h.1 h.2) y y' := by
      rw [← e]
      exact hy'
    have hr := higmanVCCommon_mk_rel (higmanVCCommon_conj_mem h.1 h.2 hmx hmy hxy hyx
      (higmanVCCommon_incomp_image (by omega) hx' hy' hxy hyx)
      (higmanVCCommon_incomp_image (by omega) hy' hx' hyx hxy))
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at hr
    rw [map_mul, map_mul, map_inv]
    exact mul_inv_eq_one.mp hr
  · have e : higmanVCCommon_perm d (FreeGroup.of (u, v)) = 1 :=
      (higmanVCCommon_perm_of u v).trans (congrArg Subtype.val (higmanVFP_swapOrOne_of_not h))
    refine ⟨x, y, ?_, ?_, Nat.le_add_right _ _, Nat.le_add_right _ _, ?_⟩
    · rw [e]
      exact mapsCone_one x
    · rw [e]
      exact mapsCone_one y
    · rw [map_mul, map_mul, map_inv, higmanVCCommon_mk_comparable h, inv_one, mul_one, one_mul]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCCommon_push_of

/-- The push property only depends on the permutation and on the class modulo the relators. -/
theorem higmanVCCommon_push_congr {d N : ℕ} {g g' : FreeGroup (List (Fin d) × List (Fin d))}
    (h : HigmanVCCommonPush d g N) (hp : higmanVCCommon_perm d g = higmanVCCommon_perm d g')
    (hm : higmanVCCommon_mk d g = higmanVCCommon_mk d g') : HigmanVCCommonPush d g' N := by
  intro x y hx hy hxy hyx
  obtain ⟨x', y', h1, h2, h3, h4, h5⟩ := h x y hx hy hxy hyx
  refine ⟨x', y', ?_, ?_, h3, h4, ?_⟩
  · rw [← hp]
    exact h1
  · rw [← hp]
    exact h2
  · rw [← h5, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hm]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCCommon_push_congr

/-- **Push for the inverse of a letter**, at the threshold of the letter. -/
theorem higmanVCCommon_push_inv_of {d : ℕ} (hd : 1 < d) (u v : List (Fin d)) :
    HigmanVCCommonPush d (FreeGroup.of (u, v))⁻¹ (max u.length v.length) :=
  higmanVCCommon_push_congr (higmanVCCommon_push_of hd u v) (higmanVCCommon_perm_inv_of u v).symm
    (higmanVCCommon_mk_inv_of u v).symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCCommon_push_inv_of

/-- **Push for a product**: thresholds add. -/
theorem higmanVCCommon_push_mul {d N₁ N₂ : ℕ} (hd : 0 < d)
    {g₁ g₂ : FreeGroup (List (Fin d) × List (Fin d))} (h₁ : HigmanVCCommonPush d g₁ N₁)
    (h₂ : HigmanVCCommonPush d g₂ N₂) : HigmanVCCommonPush d (g₁ * g₂) (N₁ + N₂) := by
  intro x y hx hy hxy hyx
  obtain ⟨x₂, y₂, hx₂, hy₂, hlx₂, hly₂, he₂⟩ := h₂ x y (by omega) (by omega) hxy hyx
  obtain ⟨x₁, y₁, hx₁, hy₁, hlx₁, hly₁, he₁⟩ := h₁ x₂ y₂ (by omega) (by omega)
    (higmanVCCommon_incomp_image hd hx₂ hy₂ hxy hyx)
    (higmanVCCommon_incomp_image hd hy₂ hx₂ hyx hxy)
  refine ⟨x₁, y₁, ?_, ?_, by omega, by omega, ?_⟩
  · rw [higmanVCCommon_perm_mul]
    exact hx₂.comp hx₁
  · rw [higmanVCCommon_perm_mul]
    exact hy₂.comp hy₁
  · have key : higmanVCCommon_mk d (g₁ * g₂ * FreeGroup.of (x, y) * (g₁ * g₂)⁻¹) =
        higmanVCCommon_mk d g₁ * higmanVCCommon_mk d (g₂ * FreeGroup.of (x, y) * g₂⁻¹) *
          (higmanVCCommon_mk d g₁)⁻¹ := by
      simp only [map_mul, map_inv, mul_inv_rev, mul_assoc]
    have he₁' : higmanVCCommon_mk d g₁ * higmanVCCommon_mk d (FreeGroup.of (x₂, y₂)) *
        (higmanVCCommon_mk d g₁)⁻¹ = higmanVCCommon_mk d (FreeGroup.of (x₁, y₁)) := by
      rw [← he₁, map_mul, map_mul, map_inv]
    rw [key, he₂, he₁']

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCCommon_push_mul

/-- **Pushing lemma.**  Every word of the all-swaps free group has the push property at some
threshold. -/
theorem higmanVCCommon_push {d : ℕ} (hd : 1 < d) (g : FreeGroup (List (Fin d) × List (Fin d))) :
    ∃ N, HigmanVCCommonPush d g N := by
  induction g using FreeGroup.induction_on with
  | C1 => exact ⟨0, higmanVCCommon_push_one d⟩
  | of p =>
    obtain ⟨u, v⟩ := p
    exact ⟨_, higmanVCCommon_push_of hd u v⟩
  | inv_of p _ =>
    obtain ⟨u, v⟩ := p
    exact ⟨_, higmanVCCommon_push_inv_of hd u v⟩
  | mul g₁ g₂ ih₁ ih₂ =>
    obtain ⟨N₁, h₁⟩ := ih₁
    obtain ⟨N₂, h₂⟩ := ih₂
    exact ⟨N₁ + N₂, higmanVCCommon_push_mul (by omega) h₁ h₂⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCCommon_push

end GroupApproximation.BooneHigman.Metabelian.Envelope
