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
