import GroupApproximation.Sofic.MappingTelescopeFiniteOrbits
import GroupApproximation.Sofic.SoficTelescope
import GroupApproximation.Sofic.VerticalAscendingHNN
import GroupApproximation.Meta.AxiomGuard

/-!
# Telescope levels in the proof that the Clifford witness is locally RF

`non_mf_groups_exist.tex`, proof of `prop:clifford-locally-rf`, lines 2025--2029:

> For $n\ge0$, write $\Gamma_n=t^{-n}\Gamma t^n$ for the image of the $n$th
> copy of $\Gamma$ in $T_\alpha$.  Since $[\Gamma:\alpha(\Gamma)]<\infty$,
> each $\Gamma_n$ has finite index in $\Gamma_{n+1}$; every element of
> $T_\alpha$ lies in some $\Gamma_m$, and conjugation by $t$ maps
> $\Gamma_{m+1}$ onto $\Gamma_m$, so $\Gamma$ is commensurated by $V$.

In the corpus `T_α = Telescope α hα`, its `n`th copy of `Γ` is
`(level α hα n).range`, `V = Vertical α hα = T_α ⋊ ℤ`, the stable letter is
`tVertical α hα` and `Γ ⊆ V` is `baseSubgroup α hα = (iotaVertical α hα).range`.

Proof route.
* Definition sentence: the vertical image `verticalLevel α hα n` of the `n`th
  copy is exactly the set of conjugates `t^{-n} γ t^n`
  (`VerticalAscendingHNN.inl_level_eq_conj`).
* Finite relative index of consecutive levels is
  `MappingTelescopeFiniteOrbits.level_relIndex_ne_zero`. Exhaustion is
  `exists_level_repr`. Conjugation by `t` sending level `m+1` onto level `m` comes
  from `inl_level_succ`. Commensuration of `Γ` by all of `V` is
  `vertical_le_commensurator`.
-/

namespace GroupApproximation.Manuscript.NonMF.AuditClifford2

open MappingTelescope MarkedCompression MappingTelescopeFiniteOrbits SemidirectProduct

universe u

variable {Γ : Type u} [Group Γ] (α : Γ →* Γ) (hα : Function.Injective α)

/-- tex 2025: `Γ_n = t^{-n} Γ t^n` is the image of the `n`th copy of `Γ`: the
vertical image of the `n`th telescope level is the image of `(level α hα n).range`
under the inclusion `T_α → V`, and it consists exactly of the conjugates
`t^{-n} γ t^n` of elements `γ ∈ Γ`. -/
theorem manuscriptSentence_levelCopyConjugate (n : ℕ) :
    verticalLevel α hα n =
        (level α hα n).range.map (inl : Telescope α hα →* Vertical α hα) ∧
      ∀ v : Vertical α hα, v ∈ verticalLevel α hα n ↔
        ∃ γ : Γ, (tVertical α hα ^ n)⁻¹ * iotaVertical α hα γ * tVertical α hα ^ n = v := by
  refine ⟨verticalLevel_eq_map α hα n, fun v ↦ ?_⟩
  constructor
  · rintro ⟨γ, rfl⟩
    exact ⟨γ, (VerticalAscendingHNN.inl_level_eq_conj α hα n γ).symm⟩
  · rintro ⟨γ, rfl⟩
    exact ⟨γ, VerticalAscendingHNN.inl_level_eq_conj α hα n γ⟩

#audit_axioms manuscriptSentence_levelCopyConjugate

/-- tex 2026--2029: if `[Γ : α(Γ)] < ∞`, then
* each `Γ_n` has finite index in `Γ_{n+1}`;
* every element of `T_α` lies in some `Γ_m`;
* conjugation by `t` maps `Γ_{m+1}` onto `Γ_m` (in `V`);
* `Γ` is commensurated by all of `V`. -/
theorem manuscriptSentence_levelsCommensurateBase [α.range.FiniteIndex] :
    (∀ n : ℕ, (level α hα n).range.relIndex (level α hα (n + 1)).range ≠ 0) ∧
      (∀ g : Telescope α hα, ∃ m : ℕ, g ∈ (level α hα m).range) ∧
      (∀ (m : ℕ) (w : Vertical α hα), w ∈ verticalLevel α hα m ↔
        ∃ v ∈ verticalLevel α hα (m + 1),
          tVertical α hα * v * (tVertical α hα)⁻¹ = w) ∧
      (⊤ : Subgroup (Vertical α hα)) ≤
        Subgroup.Commensurable.commensurator (baseSubgroup α hα) := by
  refine ⟨fun n ↦ level_relIndex_ne_zero α hα (Nat.le_succ n), fun g ↦ ?_,
    fun m w ↦ ?_, vertical_le_commensurator α hα⟩
  · obtain ⟨m, x, hx⟩ := exists_level_repr α hα g
    exact ⟨m, x, hx⟩
  · constructor
    · rintro ⟨γ, rfl⟩
      refine ⟨inl (level α hα (m + 1) γ), ⟨γ, rfl⟩, ?_⟩
      rw [inl_level_succ]
      simp only [MonoidHom.comp_apply, mul_assoc, mul_inv_cancel, mul_one,
        mul_inv_cancel_left]
    · rintro ⟨_, ⟨γ, rfl⟩, rfl⟩
      refine ⟨γ, ?_⟩
      show (inl (level α hα m γ) : Vertical α hα) =
        tVertical α hα * inl (level α hα (m + 1) γ) * (tVertical α hα)⁻¹
      rw [inl_level_succ]
      simp only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left]

#audit_axioms manuscriptSentence_levelsCommensurateBase

end GroupApproximation.Manuscript.NonMF.AuditClifford2
