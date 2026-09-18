import GroupApproximation.SteinbergFP.Swindle
import GroupApproximation.SteinbergFP.Model
import GroupApproximation.SteinbergFP.Morita
import GroupApproximation.BooneHigman.Metabelian.AbsorptionEmbedding
import GroupApproximation.KOne.FieldKOneDeterminant
import GroupApproximation.Steinberg.Perfect

/-!
# One finitely presented group containing every `GL_n(ℚ)`

`Γ = St_10(R_L)` is finitely presented (`steinberg_isFinitelyPresented`), and every `GL_n(ℚ)`
embeds in it (`exists_injective_gl_steinberg_ten`).  This answers Kourovka Problem 14.10(c)
and Problem 2.7 of Belk–Bleak–Matucci–Zaremsky with an explicit group: the research node
`gl-n-q-all-n-in-st-10-of-resolvent-ring`.

For `k = 2^n`:

    GL_n(ℚ) ↪ E_{3k}(ℚ) ≅ E_3(M_k(ℚ)) ↪ St_10(M_k(R_L)) ≅ St_10(R_L).

* `GL_n(ℚ) ↪ SL_{3k}(ℚ) = E_{3k}(ℚ)`: `g ↦ diag(g, (g⁻¹)ᵀ, 1)`, and `SL = E` over a field.
* `E_{3k}(ℚ) ≅ E_3(M_k(ℚ))`: block flattening.
* `E_3(M_k(ℚ)) ↪ St_10(M_k(R_L))`: the Leavitt swindle (`exists_injective_elementary`) with
  the scalar Leavitt family of `M_k(R_L)`, which commutes with `M_k(ℚ)` because `ℚ` is central
  in `R_L`.
* `St_10(M_k(R_L)) ≅ St_10(R_L)`: the Morita isomorphism `M_k(R_L) ≅ R_L`.
-/

namespace GroupApproximation.SteinbergFP

noncomputable section

open SteinbergGroup

/-- The binary Leavitt family `s₁, s₂, t₁, t₂` of `R_L`. -/
def resolventLeavitt : LeavittFamily ResolventRing where
  s0 := rgen 0
  s1 := rgen 1
  t0 := rgen 2
  t1 := rgen 3
  t0_s0 := isResolventTuple.t₁s₁
  t0_s1 := isResolventTuple.t₁s₂
  t1_s0 := isResolventTuple.t₂s₁
  t1_s1 := isResolventTuple.t₂s₂
  sum_range := isResolventTuple.sum

/-- `ℚ ⊆ R_L`. -/
abbrev resolventRat : ℚ →+* ResolventRing := isResolventTuple.ratHom

/-- `GL_n(ℚ) ↪ E_N(ℚ)` for `2n ≤ N`, `0 < N`. -/
theorem exists_injective_gl_elementary_rat {n N : ℕ} (h : 2 * n ≤ N) (hN : 0 < N) :
    ∃ f : Matrix.GeneralLinearGroup (Fin n) ℚ →* elementaryGroup (Fin N) ℚ,
      Function.Injective f := by
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  refine ⟨(BooneHigman.Metabelian.Absorption.absorptionUnits (R := ℚ) n N h).codRestrict
    (elementaryGroup (Fin N) ℚ) (fun g ↦ AlgebraicK.mem_elementaryGroup_of_detUnits_eq_one
      (Units.ext (BooneHigman.Metabelian.Absorption.absorptionUnits_det n N h g))), ?_⟩
  intro a b hab
  exact BooneHigman.Metabelian.Absorption.absorptionUnits_injective (R := ℚ) n N h
    (congrArg Subtype.val hab)

/-- `M_ι(ℚ) → M_ι(R_L)` commutes with the scalar Leavitt family. -/
theorem matrixRat_commute (ι : Type*) [Fintype ι] [DecidableEq ι] (a : Matrix ι ι ℚ)
    (s : Fin 2) :
    (matrixLeavitt resolventLeavitt ι).tv s * resolventRat.mapMatrix a =
      resolventRat.mapMatrix a * (matrixLeavitt resolventLeavitt ι).tv s := by
  rw [matrixLeavitt_tv]
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, RingHom.mapMatrix_apply, Matrix.map_apply]
  exact (isResolventTuple.ratHom_commute (a i j) (resolventLeavitt.tv s)).eq.symm

theorem card_steinberg_index : Fintype.card (Option (Fin 3 × Fin 3)) = 10 := by
  simp

/-- `GL_n(ℚ) ↪ St_10(R_L)`, given `M_k(R_L) ≅ R_L` with `2n ≤ 3k`. -/
theorem exists_injective_gl_of_matrixEquiv {n k : ℕ} (hk : 2 * n ≤ 3 * k) (hk0 : 0 < k)
    (e : Matrix (Fin k) (Fin k) ResolventRing ≃+* ResolventRing) :
    ∃ f : Matrix.GeneralLinearGroup (Fin n) ℚ →* SteinbergGroup (Fin 10) ResolventRing,
      Function.Injective f := by
  obtain ⟨f₁, hf₁⟩ := exists_injective_gl_elementary_rat hk (by omega)
  let f₂ : elementaryGroup (Fin (3 * k)) ℚ ≃* elementaryGroup (Fin 3 × Fin k) ℚ :=
    elementaryReindexEquiv finProdFinEquiv.symm
  let f₃ : elementaryGroup (Fin 3 × Fin k) ℚ ≃*
      elementaryGroup (Fin 3) (Matrix (Fin k) (Fin k) ℚ) :=
    elementaryBlockEquiv.symm
  haveI : Group.IsPerfect (SteinbergGroup (Fin 3) (Matrix (Fin k) (Fin k) ℚ)) :=
    fin_isPerfect le_rfl
  obtain ⟨f₄, hf₄⟩ := exists_injective_elementary (V := Fin 3)
    (matrixLeavitt resolventLeavitt (Fin k)) resolventRat.mapMatrix
    (fun a s ↦ matrixRat_commute (Fin k) a s)
    (Matrix.map_injective resolventRatHom_injective)
  let f₅ : SteinbergGroup (Option (Fin 3 × Fin 3)) (Matrix (Fin k) (Fin k) ResolventRing) ≃*
      SteinbergGroup (Option (Fin 3 × Fin 3)) ResolventRing :=
    coefficientEquiv e
  let f₆ : SteinbergGroup (Option (Fin 3 × Fin 3)) ResolventRing ≃*
      SteinbergGroup (Fin 10) ResolventRing :=
    reindexEquiv (Fintype.equivFinOfCardEq card_steinberg_index)
  refine ⟨f₆.toMonoidHom.comp (f₅.toMonoidHom.comp (f₄.comp
    (f₃.toMonoidHom.comp (f₂.toMonoidHom.comp f₁)))), ?_⟩
  exact f₆.injective.comp (f₅.injective.comp (hf₄.comp (f₃.injective.comp
    (f₂.injective.comp hf₁))))

/-- **Every `GL_n(ℚ)` embeds in `St_10(R_L)`.** -/
theorem exists_injective_gl_steinberg_ten (n : ℕ) :
    ∃ f : Matrix.GeneralLinearGroup (Fin n) ℚ →* SteinbergGroup (Fin 10) ResolventRing,
      Function.Injective f := by
  have hk : 2 * n ≤ 3 * 2 ^ n := by
    have := Nat.lt_two_pow_self (n := n)
    omega
  exact exists_injective_gl_of_matrixEquiv hk (by positivity) (morita resolventLeavitt n)

/-- **Kourovka 14.10(c), BBMZ Problem 2.7.**  The explicit finitely presented group
`St_10(R_L)` contains every `GL_n(ℚ)`. -/
theorem steinberg_ten_resolvent_contains_all_gl :
    Group.IsFinitelyPresented (SteinbergGroup (Fin 10) ResolventRing) ∧
      ∀ n : ℕ, ∃ f : Matrix.GeneralLinearGroup (Fin n) ℚ →*
        SteinbergGroup (Fin 10) ResolventRing, Function.Injective f :=
  ⟨steinberg_isFinitelyPresented 5, exists_injective_gl_steinberg_ten⟩

end

end GroupApproximation.SteinbergFP

#audit_axioms GroupApproximation.SteinbergFP.exists_injective_gl_steinberg_ten
#audit_axioms GroupApproximation.SteinbergFP.steinberg_ten_resolvent_contains_all_gl
