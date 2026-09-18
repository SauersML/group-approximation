import GroupApproximation.BooneHigman.Metabelian.VdKOmegaBuildMove
import GroupApproximation.Meta.AxiomGuard

/-!
# Building `Ω`, part 2: one identity gives the whole mixed relation

Lane `bh-met-92v`.  Assume `α` and `β` agree on `St_n(R)` and `3 ≤ n`.  Then the whole
family `vdkOmega_Mixed α β` (`n (n - 1) |R|²` identities) follows from the **single**
permutation identity

  `vdkOmegaBuild_MixedOne α β i₀ j₀ h : ⁅x_{i₀,last}(1), x_{last,j₀}(1)⁆ = x_{i₀ j₀}(1)`

at one index pair `i₀ ≠ j₀` (`vdkOmegaBuild_mixed_of_mixedOne`).  The proof moves the
relation around with `vdkOmegaBuild_moveSnd` and `vdkOmegaBuild_moveFst`, so it uses only the
semidirect-product relators and the Steinberg relators of `St_n(R)`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open scoped commutatorElement

variable {n : ℕ} {R : Type*} [CommRing R] {G : Type*} [Group G]

/-- Among `n ≥ 3` indices there is always one avoiding two given ones. -/
theorem vdkOmegaBuild_exists_third (hn : 3 ≤ n) (a b : Fin n) :
    ∃ c : Fin n, c ≠ a ∧ c ≠ b := by
  have key : (0 ≠ a.val ∧ 0 ≠ b.val) ∨ (1 ≠ a.val ∧ 1 ≠ b.val) ∨
      (2 ≠ a.val ∧ 2 ≠ b.val) := by
    omega
  rcases key with h | h | h
  · exact ⟨⟨0, by omega⟩, fun e ↦ h.1 (congrArg Fin.val e), fun e ↦ h.2 (congrArg Fin.val e)⟩
  · exact ⟨⟨1, by omega⟩, fun e ↦ h.1 (congrArg Fin.val e), fun e ↦ h.2 (congrArg Fin.val e)⟩
  · exact ⟨⟨2, by omega⟩, fun e ↦ h.1 (congrArg Fin.val e), fun e ↦ h.2 (congrArg Fin.val e)⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaBuild_exists_third

variable (α : vdkParPres_Tilde n R →* G) (β : vdkOmega_TildeMinus n R →* G)

/-- The mixed relation at the index pair `(i, k)`, for all coefficients. -/
def vdkOmegaBuild_Full (i k : Fin n) : Prop :=
  ∀ (h : i ≠ k) (a b : R),
    ⁅vdkOmega_cv α (Pi.single i a), vdkOmega_rv β (Pi.single k b)⁆ =
      α (vdkParPres_inr (x i k h (a * b)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaBuild_Full

/-- The single identity at one index pair, with both coefficients `1`. -/
def vdkOmegaBuild_MixedOne (i₀ j₀ : Fin n) (h : i₀ ≠ j₀) : Prop :=
  ⁅vdkOmega_cv α (Pi.single i₀ 1), vdkOmega_rv β (Pi.single j₀ 1)⁆ =
    α (vdkParPres_inr (x i₀ j₀ h 1))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaBuild_MixedOne

theorem vdkOmegaBuild_moveSndFull (hαβ : vdkOmega_Agree α β) {i j k : Fin n} (hij : i ≠ j)
    (hF : vdkOmegaBuild_Full α β i j) (hkj : k ≠ j) : vdkOmegaBuild_Full α β i k := by
  intro hik a b
  exact vdkOmegaBuild_moveSnd α β hαβ i j k hij (Ne.symm hkj) hik a b
    ((hF hij a 1).trans (by rw [mul_one]))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaBuild_moveSndFull

theorem vdkOmegaBuild_moveFstFull (hαβ : vdkOmega_Agree α β) {i j k : Fin n} (hjk : j ≠ k)
    (hF : vdkOmegaBuild_Full α β j k) (hij : i ≠ j) : vdkOmegaBuild_Full α β i k := by
  intro hik a b
  exact vdkOmegaBuild_moveFst α β hαβ i j k hij hjk hik a b
    ((hF hjk 1 b).trans (by rw [one_mul]))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaBuild_moveFstFull

/-- The relation at one index pair spreads to every index pair. -/
theorem vdkOmegaBuild_full_all (hαβ : vdkOmega_Agree α β) (h3 : 3 ≤ n) {p q : Fin n}
    (hpq : p ≠ q) (hF : vdkOmegaBuild_Full α β p q) (s t : Fin n) :
    vdkOmegaBuild_Full α β s t := by
  have row : ∀ t' : Fin n, vdkOmegaBuild_Full α β p t' := by
    intro t'
    by_cases htq : t' = q
    · rw [htq]
      exact hF
    · exact vdkOmegaBuild_moveSndFull α β hαβ hpq hF htq
  by_cases hsp : s = p
  · rw [hsp]
    exact row t
  by_cases htp : t = p
  · obtain ⟨r, hrs, hrp⟩ := vdkOmegaBuild_exists_third h3 s p
    have hsr : vdkOmegaBuild_Full α β s r :=
      vdkOmegaBuild_moveFstFull α β hαβ (Ne.symm hrp) (row r) hsp
    rw [htp]
    exact vdkOmegaBuild_moveSndFull α β hαβ (Ne.symm hrs) hsr (Ne.symm hrp)
  · exact vdkOmegaBuild_moveFstFull α β hαβ (Ne.symm htp) (row t) hsp

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaBuild_full_all

/-- **The reduction.**  For `n ≥ 3` and `α`, `β` agreeing on `St_n(R)`, the single identity
`⁅x_{i₀,last}(1), x_{last,j₀}(1)⁆ = x_{i₀ j₀}(1)` implies the whole mixed relation. -/
theorem vdkOmegaBuild_mixed_of_mixedOne (hαβ : vdkOmega_Agree α β) (h3 : 3 ≤ n)
    {i₀ j₀ : Fin n} (h0 : i₀ ≠ j₀) (hone : vdkOmegaBuild_MixedOne α β i₀ j₀ h0) :
    vdkOmega_Mixed α β := by
  obtain ⟨r, hri, hrj⟩ := vdkOmegaBuild_exists_third h3 i₀ j₀
  have hrow : ∀ b : R,
      ⁅vdkOmega_cv α (Pi.single i₀ 1), vdkOmega_rv β (Pi.single r b)⁆ =
        α (vdkParPres_inr (x i₀ r (Ne.symm hri) b)) := fun b ↦
    (vdkOmegaBuild_moveSnd α β hαβ i₀ j₀ r h0 (Ne.symm hrj) (Ne.symm hri) 1 b hone).trans
      (by rw [one_mul])
  have hF : vdkOmegaBuild_Full α β j₀ r := by
    intro hjr a b
    exact vdkOmegaBuild_moveFst α β hαβ j₀ i₀ r (Ne.symm h0) (Ne.symm hri) hjr a b (hrow b)
  intro i k
  exact vdkOmegaBuild_full_all α β hαβ h3 (Ne.symm hrj) hF i k

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaBuild_mixed_of_mixedOne

end GroupApproximation.BooneHigman.Metabelian.ElemFP
