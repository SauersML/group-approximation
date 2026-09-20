import GroupApproximation.BooneHigmanLinear.CharZero.K2Found.RelPres
import GroupApproximation.Meta.AxiomGuard

/-!
# The action of `E(A)` on `St(A, 𝔄)`, and the root elements (k2-poly, piece F.2)

* `actAut : E(A) →* MulAut (St(A, 𝔄))`, `X_{v,w} ↦ X_{g v, w g⁻¹}` (Tulenbaev, after Def 1.5).
* `smulPair_elementaryUnit`: the transvection `eᵢⱼ(t)` acts on pairs as vdK's conjugation by the
  ordinary pair `(eᵢ, t eⱼᵀ)`.
* `commute_of_conjPair`, `X_std_adjacent`: the root elements `X_{eᵢ, a eⱼᵀ}`, `a ∈ 𝔄`, satisfy
  the Steinberg relations inside `St(A, 𝔄)`.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace K2Found
namespace RelPres

open Matrix
open GroupApproximation.BooneHigmanLinear.K2Found.VdK (conjPair stdPair)
open scoped commutatorElement

variable {I A : Type*} [Fintype I] [DecidableEq I] [CommRing A] {𝔄 : Ideal A}

section Act

/-- `g ∈ E(A)` on the generators. -/
def actGen (g : elementaryGroup I A) (p : RGen I A 𝔄) : RelSt I A 𝔄 :=
  X (smulPair (g : (Matrix I I A)ˣ) p.1) (smulPair_mem g.2 p.2)

theorem actGen_kills (g : elementaryGroup I A) (r : FreeGroup (RGen I A 𝔄))
    (hr : r ∈ rels I A 𝔄) : FreeGroup.lift (actGen g) r = 1 := by
  obtain ⟨G, hG⟩ := g
  change IsRel 𝔄 r at hr
  cases hr with
  | add v w w' h₁ h₂ h₃ =>
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      rw [mul_inv_eq_one]
      have h₁' : RMem 𝔄 ((G : Matrix I I A) *ᵥ v,
          w ᵥ* ((G⁻¹ : (Matrix I I A)ˣ) : Matrix I I A)) := smulPair_mem hG h₁
      have h₂' : RMem 𝔄 ((G : Matrix I I A) *ᵥ v,
          w' ᵥ* ((G⁻¹ : (Matrix I I A)ˣ) : Matrix I I A)) := smulPair_mem hG h₂
      have hs := h₁'.add h₂'
      refine (X_add _ _ _ h₁' h₂' hs).trans (X_congr ?_ _ _)
      exact Prod.ext rfl (add_vecMul _ _ _).symm
  | conj p q hp hq hc =>
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      rw [mul_inv_eq_one]
      have hc' : RMem 𝔄 (conjPair (smulPair G p) (smulPair G q)) := by
        rw [← smulPair_conjPair]
        exact smulPair_mem hG hc
      exact (X_conj _ _ (smulPair_mem hG hp) (smulPair_mem hG hq) hc').trans
        (X_congr (smulPair_conjPair G p q).symm _ _)
  | frame v v' w u b hu hu' hw h₁ h₂ h₃ =>
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      rw [mul_inv_eq_one]
      have e₁ : smulPair G (b • v + v', w) = (b • ((G : Matrix I I A) *ᵥ v) +
          (G : Matrix I I A) *ᵥ v', w ᵥ* ((G⁻¹ : (Matrix I I A)ˣ) : Matrix I I A)) :=
        Prod.ext (by
          change (G : Matrix I I A) *ᵥ (b • v + v') = _
          rw [mulVec_add, mulVec_smul]) rfl
      have e₂ : smulPair G (v, b • w) = ((G : Matrix I I A) *ᵥ v,
          b • (w ᵥ* ((G⁻¹ : (Matrix I I A)ˣ) : Matrix I I A))) :=
        Prod.ext rfl (smul_vecMul _ _ _)
      have h₁' : RMem 𝔄 (b • ((G : Matrix I I A) *ᵥ v) + (G : Matrix I I A) *ᵥ v',
          w ᵥ* ((G⁻¹ : (Matrix I I A)ˣ) : Matrix I I A)) := e₁ ▸ smulPair_mem hG h₁
      have h₂' : RMem 𝔄 ((G : Matrix I I A) *ᵥ v,
          b • (w ᵥ* ((G⁻¹ : (Matrix I I A)ˣ) : Matrix I I A))) := e₂ ▸ smulPair_mem hG h₂
      have hf := X_frame ((G : Matrix I I A) *ᵥ v) ((G : Matrix I I A) *ᵥ v')
        (w ᵥ* ((G⁻¹ : (Matrix I I A)ˣ) : Matrix I I A))
        (u ᵥ* ((G⁻¹ : (Matrix I I A)ˣ) : Matrix I I A)) b
        (by rw [smulPair_dot]; exact hu) (by rw [smulPair_dot]; exact hu')
        (by rw [smulPair_dot]; exact hw) h₁' h₂' (smulPair_mem hG h₃)
      exact (X_congr e₁ _ h₁').trans (hf.trans (congrArg (· * _) (X_congr e₂.symm _ _)))

#audit_axioms actGen_kills

/-- `g ∈ E(A)` acting on `St(A, 𝔄)`. -/
noncomputable def actEnd (g : elementaryGroup I A) : RelSt I A 𝔄 →* RelSt I A 𝔄 :=
  PresentedGroup.toGroup (actGen_kills g)

theorem actEnd_X (g : elementaryGroup I A) (p : (I → A) × (I → A)) (hp : RMem 𝔄 p) :
    actEnd g (X p hp) = X (smulPair (g : (Matrix I I A)ˣ) p) (smulPair_mem g.2 hp) :=
  PresentedGroup.toGroup.of _

#audit_axioms actEnd_X

theorem actEnd_one : actEnd (1 : elementaryGroup I A) = MonoidHom.id (RelSt I A 𝔄) := by
  apply PresentedGroup.ext
  rintro ⟨p, hp⟩
  change actEnd 1 (X p hp) = X p hp
  rw [actEnd_X]
  exact X_congr (smulPair_one p) _ _

#audit_axioms actEnd_one

theorem actEnd_mul (g h : elementaryGroup I A) :
    actEnd (g * h) = (actEnd g).comp (actEnd (𝔄 := 𝔄) h) := by
  apply PresentedGroup.ext
  rintro ⟨p, hp⟩
  change actEnd (g * h) (X p hp) = actEnd g (actEnd h (X p hp))
  rw [actEnd_X, actEnd_X, actEnd_X]
  exact X_congr (smulPair_mul _ _ p) _ _

#audit_axioms actEnd_mul

theorem actEnd_inv_apply (g : elementaryGroup I A) (n : RelSt I A 𝔄) :
    actEnd g⁻¹ (actEnd g n) = n := by
  have h := DFunLike.congr_fun (actEnd_mul (𝔄 := 𝔄) g⁻¹ g) n
  rw [inv_mul_cancel, actEnd_one, MonoidHom.id_apply, MonoidHom.comp_apply] at h
  exact h.symm

theorem actEnd_apply_inv (g : elementaryGroup I A) (n : RelSt I A 𝔄) :
    actEnd g (actEnd g⁻¹ n) = n := by
  have h := DFunLike.congr_fun (actEnd_mul (𝔄 := 𝔄) g g⁻¹) n
  rw [mul_inv_cancel, actEnd_one, MonoidHom.id_apply, MonoidHom.comp_apply] at h
  exact h.symm

variable (I A 𝔄) in
/-- **The action of `E(A)` on `St(A, 𝔄)`**, `X_{v,w} ↦ X_{g v, w g⁻¹}`. -/
noncomputable def actAut : elementaryGroup I A →* MulAut (RelSt I A 𝔄) where
  toFun g :=
    { toFun := actEnd g
      invFun := actEnd g⁻¹
      left_inv := actEnd_inv_apply g
      right_inv := actEnd_apply_inv g
      map_mul' := map_mul (actEnd g) }
  map_one' := MulEquiv.ext fun n => by
    change actEnd 1 n = n
    rw [actEnd_one, MonoidHom.id_apply]
  map_mul' g h := MulEquiv.ext fun n => by
    change actEnd (g * h) n = actEnd g (actEnd h n)
    rw [actEnd_mul, MonoidHom.comp_apply]

theorem actAut_X (g : elementaryGroup I A) (p : (I → A) × (I → A)) (hp : RMem 𝔄 p) :
    actAut I A 𝔄 g (X p hp) = X (smulPair (g : (Matrix I I A)ˣ) p) (smulPair_mem g.2 hp) :=
  actEnd_X g p hp

#audit_axioms actAut_X

end Act

section Roots

/-- The transvection `eᵢⱼ(t)` acts on pairs as vdK's conjugation by `(eᵢ, t eⱼᵀ)`. -/
theorem smulPair_elementaryUnit {i j : I} (hij : i ≠ j) (t : A) (q : (I → A) × (I → A)) :
    smulPair (elementaryUnit i j hij t) q = conjPair (stdPair i j t) q := by
  refine Prod.ext ?_ ?_
  · change (1 + Matrix.single i j t) *ᵥ q.1 = q.1 + (Pi.single j t ⬝ᵥ q.1) • Pi.single i 1
    rw [add_mulVec, one_mulVec, single_mulVec_eq, single_dotProduct]
  · change q.2 ᵥ* (1 - Matrix.single i j t) = q.2 - (q.2 ⬝ᵥ Pi.single i 1) • Pi.single j t
    rw [vecMul_sub, vecMul_one, ← mulVec_transpose, transpose_single, single_mulVec_eq,
      dotProduct_single, mul_one]
    congr 1
    ext m
    simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    split_ifs <;> ring

#audit_axioms smulPair_elementaryUnit

theorem rmem_std {i j : I} (hij : i ≠ j) {c : A} (hc : c ∈ 𝔄) : RMem 𝔄 (stdPair i j c) := by
  refine ⟨isEColumn_single i, fun k => ?_, ?_⟩
  · change (Pi.single j c : I → A) k ∈ 𝔄
    by_cases hk : k = j
    · rw [hk, Pi.single_eq_same]
      exact hc
    · rw [Pi.single_eq_of_ne hk]
      exact zero_mem _
  · change Pi.single j c ⬝ᵥ Pi.single i 1 = 0
    rw [single_dotProduct, Pi.single_eq_of_ne hij.symm, mul_zero]

#audit_axioms rmem_std

/-- Two generators commute when the first fixes the pair of the second. -/
theorem commute_of_conjPair {p q : (I → A) × (I → A)} (hp : RMem 𝔄 p) (hq : RMem 𝔄 q)
    (h : conjPair p q = q) : Commute (X p hp) (X q hq) := by
  have hc := X_conj p q hp hq (by rw [h]; exact hq)
  rw [X_congr h _ hq] at hc
  exact (mul_inv_eq_iff_eq_mul.mp hc)

#audit_axioms commute_of_conjPair

theorem conjPair_std_std {i j k l : I} (hjk : j ≠ k) (hli : l ≠ i) (a b : A) :
    conjPair (stdPair i j a) (stdPair k l b) = stdPair k l b := by
  refine Prod.ext ?_ ?_
  · change Pi.single k 1 + (Pi.single j a ⬝ᵥ Pi.single k 1) • Pi.single i 1 = Pi.single k 1
    rw [single_dotProduct, Pi.single_eq_of_ne hjk, mul_zero, zero_smul, add_zero]
  · change Pi.single l b - (Pi.single l b ⬝ᵥ Pi.single i 1) • Pi.single j a = Pi.single l b
    rw [single_dotProduct, Pi.single_eq_of_ne hli, mul_zero, zero_smul, sub_zero]

#audit_axioms conjPair_std_std

/-- The adjacent relation for root elements of `St(A, 𝔄)` (as vdK's `X_std_adjacent`). -/
theorem X_std_adjacent {i j k : I} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) {a b : A}
    (ha : a ∈ 𝔄) (hb : b ∈ 𝔄) :
    ⁅X (stdPair i j a) (rmem_std hij ha), X (stdPair j k b) (rmem_std hjk hb)⁆ =
      X (stdPair i k (a * b)) (rmem_std hik (𝔄.mul_mem_left a hb)) := by
  have hab : a * b ∈ 𝔄 := 𝔄.mul_mem_left a hb
  have htu : RMem 𝔄 (Pi.single i 1, -Pi.single k (a * b)) := (rmem_std hik hab).neg
  have hsum : RMem 𝔄 (Pi.single i 1, Pi.single j a + -Pi.single k (a * b)) :=
    (rmem_std hij ha).add htu
  have hF1 : X (stdPair j k b) (rmem_std hjk hb) * X (stdPair i j a) (rmem_std hij ha) *
      (X (stdPair j k b) (rmem_std hjk hb))⁻¹ =
      X (stdPair i j a) (rmem_std hij ha) * (X (stdPair i k (a * b)) (rmem_std hik hab))⁻¹ := by
    have hpair : conjPair (stdPair j k b) (stdPair i j a) =
        (Pi.single i 1, Pi.single j a + -Pi.single k (a * b)) := by
      refine Prod.ext ?_ ?_
      · change Pi.single i 1 + (Pi.single k b ⬝ᵥ Pi.single i 1) • Pi.single j 1 = Pi.single i 1
        rw [single_dotProduct, Pi.single_eq_of_ne hik.symm, mul_zero, zero_smul, add_zero]
      · change Pi.single j a - (Pi.single j a ⬝ᵥ Pi.single j 1) • Pi.single k b =
          Pi.single j a + -Pi.single k (a * b)
        rw [single_dotProduct, Pi.single_eq_same, mul_one, ← smul_eq_mul, Pi.single_smul',
          sub_eq_add_neg]
    rw [X_conj (stdPair j k b) (stdPair i j a) (rmem_std hjk hb) (rmem_std hij ha)
        (by rw [hpair]; exact hsum),
      X_congr hpair _ hsum,
      ← X_neg (Pi.single i 1) (Pi.single k (a * b)) (rmem_std hik hab) htu,
      X_add (Pi.single i 1) (Pi.single j a) (-Pi.single k (a * b)) (rmem_std hij ha) htu hsum]
  have hF2 : X (stdPair i j a) (rmem_std hij ha) * X (stdPair i k (a * b)) (rmem_std hik hab) *
      (X (stdPair i j a) (rmem_std hij ha))⁻¹ = X (stdPair i k (a * b)) (rmem_std hik hab) := by
    have hpair : conjPair (stdPair i j a) (stdPair i k (a * b)) = stdPair i k (a * b) :=
      conjPair_std_std hij.symm hik.symm a (a * b)
    rw [X_conj (stdPair i j a) (stdPair i k (a * b)) (rmem_std hij ha) (rmem_std hik hab)
      (by rw [hpair]; exact rmem_std hik hab), X_congr hpair _ (rmem_std hik hab)]
  have hinv : X (stdPair j k b) (rmem_std hjk hb) * (X (stdPair i j a) (rmem_std hij ha))⁻¹ *
      (X (stdPair j k b) (rmem_std hjk hb))⁻¹ =
      X (stdPair i k (a * b)) (rmem_std hik hab) * (X (stdPair i j a) (rmem_std hij ha))⁻¹ := by
    calc _ = (X (stdPair j k b) (rmem_std hjk hb) * X (stdPair i j a) (rmem_std hij ha) *
          (X (stdPair j k b) (rmem_std hjk hb))⁻¹)⁻¹ := by group
      _ = _ := by rw [hF1]; group
  calc ⁅X (stdPair i j a) (rmem_std hij ha), X (stdPair j k b) (rmem_std hjk hb)⁆ =
      X (stdPair i j a) (rmem_std hij ha) * (X (stdPair j k b) (rmem_std hjk hb) *
        (X (stdPair i j a) (rmem_std hij ha))⁻¹ * (X (stdPair j k b) (rmem_std hjk hb))⁻¹) := by
        rw [commutatorElement_def]
        group
    _ = X (stdPair i j a) (rmem_std hij ha) * X (stdPair i k (a * b)) (rmem_std hik hab) *
        (X (stdPair i j a) (rmem_std hij ha))⁻¹ := by
        rw [hinv]
        group
    _ = _ := hF2

#audit_axioms X_std_adjacent

end Roots

end RelPres
end K2Found
end BooneHigmanLinear
end GroupApproximation
