import GroupApproximation.Analysis.GroupVonNeumannTrace
import GroupApproximation.Meta.AxiomGuard

/-!
# Twisted group von Neumann algebras over a sign cocycle

Infrastructure of lane `oa-hyperfinite` for tex l.168–173 of `simple_kazhdan_sofic_group.tex`
(at e80dcf20a): "So `L(G)` embeds in `𝓡^ω` … `L(G) ⊗̄ 𝓡` is a McDuff factor that embeds in `𝓡^ω`".
The hyperfinite II₁ factor `𝓡` is modelled in `Analysis/PauliHyperfiniteFactor.lean` as the
twisted group von Neumann algebra of the Pauli group.  This module builds twisted group von
Neumann algebras in general.

For a group `Γ` and a normalized `ZMod 2`-valued 2-cocycle `σ` (`IsSignCocycle σ`), write
`s(z) = (-1)^z` (`zsign`).

* `twistedLeftOperator σ g`, `(λ_g f)(h) = s(σ(g, g⁻¹h)) f(g⁻¹h)`, and `twistedRightOperator σ g`,
  `(ρ_g f)(h) = s(σ(hg⁻¹, g)) f(hg⁻¹)`: unitaries of `ℓ²(Γ)`.
* `twistedLeftOperator_mul`: `λ_g λ_k = s(σ(g,k)) λ_{gk}`.
* `twistedLeftOperator_comm_twistedRightOperator`: the two families commute, by the cocycle
  identity.
* `twistedVonNeumannAlgebra σ`: the double centralizer of the left operators and their adjoints.
* The canonical trace `T ↦ (Tδ₁)(1)`: tracial (`coefficient_mul_comm`) and faithful, with `δ₁`
  separating (`eq_zero_of_mem_of_apply_deltaOne_eq_zero`); finiteness
  (`mul_star_eq_one_of_star_mul_eq_one`).

With `σ = 0` these are the untwisted objects of `Analysis/GroupVonNeumannTrace.lean`, whose proofs
this module follows.
-/

namespace GroupApproximation
namespace TwistedGroupVonNeumann

open ReducedGroupCStarTrace
open scoped ENNReal InnerProductSpace

noncomputable section

universe u

/-! ## Signs -/

/-- The sign `(-1)^z` of `z : ZMod 2`, as a complex number. -/
def zsign (z : ZMod 2) : ℂ := if z = 0 then 1 else -1

@[simp]
theorem zsign_zero : zsign 0 = 1 := if_pos rfl

@[simp]
theorem zsign_one : zsign 1 = -1 := if_neg (by decide)

theorem zmod_two_cases : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide

theorem zsign_add (a b : ZMod 2) : zsign (a + b) = zsign a * zsign b := by
  rcases zmod_two_cases a with rfl | rfl <;> rcases zmod_two_cases b with rfl | rfl
  · simp
  · simp
  · simp
  · rw [show (1 : ZMod 2) + 1 = 0 by decide]
    simp

theorem zsign_mul_zsign_mul (a b : ZMod 2) (x : ℂ) :
    zsign a * (zsign b * x) = zsign (a + b) * x := by
  rw [zsign_add, mul_assoc]

theorem zsign_mul_self (a : ZMod 2) : zsign a * zsign a = 1 := by
  rcases zmod_two_cases a with rfl | rfl <;> simp

theorem star_zsign (a : ZMod 2) : starRingEnd ℂ (zsign a) = zsign a := by
  rcases zmod_two_cases a with rfl | rfl <;> simp

theorem norm_zsign (a : ZMod 2) : ‖zsign a‖ = 1 := by
  rcases zmod_two_cases a with rfl | rfl <;> simp

/-! ## Sign multipliers of `ℓ²` -/

section SignMul

variable {α : Type u}

/-- Multiplying by a `±1`-valued function keeps square-summability. -/
theorem memℓp_zsign_mul (s : α → ZMod 2) (f : lp (fun _ : α ↦ ℂ) 2) :
    Memℓp (fun a : α ↦ zsign (s a) * f a) 2 := by
  apply memℓp_gen
  have h := (memℓp_gen_iff (by norm_num)).1 (lp.memℓp f)
  simpa only [norm_mul, norm_zsign, one_mul] using h

/-- Multiplication by a `±1`-valued function, as a linear equivalence of `ℓ²`. -/
def zsignMulLinear (s : α → ZMod 2) :
    lp (fun _ : α ↦ ℂ) 2 ≃ₗ[ℂ] lp (fun _ : α ↦ ℂ) 2 where
  toFun f := ⟨fun a ↦ zsign (s a) * f a, memℓp_zsign_mul s f⟩
  invFun f := ⟨fun a ↦ zsign (s a) * f a, memℓp_zsign_mul s f⟩
  map_add' f g := by
    apply lp.ext
    funext a
    change zsign (s a) * (⇑(f + g)) a = zsign (s a) * f a + zsign (s a) * g a
    rw [lp.coeFn_add, Pi.add_apply, mul_add]
  map_smul' c f := by
    apply lp.ext
    funext a
    change zsign (s a) * (⇑(c • f)) a = c • (zsign (s a) * f a)
    rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm]
  left_inv f := by
    apply lp.ext
    funext a
    change zsign (s a) * (zsign (s a) * f a) = f a
    rw [← mul_assoc, zsign_mul_self, one_mul]
  right_inv f := by
    apply lp.ext
    funext a
    change zsign (s a) * (zsign (s a) * f a) = f a
    rw [← mul_assoc, zsign_mul_self, one_mul]

/-- Multiplication by a `±1`-valued function, as a unitary of `ℓ²`. -/
def zsignMul (s : α → ZMod 2) : lp (fun _ : α ↦ ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : α ↦ ℂ) 2 :=
  (zsignMulLinear s).isometryOfInner (by
    intro f g
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
    refine tsum_congr fun a ↦ ?_
    change ⟪zsign (s a) * f a, zsign (s a) * g a⟫_ℂ = ⟪f a, g a⟫_ℂ
    rw [← smul_eq_mul (zsign (s a)) (f a), ← smul_eq_mul (zsign (s a)) (g a),
      inner_smul_left, inner_smul_right, star_zsign, ← mul_assoc, zsign_mul_self, one_mul])

@[simp]
theorem zsignMul_apply (s : α → ZMod 2) (f : lp (fun _ : α ↦ ℂ) 2) (a : α) :
    zsignMul s f a = zsign (s a) * f a :=
  rfl

end SignMul

/-- Two elements of a monoid that are mutually inverse commute with everything the first commutes
with. -/
theorem commute_of_inverse {M : Type*} [Monoid M] {A A' B : M}
    (h1 : A * A' = 1) (h2 : A' * A = 1) (hc : A * B = B * A) : A' * B = B * A' := by
  calc A' * B = A' * B * (A * A') := by rw [h1, mul_one]
    _ = A' * (B * A) * A' := by simp only [mul_assoc]
    _ = A' * (A * B) * A' := by rw [hc]
    _ = A' * A * B * A' := by simp only [mul_assoc]
    _ = B * A' := by rw [h2, one_mul]

/-! ## Sign cocycles and the twisted regular operators -/

variable {Γ : Type u} [Group Γ]

local instance : DecidableEq Γ := Classical.decEq Γ

/-- A normalized `ZMod 2`-valued 2-cocycle on `Γ`. -/
structure IsSignCocycle (σ : Γ → Γ → ZMod 2) : Prop where
  map_one_left : ∀ g : Γ, σ 1 g = 0
  map_one_right : ∀ g : Γ, σ g 1 = 0
  cocycle : ∀ g h k : Γ, σ g h + σ (g * h) k = σ h k + σ g (h * k)

theorem IsSignCocycle.inv_comm {σ : Γ → Γ → ZMod 2} (hσ : IsSignCocycle σ) (g : Γ) :
    σ g g⁻¹ = σ g⁻¹ g := by
  have h := hσ.cocycle g g⁻¹ g
  rw [mul_inv_cancel, inv_mul_cancel, hσ.map_one_left, hσ.map_one_right, add_zero,
    add_zero] at h
  exact h

variable (σ : Γ → Γ → ZMod 2)

/-- The twisted left unitary `(λ_g f)(h) = s(σ(g, g⁻¹h)) f(g⁻¹h)`. -/
def twistedLeft (g : Γ) : GroupHilbert Γ ≃ₗᵢ[ℂ] GroupHilbert Γ :=
  (leftRegular Γ g).trans (zsignMul fun h ↦ σ g (g⁻¹ * h))

/-- The twisted left unitary as a bounded operator. -/
def twistedLeftOperator (g : Γ) : GroupHilbert Γ →L[ℂ] GroupHilbert Γ :=
  (twistedLeft σ g).toLinearIsometry.toContinuousLinearMap

@[simp]
theorem twistedLeftOperator_apply (g : Γ) (f : GroupHilbert Γ) (h : Γ) :
    twistedLeftOperator σ g f h = zsign (σ g (g⁻¹ * h)) * f (g⁻¹ * h) :=
  rfl

/-- The twisted right unitary `(ρ_g f)(h) = s(σ(hg⁻¹, g)) f(hg⁻¹)`. -/
def twistedRight (g : Γ) : GroupHilbert Γ ≃ₗᵢ[ℂ] GroupHilbert Γ :=
  (rightRegular Γ g).trans (zsignMul fun h ↦ σ (h * g⁻¹) g)

/-- The twisted right unitary as a bounded operator. -/
def twistedRightOperator (g : Γ) : GroupHilbert Γ →L[ℂ] GroupHilbert Γ :=
  (twistedRight σ g).toLinearIsometry.toContinuousLinearMap

@[simp]
theorem twistedRightOperator_apply (g : Γ) (f : GroupHilbert Γ) (h : Γ) :
    twistedRightOperator σ g f h = zsign (σ (h * g⁻¹) g) * f (h * g⁻¹) :=
  rfl

/-- **The twisted multiplication law** `λ_g λ_k = s(σ(g,k)) λ_{gk}`. -/
theorem twistedLeftOperator_mul (hσ : IsSignCocycle σ) (g k : Γ) :
    twistedLeftOperator σ g * twistedLeftOperator σ k =
      zsign (σ g k) • twistedLeftOperator σ (g * k) := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext h
  change zsign (σ g (g⁻¹ * h)) * (zsign (σ k (k⁻¹ * (g⁻¹ * h))) * f (k⁻¹ * (g⁻¹ * h))) =
    zsign (σ g k) * (zsign (σ (g * k) ((g * k)⁻¹ * h)) * f ((g * k)⁻¹ * h))
  have hinv : (g * k)⁻¹ * h = k⁻¹ * (g⁻¹ * h) := by rw [mul_inv_rev, mul_assoc]
  have hco := hσ.cocycle g k (k⁻¹ * (g⁻¹ * h))
  rw [mul_inv_cancel_left] at hco
  rw [hinv, zsign_mul_zsign_mul, zsign_mul_zsign_mul, hco, add_comm]

/-- **The twisted left and right operators commute**, by the cocycle identity. -/
theorem twistedLeftOperator_comm_twistedRightOperator (hσ : IsSignCocycle σ) (k g : Γ) :
    twistedLeftOperator σ k * twistedRightOperator σ g =
      twistedRightOperator σ g * twistedLeftOperator σ k := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext h
  change zsign (σ k (k⁻¹ * h)) * (zsign (σ (k⁻¹ * h * g⁻¹) g) * f (k⁻¹ * h * g⁻¹)) =
    zsign (σ (h * g⁻¹) g) * (zsign (σ k (k⁻¹ * (h * g⁻¹))) * f (k⁻¹ * (h * g⁻¹)))
  have hx : k⁻¹ * (h * g⁻¹) = k⁻¹ * h * g⁻¹ := (mul_assoc _ _ _).symm
  have hco := hσ.cocycle k (k⁻¹ * h * g⁻¹) g
  have h1 : k * (k⁻¹ * h * g⁻¹) = h * g⁻¹ := by rw [mul_assoc, mul_inv_cancel_left]
  have h2 : k⁻¹ * h * g⁻¹ * g = k⁻¹ * h := inv_mul_cancel_right _ _
  rw [h1, h2] at hco
  rw [hx, zsign_mul_zsign_mul, zsign_mul_zsign_mul, add_comm (σ (h * g⁻¹) g), hco, add_comm]

/-- The adjoint of a twisted left unitary is its inverse. -/
theorem star_twistedLeftOperator (g : Γ) :
    star (twistedLeftOperator σ g) =
      ((twistedLeft σ g).symm : GroupHilbert Γ →L[ℂ] GroupHilbert Γ) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  exact LinearIsometryEquiv.adjoint_eq_symm (twistedLeft σ g)

theorem twistedLeftOperator_mul_star (g : Γ) :
    twistedLeftOperator σ g * star (twistedLeftOperator σ g) = 1 := by
  rw [star_twistedLeftOperator]
  apply ContinuousLinearMap.ext
  intro f
  exact (twistedLeft σ g).apply_symm_apply f

theorem star_mul_twistedLeftOperator (g : Γ) :
    star (twistedLeftOperator σ g) * twistedLeftOperator σ g = 1 := by
  rw [star_twistedLeftOperator]
  apply ContinuousLinearMap.ext
  intro f
  exact (twistedLeft σ g).symm_apply_apply f

/-! ## The twisted group von Neumann algebra -/

/-- The twisted left operators together with their adjoints. -/
def twistedGenerators : Set (GroupHilbert Γ →L[ℂ] GroupHilbert Γ) :=
  Set.range (twistedLeftOperator σ) ∪ Set.range fun g ↦ star (twistedLeftOperator σ g)

theorem star_mem_twistedGenerators {a : GroupHilbert Γ →L[ℂ] GroupHilbert Γ}
    (ha : a ∈ twistedGenerators σ) : star a ∈ twistedGenerators σ := by
  rcases ha with ⟨g, rfl⟩ | ⟨g, rfl⟩
  · exact Set.mem_union_right _ ⟨g, rfl⟩
  · exact Set.mem_union_left _ ⟨g, (star_star _).symm⟩

/-- **The twisted group von Neumann algebra** `L_σ(Γ)`: the double centralizer of the twisted left
operators and their adjoints, as a concrete `VonNeumannAlgebra` on `ℓ²(Γ)`. -/
def twistedVonNeumannAlgebra : VonNeumannAlgebra (GroupHilbert Γ) where
  toStarSubalgebra :=
    { Subalgebra.centralizer ℂ (Set.centralizer (twistedGenerators σ)) with
      star_mem' := fun {_} ha ↦
        Set.star_mem_centralizer'
          (fun _ hb ↦ Set.star_mem_centralizer'
            (fun _ hm ↦ star_mem_twistedGenerators σ hm) hb) ha }
  centralizer_centralizer' :=
    Set.centralizer_centralizer_centralizer (Set.centralizer (twistedGenerators σ))

theorem mem_twistedVonNeumannAlgebra_iff {T : GroupHilbert Γ →L[ℂ] GroupHilbert Γ} :
    T ∈ twistedVonNeumannAlgebra σ ↔
      T ∈ Set.centralizer (Set.centralizer (twistedGenerators σ)) :=
  Iff.rfl

/-- `λ_σ(Γ) ⊆ L_σ(Γ)`. -/
theorem twistedLeftOperator_mem (g : Γ) :
    twistedLeftOperator σ g ∈ twistedVonNeumannAlgebra σ :=
  Set.subset_centralizer_centralizer (Set.mem_union_left _ ⟨g, rfl⟩)

/-- Every twisted right operator lies in the commutant of the generators. -/
theorem twistedRightOperator_mem_centralizer (hσ : IsSignCocycle σ) (g : Γ) :
    twistedRightOperator σ g ∈ Set.centralizer (twistedGenerators σ) := by
  rintro m (⟨k, rfl⟩ | ⟨k, rfl⟩)
  · exact twistedLeftOperator_comm_twistedRightOperator σ hσ k g
  · exact commute_of_inverse (twistedLeftOperator_mul_star σ k)
      (star_mul_twistedLeftOperator σ k) (twistedLeftOperator_comm_twistedRightOperator σ hσ k g)

/-- Every element of `L_σ(Γ)` commutes with every twisted right operator. -/
theorem commutes_twistedRightOperator (hσ : IsSignCocycle σ)
    {T : GroupHilbert Γ →L[ℂ] GroupHilbert Γ} (hT : T ∈ twistedVonNeumannAlgebra σ) (g : Γ) :
    twistedRightOperator σ g * T = T * twistedRightOperator σ g :=
  hT _ (twistedRightOperator_mem_centralizer σ hσ g)

/-! ## The canonical trace -/

/-- A twisted right translate of the identity point mass is a point mass. -/
theorem twistedRightOperator_deltaOne (hσ : IsSignCocycle σ) (g : Γ) :
    twistedRightOperator σ g (deltaOne Γ) = lp.single 2 g 1 := by
  apply lp.ext
  funext x
  simp only [twistedRightOperator_apply, deltaOne, lp.coeFn_single]
  by_cases hx : x = g
  · subst hx
    simp [hσ.map_one_left]
  · have hne : x * g⁻¹ ≠ 1 := fun h ↦ hx (mul_inv_eq_one.mp h)
    rw [Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hx, mul_zero]

/-- An element of `L_σ(Γ)` acts on a point mass by a twisted right translation of its
coefficient vector. -/
theorem apply_single_of_mem (hσ : IsSignCocycle σ) {T : GroupHilbert Γ →L[ℂ] GroupHilbert Γ}
    (hT : T ∈ twistedVonNeumannAlgebra σ) (g : Γ) (c : ℂ) :
    T (lp.single 2 g c) = c • twistedRightOperator σ g (T (deltaOne Γ)) := by
  have hsingle : (lp.single 2 g c : GroupHilbert Γ) =
      c • (lp.single 2 g (1 : ℂ) : GroupHilbert Γ) := by
    rw [← lp.single_smul]
    simp
  rw [hsingle, map_smul, ← twistedRightOperator_deltaOne σ hσ]
  congr 1
  exact (DFunLike.congr_fun (commutes_twistedRightOperator σ hσ hT g) (deltaOne Γ)).symm

/-- **The twisted convolution formula** for the identity coefficient of `T ∘ S`. -/
theorem hasSum_product_coefficient_of_mem (hσ : IsSignCocycle σ)
    {T : GroupHilbert Γ →L[ℂ] GroupHilbert Γ} (hT : T ∈ twistedVonNeumannAlgebra σ)
    (S : GroupHilbert Γ →L[ℂ] GroupHilbert Γ) :
    HasSum (fun g : Γ ↦ (S (deltaOne Γ)) g * (zsign (σ g⁻¹ g) * (T (deltaOne Γ)) g⁻¹))
      (((T * S) (deltaOne Γ)) 1) := by
  let evalAfterT : GroupHilbert Γ →L[ℂ] ℂ :=
    (lp.evalCLM ℂ (fun _ : Γ ↦ ℂ) 2 (1 : Γ)).comp T
  have hs := (lp.hasSum_single ENNReal.ofNat_ne_top (S (deltaOne Γ))).mapL evalAfterT
  convert hs using 1
  · ext g
    dsimp only [evalAfterT, ContinuousLinearMap.comp_apply]
    change (S (deltaOne Γ)) g * (zsign (σ g⁻¹ g) * (T (deltaOne Γ)) g⁻¹)
      = (T (lp.single 2 g ((S (deltaOne Γ)) g))) 1
    rw [apply_single_of_mem σ hσ hT]
    change (S (deltaOne Γ)) g * (zsign (σ g⁻¹ g) * (T (deltaOne Γ)) g⁻¹)
      = (S (deltaOne Γ)) g * (twistedRightOperator σ g (T (deltaOne Γ))) 1
    rw [twistedRightOperator_apply]
    simp only [one_mul]
  · rfl

/-- **Traciality** of the identity coefficient on `L_σ(Γ)`. -/
theorem coefficient_mul_comm (hσ : IsSignCocycle σ)
    {T S : GroupHilbert Γ →L[ℂ] GroupHilbert Γ}
    (hT : T ∈ twistedVonNeumannAlgebra σ) (hS : S ∈ twistedVonNeumannAlgebra σ) :
    ((T * S) (deltaOne Γ)) 1 = ((S * T) (deltaOne Γ)) 1 := by
  have hTS := hasSum_product_coefficient_of_mem σ hσ hT S
  have hST := hasSum_product_coefficient_of_mem σ hσ hS T
  have hSTinv := (Equiv.inv Γ).hasSum_iff.mpr hST
  apply hTS.unique
  convert hSTinv using 1
  ext g
  simp only [Function.comp_apply, Equiv.inv_apply, inv_inv]
  rw [hσ.inv_comm g]
  ring

/-- **`δ₁` separates `L_σ(Γ)`.** -/
theorem eq_zero_of_mem_of_apply_deltaOne_eq_zero (hσ : IsSignCocycle σ)
    {T : GroupHilbert Γ →L[ℂ] GroupHilbert Γ}
    (hT : T ∈ twistedVonNeumannAlgebra σ) (h : T (deltaOne Γ) = 0) : T = 0 := by
  apply ContinuousLinearMap.ext
  intro f
  have hs := (lp.hasSum_single ENNReal.ofNat_ne_top f).mapL T
  have hzero : ∀ g : Γ, T (lp.single 2 g (f g)) = 0 := by
    intro g
    rw [apply_single_of_mem σ hσ hT, h, map_zero, smul_zero]
  have hz : HasSum (fun g : Γ ↦ T (lp.single 2 g (f g))) 0 := by
    simpa only [hzero] using
      (hasSum_zero : HasSum (fun _ : Γ ↦ (0 : GroupHilbert Γ)) 0)
  exact hs.unique hz

/-- **Faithfulness of the trace on `L_σ(Γ)`.** -/
theorem eq_zero_of_mem_of_coefficient_star_mul_self_eq_zero (hσ : IsSignCocycle σ)
    {T : GroupHilbert Γ →L[ℂ] GroupHilbert Γ}
    (hT : T ∈ twistedVonNeumannAlgebra σ)
    (h : ((star T * T) (deltaOne Γ)) 1 = 0) : T = 0 := by
  rw [GroupVonNeumann.coefficient_star_mul_self] at h
  have hnorm : ‖T (deltaOne Γ)‖ = 0 := by
    have hc : (‖T (deltaOne Γ)‖ : ℂ) = 0 := sq_eq_zero_iff.mp h
    exact Complex.ofReal_eq_zero.mp hc
  exact eq_zero_of_mem_of_apply_deltaOne_eq_zero σ hσ hT (norm_eq_zero.mp hnorm)

/-- **`L_σ(Γ)` is finite**: an isometry is a unitary, because `1 − vv⋆` is a projection of trace
zero. -/
theorem mul_star_eq_one_of_star_mul_eq_one (hσ : IsSignCocycle σ)
    {v : GroupHilbert Γ →L[ℂ] GroupHilbert Γ}
    (hv : v ∈ twistedVonNeumannAlgebra σ)
    (h : star v * v = 1) : v * star v = 1 := by
  have hvstar : star v ∈ twistedVonNeumannAlgebra σ := star_mem hv
  have hmem : v * star v ∈ twistedVonNeumannAlgebra σ := mul_mem hv hvstar
  have hPmem : 1 - v * star v ∈ twistedVonNeumannAlgebra σ :=
    sub_mem (one_mem _) hmem
  have htrace : ((v * star v) (deltaOne Γ)) 1 = 1 := by
    have hcomm := coefficient_mul_comm σ hσ hv hvstar
    rw [hcomm, h]
    exact GroupVonNeumann.coefficient_one Γ
  have hsa : star (1 - v * star v) = 1 - v * star v := by
    rw [star_sub, star_one, star_mul, star_star]
  have hidem : (v * star v) * (v * star v) = v * star v := by
    calc (v * star v) * (v * star v)
        = v * (star v * v) * star v := by
          rw [mul_assoc, mul_assoc, ← mul_assoc (star v) v (star v),
            ← mul_assoc v (star v * v) (star v)]
      _ = v * star v := by rw [h, mul_one]
  have hPP : (1 - v * star v) * (1 - v * star v) = 1 - v * star v := by
    have hexp : (1 - v * star v) * (1 - v * star v)
        = 1 - v * star v - v * star v + (v * star v) * (v * star v) := by
      noncomm_ring
    rw [hexp, hidem]
    abel
  have hPcoef : ((1 - v * star v) (deltaOne Γ)) 1 = 0 := by
    have hsub : ((1 - v * star v) (deltaOne Γ)) 1
        = ((1 : GroupHilbert Γ →L[ℂ] GroupHilbert Γ) (deltaOne Γ)) 1
          - ((v * star v) (deltaOne Γ)) 1 := by
      rw [sub_apply, lp.coeFn_sub, Pi.sub_apply]
    rw [hsub, GroupVonNeumann.coefficient_one, htrace, sub_self]
  have hstarPP : ((star (1 - v * star v) * (1 - v * star v))
      (deltaOne Γ)) 1 = 0 := by
    rw [hsa, hPP]
    exact hPcoef
  have hPzero : (1 : GroupHilbert Γ →L[ℂ] GroupHilbert Γ) - v * star v = 0 :=
    eq_zero_of_mem_of_coefficient_star_mul_self_eq_zero σ hσ hPmem hstarPP
  exact (sub_eq_zero.mp hPzero).symm

end

#audit_axioms twistedLeftOperator_mul
#audit_axioms twistedLeftOperator_comm_twistedRightOperator
#audit_axioms coefficient_mul_comm
#audit_axioms eq_zero_of_mem_of_coefficient_star_mul_self_eq_zero
#audit_axioms mul_star_eq_one_of_star_mul_eq_one

end TwistedGroupVonNeumann
end GroupApproximation
