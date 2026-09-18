import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.A2ThomT.RelTMass
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.A2ThomT.Ext
import GroupApproximation.Kazhdan.SemidirectProductKazhdan
import GroupApproximation.Leavitt.ElementaryGroup
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Data.Matrix.Basis
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finite.Prod

/-!
# Relative property (T) for `(L³ ⋊ EL_3(L), L³)`, `L = F_p[t,t⁻¹]`

`simple_kazhdan_sofic_group.tex`, Introduction, tex l.57–59 (table row A2): Thom's Kazhdan group
uses relative property (T) of `(F_p[t,t⁻¹]^3 ⋊ SL_3, F_p[t,t⁻¹]^3)` (A. Thom, Groups Geom. Dyn. 4
(2010), §2.1, Lemma 2.1), proved by Burger's argument (Burger 1991; Shalom 1999; Kassabov 2007, §2).

* `relTActionHom R`: the linear action `A • v = A *ᵥ v` of `EL_3(R)` on `R³`, for a commutative
  ring `R`; `relTAction p` and `relTAction_apply` for `R = F_p[t,t⁻¹]`, and the pair
  `RelTPair p = L³ ⋊ EL_3(L)`.
* `planeShearData ι h`: for a ring map `ι : F_p[X] → R` and indices `i ≠ j`, the plane
  `(a, b) ↦ ι a eᵢ + ι b eⱼ` of `R³` with the root shears `x_{ij}(ι r)`, `x_{ji}(ι r)` is a
  `RelTShear`, so Burger's bound `RelTShear.norm_vec_displacement_le` applies to it.
* `exists_laurentEmb_add`: every Laurent polynomial is `f(t) + g(t⁻¹)` with `f, g ∈ F_p[t]`.
* `isRelativeKazhdanPair_relT`: every vector of `L³` is a sum of six vectors `ι a eᵢ`, with
  `ι` one of the two embeddings `t ↦ t`, `t ↦ t⁻¹`; each moves a `(Q, δ)`-invariant unit vector
  by at most `26 (p + 1) δ`, so the whole normal copy moves it by at most `1/2` when
  `312 (p + 1) δ = 1`, and `isRelativeKazhdanPair_of_displacement` concludes.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false

namespace GroupApproximation.Full.A2ThomT

open GroupApproximation

noncomputable section

universe v

section Generic

variable {R : Type*} [CommRing R]

/-- The linear action of an elementary matrix on `R³`, as an automorphism of the multiplicative
copy of `R³`. -/
def relTActionAut (A : elementaryGroup (Fin 3) R) : MulAut (Multiplicative (Fin 3 → R)) where
  toFun n := Multiplicative.ofAdd
    (((A : (Matrix (Fin 3) (Fin 3) R)ˣ) : Matrix (Fin 3) (Fin 3) R) *ᵥ Multiplicative.toAdd n)
  invFun n := Multiplicative.ofAdd
    ((((A : (Matrix (Fin 3) (Fin 3) R)ˣ)⁻¹ : (Matrix (Fin 3) (Fin 3) R)ˣ) :
      Matrix (Fin 3) (Fin 3) R) *ᵥ Multiplicative.toAdd n)
  left_inv n := by
    simp only [toAdd_ofAdd, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, ofAdd_toAdd]
  right_inv n := by
    simp only [toAdd_ofAdd, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, ofAdd_toAdd]
  map_mul' x y := by
    simp only [toAdd_mul, Matrix.mulVec_add, ofAdd_add]

theorem relTActionAut_apply (A : elementaryGroup (Fin 3) R) (n : Multiplicative (Fin 3 → R)) :
    relTActionAut A n = Multiplicative.ofAdd
      (((A : (Matrix (Fin 3) (Fin 3) R)ˣ) : Matrix (Fin 3) (Fin 3) R) *ᵥ Multiplicative.toAdd n) :=
  rfl

variable (R) in
/-- The linear action `A • v = A *ᵥ v` of `EL_3(R)` on `R³`. -/
def relTActionHom : elementaryGroup (Fin 3) R →* MulAut (Multiplicative (Fin 3 → R)) where
  toFun := relTActionAut
  map_one' := MulEquiv.ext fun n ↦ by
    simp only [relTActionAut_apply, MulAut.one_apply, Subgroup.coe_one, OneMemClass.coe_one,
      Units.val_one, Matrix.one_mulVec, ofAdd_toAdd]
  map_mul' A B := MulEquiv.ext fun n ↦ by
    simp only [MulAut.mul_apply, relTActionAut_apply, toAdd_ofAdd, Matrix.mulVec_mulVec,
      Subgroup.coe_mul, MulMemClass.coe_mul, Units.val_mul]

theorem relTActionHom_apply (A : elementaryGroup (Fin 3) R) (n : Multiplicative (Fin 3 → R)) :
    relTActionHom R A n = Multiplicative.ofAdd
      (((A : (Matrix (Fin 3) (Fin 3) R)ˣ) : Matrix (Fin 3) (Fin 3) R) *ᵥ Multiplicative.toAdd n) :=
  rfl

variable (R) in
/-- The semidirect product `R³ ⋊ EL_3(R)` for the linear action. -/
abbrev RelTSemi : Type _ :=
  SemidirectProduct (Multiplicative (Fin 3 → R)) (elementaryGroup (Fin 3) R) (relTActionHom R)

/-- The elementary matrix `x_{ij}(c)` on the plane spanned by `eᵢ, eⱼ`. -/
theorem elementaryUnit_mulVec_single {i j : Fin 3} (h : i ≠ j) (c x y : R) :
    ((elementaryUnit i j h c : (Matrix (Fin 3) (Fin 3) R)ˣ) : Matrix (Fin 3) (Fin 3) R) *ᵥ
        (Pi.single i x + Pi.single j y) = Pi.single i (x + c * y) + Pi.single j y := by
  show (1 + Matrix.single i j c) *ᵥ (Pi.single i x + Pi.single j y) = _
  have hj : (Pi.single i x + Pi.single j y : Fin 3 → R) j = y := by
    simp [Pi.single_apply, h.symm]
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec, hj]
  ext k
  by_cases hki : k = i
  · subst hki
    simp [Pi.single_apply, h]
  · simp [Pi.single_apply, Function.update_apply, hki]

/-- The elementary matrix `x_{ji}(c)` on the plane spanned by `eᵢ, eⱼ`. -/
theorem elementaryUnit_mulVec_single_low {i j : Fin 3} (h : i ≠ j) (c x y : R) :
    ((elementaryUnit j i h.symm c : (Matrix (Fin 3) (Fin 3) R)ˣ) : Matrix (Fin 3) (Fin 3) R) *ᵥ
        (Pi.single i x + Pi.single j y) = Pi.single i x + Pi.single j (y + c * x) := by
  rw [add_comm (Pi.single i x : Fin 3 → R), elementaryUnit_mulVec_single h.symm c y x]
  exact add_comm _ _

/-- The plane vector `x eᵢ + y eⱼ` in the normal copy of `R³`. -/
def planeVec (i j : Fin 3) (x y : R) : RelTSemi R :=
  SemidirectProduct.inl (Multiplicative.ofAdd (Pi.single i x + Pi.single j y))

/-- The root shear `x_{ij}(c)` in the complement `EL_3(R)`. -/
def planeShear (i j : Fin 3) (h : i ≠ j) (c : R) : RelTSemi R :=
  SemidirectProduct.inr ⟨elementaryUnit i j h c, elementaryUnit_mem i j h c⟩

theorem planeVec_add (i j : Fin 3) (x y x' y' : R) :
    planeVec i j (x + x') (y + y') = planeVec i j x y * planeVec i j x' y' := by
  unfold planeVec
  have hv : (Pi.single i (x + x') + Pi.single j (y + y') : Fin 3 → R) =
      (Pi.single i x + Pi.single j y) + (Pi.single i x' + Pi.single j y') := by
    rw [Pi.single_add, Pi.single_add]
    abel
  rw [hv, ofAdd_add, map_mul]

theorem planeVec_zero_right (i j : Fin 3) (x : R) :
    planeVec i j x 0 = SemidirectProduct.inl (Multiplicative.ofAdd (Pi.single i x)) := by
  unfold planeVec
  rw [Pi.single_zero, add_zero]

theorem planeShear_conj {i j : Fin 3} (h : i ≠ j) (c x y : R) :
    planeShear i j h c * planeVec i j x y * (planeShear i j h c)⁻¹ =
      planeVec i j (x + c * y) y := by
  unfold planeShear planeVec
  rw [← map_inv, ← SemidirectProduct.inl_aut, relTActionHom_apply, toAdd_ofAdd]
  exact congrArg
    (fun w : Fin 3 → R ↦ (SemidirectProduct.inl (Multiplicative.ofAdd w) : RelTSemi R))
    (elementaryUnit_mulVec_single h c x y)

theorem planeShear_conj_low {i j : Fin 3} (h : i ≠ j) (c x y : R) :
    planeShear j i h.symm c * planeVec i j x y * (planeShear j i h.symm c)⁻¹ =
      planeVec i j x (y + c * x) := by
  unfold planeShear planeVec
  rw [← map_inv, ← SemidirectProduct.inl_aut, relTActionHom_apply, toAdd_ofAdd]
  exact congrArg
    (fun w : Fin 3 → R ↦ (SemidirectProduct.inl (Multiplicative.ofAdd w) : RelTSemi R))
    (elementaryUnit_mulVec_single_low h c x y)

/-- The shear plane `(a, b) ↦ ι a eᵢ + ι b eⱼ` with the root shears `x_{ij}(ι r)`, `x_{ji}(ι r)`. -/
def planeShearData {p : ℕ} (ι : Polynomial (ZMod p) →+* R) {i j : Fin 3} (h : i ≠ j) :
    RelTShear (RelTSemi R) p where
  vec x := planeVec i j (ι x.1) (ι x.2)
  vec_add x y := by
    show planeVec i j (ι (x.1 + y.1)) (ι (x.2 + y.2)) = _
    rw [map_add, map_add]
    exact planeVec_add i j _ _ _ _
  up r := planeShear i j h (ι r)
  low r := planeShear j i h.symm (ι r)
  up_conj r a b := by
    show planeShear i j h (ι r) * planeVec i j (ι a) (ι b) * (planeShear i j h (ι r))⁻¹ =
      planeVec i j (ι (a + r * b)) (ι b)
    rw [map_add, map_mul]
    exact planeShear_conj h (ι r) (ι a) (ι b)
  low_conj r a b := by
    show planeShear j i h.symm (ι r) * planeVec i j (ι a) (ι b) *
        (planeShear j i h.symm (ι r))⁻¹ = planeVec i j (ι a) (ι (b + r * a))
    rw [map_add, map_mul]
    exact planeShear_conj_low h (ι r) (ι a) (ι b)

/-- The triangle inequality for displacements. -/
theorem relT_norm_map_mul_sub_le {G : Type*} [Group G] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (g h : G) (x : E) :
    ‖ρ (g * h) x - x‖ ≤ ‖ρ g x - x‖ + ‖ρ h x - x‖ := by
  have hmul : ρ (g * h) x = ρ g (ρ h x) :=
    congrArg (fun T : E ≃ₗᵢ[ℝ] E ↦ T x) (map_mul ρ g h)
  have hsplit : ρ (g * h) x - x = ρ g (ρ h x - x) + (ρ g x - x) := by
    rw [hmul, map_sub]
    abel
  rw [hsplit]
  calc ‖ρ g (ρ h x - x) + (ρ g x - x)‖ ≤ ‖ρ g (ρ h x - x)‖ + ‖ρ g x - x‖ := norm_add_le _ _
    _ = ‖ρ h x - x‖ + ‖ρ g x - x‖ := by rw [LinearIsometryEquiv.norm_map]
    _ = ‖ρ g x - x‖ + ‖ρ h x - x‖ := add_comm _ _

theorem relT_norm_map_mul6_sub_le {G : Type*} [Group G] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) (g₁ g₂ g₃ g₄ g₅ g₆ : G) :
    ‖ρ (g₁ * g₂ * g₃ * g₄ * g₅ * g₆) x - x‖ ≤ ‖ρ g₁ x - x‖ + ‖ρ g₂ x - x‖ + ‖ρ g₃ x - x‖ +
      ‖ρ g₄ x - x‖ + ‖ρ g₅ x - x‖ + ‖ρ g₆ x - x‖ := by
  have h5 := relT_norm_map_mul_sub_le ρ (g₁ * g₂ * g₃ * g₄ * g₅) g₆ x
  have h4 := relT_norm_map_mul_sub_le ρ (g₁ * g₂ * g₃ * g₄) g₅ x
  have h3 := relT_norm_map_mul_sub_le ρ (g₁ * g₂ * g₃) g₄ x
  have h2 := relT_norm_map_mul_sub_le ρ (g₁ * g₂) g₃ x
  have h1 := relT_norm_map_mul_sub_le ρ g₁ g₂ x
  linarith

/-- Burger's bound on one coordinate line: if the six generators of the shear plane
`(a, b) ↦ ι a eᵢ + ι b eⱼ` move a unit vector by at most `δ`, every vector `ι a eᵢ` moves it by
at most `26 (p + 1) δ`. -/
theorem norm_inl_single_le {p : ℕ} [NeZero p] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (ρ : RelTSemi R →* (E ≃ₗᵢ[ℝ] E)) (x : E)
    (hx : ‖x‖ = 1) {δ : ℝ} (hδ : 0 ≤ δ) (ι : Polynomial (ZMod p) →+* R) {i j : Fin 3}
    (h : i ≠ j)
    (hupX : ‖ρ (planeShear i j h (ι Polynomial.X)) x - x‖ ≤ δ)
    (hlowX : ‖ρ (planeShear j i h.symm (ι Polynomial.X)) x - x‖ ≤ δ)
    (hup1 : ‖ρ (planeShear i j h (ι 1)) x - x‖ ≤ δ)
    (hlow1 : ‖ρ (planeShear j i h.symm (ι 1)) x - x‖ ≤ δ)
    (hfst : ‖ρ (planeVec i j (ι 1) (ι 0)) x - x‖ ≤ δ)
    (hsnd : ‖ρ (planeVec i j (ι 0) (ι 1)) x - x‖ ≤ δ) (a : Polynomial (ZMod p)) :
    ‖ρ (SemidirectProduct.inl (Multiplicative.ofAdd (Pi.single i (ι a)))) x - x‖ ≤
      26 * ((p : ℝ) + 1) * δ := by
  have hbound := RelTShear.norm_vec_displacement_le (planeShearData ι h) ρ x hx hδ hupX hlowX
    hup1 hlow1 hfst hsnd a 0
  have hv : (planeShearData ι h).vec (a, 0) =
      SemidirectProduct.inl (Multiplicative.ofAdd (Pi.single i (ι a))) := by
    show planeVec i j (ι a) (ι 0) = _
    rw [map_zero, planeVec_zero_right]
  rw [hv] at hbound
  exact hbound

/-- A vector of `R³` written through two ring maps, as a product of six coordinate vectors in the
normal copy. -/
theorem inl_ofAdd_eq_prod {S : Type*} [Semiring S] (ι₁ ι₂ : S →+* R) (w : Fin 3 → R)
    (a b : Fin 3 → S) (hab : ∀ k, ι₁ (a k) + ι₂ (b k) = w k) :
    (SemidirectProduct.inl (Multiplicative.ofAdd w) : RelTSemi R) =
      SemidirectProduct.inl (Multiplicative.ofAdd (Pi.single 0 (ι₁ (a 0)))) *
        SemidirectProduct.inl (Multiplicative.ofAdd (Pi.single 0 (ι₂ (b 0)))) *
        SemidirectProduct.inl (Multiplicative.ofAdd (Pi.single 1 (ι₁ (a 1)))) *
        SemidirectProduct.inl (Multiplicative.ofAdd (Pi.single 1 (ι₂ (b 1)))) *
        SemidirectProduct.inl (Multiplicative.ofAdd (Pi.single 2 (ι₁ (a 2)))) *
        SemidirectProduct.inl (Multiplicative.ofAdd (Pi.single 2 (ι₂ (b 2)))) := by
  have hv : w = Pi.single 0 (ι₁ (a 0)) + Pi.single 0 (ι₂ (b 0)) + Pi.single 1 (ι₁ (a 1)) +
      Pi.single 1 (ι₂ (b 1)) + Pi.single 2 (ι₁ (a 2)) + Pi.single 2 (ι₂ (b 2)) := by
    conv_lhs => rw [← Finset.univ_sum_single w]
    rw [Fin.sum_univ_three, ← hab 0, ← hab 1, ← hab 2, Pi.single_add, Pi.single_add,
      Pi.single_add]
    abel
  rw [hv]
  simp only [ofAdd_add, map_mul]

end Generic

section Laurent

variable (p : ℕ)

/-- The linear action of `EL_3(F_p[t,t⁻¹])` on `F_p[t,t⁻¹]³`. -/
abbrev relTAction : elementaryGroup (Fin 3) (LaurentPolynomial (ZMod p)) →*
    MulAut (Multiplicative (Fin 3 → LaurentPolynomial (ZMod p))) :=
  relTActionHom (LaurentPolynomial (ZMod p))

theorem relTAction_apply :
    ∀ (A : elementaryGroup (Fin 3) (LaurentPolynomial (ZMod p)))
      (n : Multiplicative (Fin 3 → LaurentPolynomial (ZMod p))),
      relTAction p A n = Multiplicative.ofAdd
        (((A : (Matrix (Fin 3) (Fin 3) (LaurentPolynomial (ZMod p)))ˣ) :
          Matrix (Fin 3) (Fin 3) (LaurentPolynomial (ZMod p))) *ᵥ Multiplicative.toAdd n) :=
  fun _ _ ↦ rfl

/-- The pair `L³ ⋊ EL_3(L)`, `L = F_p[t,t⁻¹]`. -/
abbrev RelTPair : Type :=
  SemidirectProduct (Multiplicative (Fin 3 → LaurentPolynomial (ZMod p)))
    (elementaryGroup (Fin 3) (LaurentPolynomial (ZMod p))) (relTAction p)

/-- The two embeddings `F_p[t] → F_p[t,t⁻¹]`: `t ↦ t` (`true`) and `t ↦ t⁻¹` (`false`). -/
def laurentEmb : Bool → Polynomial (ZMod p) →+* LaurentPolynomial (ZMod p)
  | true => Polynomial.toLaurent
  | false => (LaurentPolynomial.invert (R := ZMod p)).toRingEquiv.toRingHom.comp
      Polynomial.toLaurent

/-- Every Laurent polynomial is `f(t) + g(t⁻¹)` with `f, g ∈ F_p[t]`. -/
theorem exists_laurentEmb_add (f : LaurentPolynomial (ZMod p)) :
    ∃ a b : Polynomial (ZMod p), laurentEmb p true a + laurentEmb p false b = f := by
  induction f using LaurentPolynomial.induction_on' with
  | add f g hf hg =>
    obtain ⟨a₁, b₁, rfl⟩ := hf
    obtain ⟨a₂, b₂, rfl⟩ := hg
    refine ⟨a₁ + a₂, b₁ + b₂, ?_⟩
    rw [map_add, map_add]
    abel
  | C_mul_T n c =>
    obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg n
    · refine ⟨Polynomial.C c * Polynomial.X ^ k, 0, ?_⟩
      show Polynomial.toLaurent (Polynomial.C c * Polynomial.X ^ k) +
          LaurentPolynomial.invert (Polynomial.toLaurent (0 : Polynomial (ZMod p))) = _
      simp only [map_zero, add_zero, Polynomial.toLaurent_C_mul_X_pow]
    · refine ⟨0, Polynomial.C c * Polynomial.X ^ k, ?_⟩
      show Polynomial.toLaurent (0 : Polynomial (ZMod p)) +
          LaurentPolynomial.invert (Polynomial.toLaurent (Polynomial.C c * Polynomial.X ^ k)) = _
      simp only [map_zero, zero_add, Polynomial.toLaurent_C_mul_X_pow, map_mul,
        Polynomial.toLaurent_C, Polynomial.toLaurent_X_pow, LaurentPolynomial.invert_C,
        LaurentPolynomial.invert_T]

theorem fin3_ne_succ (i : Fin 3) : i ≠ i + 1 := by
  revert i
  decide

/-- The generators of the relative Kazhdan pair: for the plane `(eᵢ, eᵢ₊₁)` and the embedding
`laurentEmb p e`, the shears by `X` and `1` (`b₁ = true`, `b₂` upper/lower, `b₃` for `X`/`1`) and
the two unit plane vectors (`b₁ = false`). -/
def relTGen (i : Fin 3) (e b₁ b₂ b₃ : Bool) : RelTPair p :=
  bif b₁ then
    (bif b₂ then
      planeShear i (i + 1) (fin3_ne_succ i)
        (laurentEmb p e (bif b₃ then Polynomial.X else 1))
    else
      planeShear (i + 1) i (fin3_ne_succ i).symm
        (laurentEmb p e (bif b₃ then Polynomial.X else 1)))
  else
    (bif b₂ then planeVec i (i + 1) (laurentEmb p e 1) (laurentEmb p e 0)
    else planeVec i (i + 1) (laurentEmb p e 0) (laurentEmb p e 1))

/-- **Relative property (T) for `(L³ ⋊ EL_3(L), L³)`**, `L = F_p[t,t⁻¹]` (Thom, GGD 4 (2010),
§2.1, Lemma 2.1; Burger 1991, Shalom 1999, Kassabov 2007, §2). -/
theorem isRelativeKazhdanPair_relT [Fact p.Prime] :
    ∃ (Q : Finset (RelTPair p)) (ε : ℝ),
      IsRelativeKazhdanPair.{0, v} (RelTPair p)
        (SemidirectProductKazhdan.normalCopy (relTAction p)) Q ε := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hp0 : (0 : ℝ) < 312 * ((p : ℝ) + 1) := by positivity
  obtain ⟨δ, hδpos, hδeq⟩ : ∃ δ : ℝ, 0 < δ ∧ 312 * ((p : ℝ) + 1) * δ = 1 :=
    ⟨1 / (312 * ((p : ℝ) + 1)), by positivity, mul_one_div_cancel hp0.ne'⟩
  have hfin := Set.finite_range fun t : Fin 3 × Bool × Bool × Bool × Bool ↦
    relTGen p t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2
  refine ⟨hfin.toFinset, δ, isRelativeKazhdanPair_of_displacement _ _ hδpos ?_⟩
  intro E _ _ _ ρ x hx hnear
  have hgen : ∀ (i : Fin 3) (e b₁ b₂ b₃ : Bool), ‖ρ (relTGen p i e b₁ b₂ b₃) x - x‖ ≤ δ :=
    fun i e b₁ b₂ b₃ ↦ (hnear _ (hfin.mem_toFinset.mpr ⟨(i, e, b₁, b₂, b₃), rfl⟩)).le
  have hplane := fun (i : Fin 3) (e : Bool) (a : Polynomial (ZMod p)) ↦
    norm_inl_single_le (R := LaurentPolynomial (ZMod p)) ρ x hx hδpos.le (laurentEmb p e)
      (fin3_ne_succ i) (hgen i e true true true) (hgen i e true false true)
      (hgen i e true true false) (hgen i e true false false) (hgen i e false true true)
      (hgen i e false false true) a
  intro g hg
  rw [← SemidirectProductKazhdan.inl_left_eq_of_mem_normalCopy hg, ← ofAdd_toAdd g.left]
  choose a b hab using fun k ↦ exists_laurentEmb_add p (Multiplicative.toAdd g.left k)
  rw [inl_ofAdd_eq_prod (laurentEmb p true) (laurentEmb p false) (Multiplicative.toAdd g.left)
    a b hab]
  have hsum := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
    (hplane 0 true (a 0)) (hplane 0 false (b 0))) (hplane 1 true (a 1)))
    (hplane 1 false (b 1))) (hplane 2 true (a 2))) (hplane 2 false (b 2))
  refine (relT_norm_map_mul6_sub_le ρ x _ _ _ _ _ _).trans (hsum.trans (le_of_eq ?_))
  linear_combination (1 / 2 : ℝ) * hδeq

end Laurent

end

end GroupApproximation.Full.A2ThomT
