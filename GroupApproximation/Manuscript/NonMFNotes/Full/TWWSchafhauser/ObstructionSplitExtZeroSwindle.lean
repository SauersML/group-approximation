import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ExtensionAbsorbRepeat

/-!
# The amplification swindle for unital normal forms

Lane `TWWSch3d4a-A`, work order `WO-TWWSch-3d-4a`, part A. Manuscript label:
`non_mf_group_notes.tex`, TWW/Schafhauser step 3d-4 (`thm:fixed-radical-membership`). Sources:
G. G. Kasparov, J. Operator Theory 4 (1980), §7; G. A. Elliott and D. Kucerovsky, Pacific J. Math.
198 (2001), proof of Thm. 6; C. Schafhauser, J. reine angew. Math. 759 (2020), §5.

Split generators of `ExtGroup` are allowed to be non-unital. To compare them with unital trivial
extensions, we fill the defect `1 - ρ(1)` with a unital `⋆`-homomorphism, moved into place by an
isometry `V` with range `e ⊕ 1`. The amplification `φ(x) = t₁ φ(x) t₁* + t₂ x t₂*` builds `V`:

`V = s₁ e t₂* + s₂ (φ(f) + φ(e) t₁*)` for complementary projections `e + f = 1`.

* `BusbyCuntzPair.swindleIsometry`: the element `V`;
* `star_swindleIsometry_mul_self`: `V* V = 1`;
* `swindleIsometry_mul_star`: `V V* = s₁ e s₁* + s₂ s₂* = P.diag e 1`;
* `star_s₁_mul_eq_of_mul_star_eq_diag`: an isometry with range `P.diag e 1` satisfies
  `s₁* V = e s₁* V`.
-/

namespace GroupApproximation.Full.TWWSchafhauser

namespace BusbyCuntzPair

section Amplification

variable {𝕜 : Type*} [CommSemiring 𝕜]
variable {E : Type*} [Ring E] [StarRing E] [Algebra 𝕜 E]

/-- `a * (b * x) = c * x` from `a * b = c`: the right-associated form of a product relation. -/
theorem swindle_mul_mul {a b c : E} (h : a * b = c) (x : E) : a * (b * x) = c * x := by
  rw [← mul_assoc, h]

variable {T : BusbyCuntzPair E} {φ : E →⋆ₐ[𝕜] E}

/-- `t₂* φ(x) = x t₂*` for an amplification. -/
theorem amp_star_s₂_mul (hφ : IsBusbyAmplification T φ) (x : E) :
    star T.s₂ * φ x = x * star T.s₂ := by
  rw [hφ x]
  simp only [BusbyCuntzPair.diag, mul_add, ← mul_assoc, T.star_s₂_mul_s₁, T.star_mul_self₂,
    zero_mul, one_mul, zero_add]

/-- `φ(x) t₂ = t₂ x` for an amplification. -/
theorem amp_mul_s₂ (hφ : IsBusbyAmplification T φ) (x : E) : φ x * T.s₂ = T.s₂ * x := by
  rw [hφ x]
  simp only [BusbyCuntzPair.diag, add_mul, mul_assoc, T.star_s₁_mul_s₂, T.star_mul_self₂,
    mul_zero, mul_one, zero_add]

/-- `t₁* φ(x) = φ(x) t₁*` for an amplification. -/
theorem amp_star_s₁_mul (hφ : IsBusbyAmplification T φ) (x : E) :
    star T.s₁ * φ x = φ x * star T.s₁ := by
  conv_lhs => rw [hφ x]
  simp only [BusbyCuntzPair.diag, mul_add, ← mul_assoc, T.star_mul_self₁, T.star_s₁_mul_s₂,
    zero_mul, one_mul, add_zero]

/-- `φ(x) t₁ = t₁ φ(x)` for an amplification. -/
theorem amp_mul_s₁ (hφ : IsBusbyAmplification T φ) (x : E) : φ x * T.s₁ = T.s₁ * φ x := by
  conv_lhs => rw [hφ x]
  simp only [BusbyCuntzPair.diag, add_mul, mul_assoc, T.star_mul_self₁, T.star_s₂_mul_s₁,
    mul_zero, mul_one, add_zero]

/-- The decomposition `t₁ φ(x) t₁* + t₂ x t₂* = φ(x)`, right-associated. -/
theorem amp_decomp (hφ : IsBusbyAmplification T φ) (x : E) :
    T.s₁ * (φ x * star T.s₁) + T.s₂ * (x * star T.s₂) = φ x := by
  conv_rhs => rw [hφ x]
  simp only [BusbyCuntzPair.diag, mul_assoc]

variable (P T φ)

/-- The swindle isometry `V = s₁ e t₂* + s₂ (φ(f) + φ(e) t₁*)`. -/
def swindleIsometry (e f : E) : E :=
  P.s₁ * e * star T.s₂ + P.s₂ * (φ f + φ e * star T.s₁)

variable {P T φ}

/-- Hypotheses on a pair of complementary projections `e + f = 1`. -/
structure SwindleProj (e f : E) : Prop where
  mul_self_left : e * e = e
  mul_self_right : f * f = f
  mul_left_right : e * f = 0
  mul_right_left : f * e = 0
  star_left : star e = e
  star_right : star f = f
  add_eq_one : e + f = 1

/-- `1 - p, p` are complementary projections when `p` is a self-adjoint idempotent. -/
theorem swindleProj_sub_one {p : E} (hp : p * p = p) (hsp : star p = p) : SwindleProj (1 - p) p :=
  { mul_self_left := by rw [sub_mul, one_mul, mul_sub, mul_one, hp, sub_self, sub_zero]
    mul_self_right := hp
    mul_left_right := by rw [sub_mul, one_mul, hp, sub_self]
    mul_right_left := by rw [mul_sub, mul_one, hp, sub_self]
    star_left := by rw [star_sub, star_one, hsp]
    star_right := hsp
    add_eq_one := sub_add_cancel 1 p }

/-- The images of complementary projections under `φ`. -/
theorem SwindleProj.map {e f : E} (h : SwindleProj e f) : SwindleProj (φ e) (φ f) :=
  { mul_self_left := by rw [← map_mul, h.mul_self_left]
    mul_self_right := by rw [← map_mul, h.mul_self_right]
    mul_left_right := by rw [← map_mul, h.mul_left_right, map_zero]
    mul_right_left := by rw [← map_mul, h.mul_right_left, map_zero]
    star_left := by rw [← map_star, h.star_left]
    star_right := by rw [← map_star, h.star_right]
    add_eq_one := by rw [← map_add, h.add_eq_one, map_one] }

/-- **The swindle isometry is an isometry**, `V* V = 1`. -/
theorem star_swindleIsometry_mul_self (hφ : IsBusbyAmplification T φ) {e f : E}
    (h : SwindleProj e f) : star (swindleIsometry P T φ e f) * swindleIsometry P T φ e f = 1 := by
  have hm := h.map (φ := φ)
  calc star (swindleIsometry P T φ e f) * swindleIsometry P T φ e f
      = T.s₁ * (φ e * star T.s₁) + T.s₂ * (e * star T.s₂) + φ f := by
        simp only [swindleIsometry, star_add, star_mul, star_star, h.star_left, hm.star_left,
          hm.star_right, mul_add, add_mul, mul_assoc, P.star_mul_self₁, P.star_mul_self₂,
          swindle_mul_mul P.star_mul_self₁, swindle_mul_mul P.star_mul_self₂,
          P.star_s₁_mul_s₂, P.star_s₂_mul_s₁, swindle_mul_mul P.star_s₁_mul_s₂,
          swindle_mul_mul P.star_s₂_mul_s₁, h.mul_self_left, swindle_mul_mul h.mul_self_left,
          hm.mul_self_left, swindle_mul_mul hm.mul_self_left, hm.mul_self_right,
          swindle_mul_mul hm.mul_self_right, hm.mul_left_right, swindle_mul_mul hm.mul_left_right,
          hm.mul_right_left, swindle_mul_mul hm.mul_right_left, zero_mul, mul_zero, add_zero,
          zero_add]
        all_goals abel
    _ = 1 := by rw [amp_decomp hφ e, hm.add_eq_one]

/-- **The range of the swindle isometry**, `V V* = s₁ e s₁* + s₂ s₂*`. -/
theorem swindleIsometry_mul_star (hφ : IsBusbyAmplification T φ) {e f : E}
    (h : SwindleProj e f) :
    swindleIsometry P T φ e f * star (swindleIsometry P T φ e f) = P.diag e 1 := by
  have hm := h.map (φ := φ)
  have hs₂ : P.s₂ * (φ e * star P.s₂) + P.s₂ * (φ f * star P.s₂) = P.s₂ * star P.s₂ := by
    rw [← mul_add, ← add_mul, hm.add_eq_one, one_mul]
  calc swindleIsometry P T φ e f * star (swindleIsometry P T φ e f)
      = P.s₁ * (e * star P.s₁) + (P.s₂ * (φ e * star P.s₂) + P.s₂ * (φ f * star P.s₂)) := by
        simp only [swindleIsometry, star_add, star_mul, star_star, h.star_left, hm.star_left,
          hm.star_right, mul_add, add_mul, mul_assoc, T.star_mul_self₁, T.star_mul_self₂,
          swindle_mul_mul T.star_mul_self₁, swindle_mul_mul T.star_mul_self₂,
          T.star_s₁_mul_s₂, T.star_s₂_mul_s₁, swindle_mul_mul T.star_s₁_mul_s₂,
          swindle_mul_mul T.star_s₂_mul_s₁, amp_star_s₂_mul hφ f,
          swindle_mul_mul (amp_star_s₂_mul hφ f), amp_mul_s₂ hφ f,
          swindle_mul_mul (amp_mul_s₂ hφ f), amp_mul_s₁ hφ f, swindle_mul_mul (amp_mul_s₁ hφ f),
          amp_star_s₁_mul hφ f, swindle_mul_mul (amp_star_s₁_mul hφ f), h.mul_self_left,
          swindle_mul_mul h.mul_self_left, h.mul_left_right, swindle_mul_mul h.mul_left_right,
          h.mul_right_left, swindle_mul_mul h.mul_right_left, hm.mul_self_left,
          swindle_mul_mul hm.mul_self_left, hm.mul_self_right, swindle_mul_mul hm.mul_self_right,
          hm.mul_left_right, swindle_mul_mul hm.mul_left_right, hm.mul_right_left,
          swindle_mul_mul hm.mul_right_left, zero_mul, mul_zero, add_zero, zero_add]
        all_goals abel
    _ = P.diag e 1 := by
        rw [hs₂, BusbyCuntzPair.diag, mul_one, mul_assoc]

end Amplification

section Corner

variable {E : Type*} [Ring E] [StarRing E] (P : BusbyCuntzPair E)

/-- An isometry `V` with range `P.diag e 1` satisfies `s₁* V = e s₁* V`. -/
theorem star_s₁_mul_eq_of_mul_star_eq_diag {V e : E} (hV : star V * V = 1)
    (hVV : V * star V = P.diag e 1) : star P.s₁ * V = e * (star P.s₁ * V) := by
  calc star P.s₁ * V = star P.s₁ * (V * star V * V) := by rw [mul_assoc V, hV, mul_one]
    _ = star P.s₁ * (P.diag e 1 * V) := by rw [hVV]
    _ = e * (star P.s₁ * V) := by
        simp only [BusbyCuntzPair.diag, add_mul, mul_add, mul_assoc, mul_one,
          swindle_mul_mul P.star_mul_self₁, swindle_mul_mul P.star_s₁_mul_s₂, zero_mul,
          add_zero]

/-- The adjoint form: `V* s₁ = V* s₁ e` when `e` is self-adjoint. -/
theorem star_mul_s₁_eq_of_mul_star_eq_diag {V e : E} (hV : star V * V = 1)
    (hVV : V * star V = P.diag e 1) (he : star e = e) : star V * P.s₁ = star V * P.s₁ * e := by
  have h := congrArg star (P.star_s₁_mul_eq_of_mul_star_eq_diag hV hVV)
  rwa [star_mul, star_star, star_mul, star_mul, star_star, he, ← mul_assoc] at h

end Corner

end BusbyCuntzPair

end GroupApproximation.Full.TWWSchafhauser
