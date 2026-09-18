import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionSplit

/-!
# Domination implies absorption

Lane `TWWSch3c2`, work order `WO-TWWSch-3c-2`: the ring-level step of the Elliott–Kucerovsky theorem.

This is the algebraic half of G. A. Elliott and D. Kucerovsky, *An abstract
Voiculescu–Brown–Douglas–Fillmore absorption theorem*, Pacific J. Math. 198 (2001), Thm. 6. The
same argument is Kasparov's "domination implies absorption" (Kasparov, J. Operator Theory 4
(1980), §7), and it is used in C. Schafhauser, J. reine angew. Math. 759 (2020), §5.
Manuscript label: `non_mf_group_notes.tex`, `thm:fixed-radical-membership` (the absorption step).

Setting: `π : E →⋆ₐ[R] Q`, for instance the quotient `M → C = M/J` of the multiplier (or adjointable)
algebra by the ideal. Suppose `σ ∈ 𝒯` has an *infinite repeat* `ρ : S →⋆ₐ[R] E`, so that
`ρ = T.diag ρ σ` exactly in `E` for some Cuntz pair `T` of `E`. Suppose also that the Busby map `θ`
*dominates* `ρ` through an isometry `w ∈ E`, meaning `θ(s) π(w) = π(w) π(ρ(s))`. Then
`θ ⊕ π ∘ σ` is strongly unitarily equivalent to `θ`.

The unitary is written out explicitly. `A = (1 - w w*) + w t₁ w*` and `B = w t₂` form a Cuntz pair
of `E` with `A θ A* + B σ B* = θ` in `Q`, and the transfer unitary from the given pair to `(A, B)`
implements the equivalence.

* `absorbPair`: the pair `(A, B)`.
* `absorb_diag_eq` / `absorbPair_diag`: `A x A* + B z B* = x`.
* `busby_mul_isometry_of_compress`: in a quotient where `d* d = 0 ⇒ d = 0` (for example a
  C⋆-algebra), `w* θ w = σ` for `⋆`-homomorphisms forces `θ w = w σ`.
* `isStronglyAbsorbingBusby_of_dominates` and `isStronglyAbsorbingBusby_of_compress_dominates`:
  domination of infinite repeats gives strong absorption.
-/

namespace GroupApproximation.Full.TWWSchafhauser

section Elements

variable {A : Type*} [Ring A] [StarRing A]

theorem absorb_proj_mul_isometry {w : A} (hw : star w * w = 1) : (1 - w * star w) * w = 0 := by
  rw [sub_mul, one_mul, mul_assoc w (star w) w, hw, mul_one, sub_self]

theorem absorb_isometry_star_mul_proj {w : A} (hw : star w * w = 1) :
    star w * (1 - w * star w) = 0 := by
  rw [mul_sub, mul_one, ← mul_assoc (star w) w (star w), hw, one_mul, sub_self]

theorem absorb_proj_mul_proj {w : A} (hw : star w * w = 1) :
    (1 - w * star w) * (1 - w * star w) = 1 - w * star w := by
  rw [mul_sub (1 - w * star w) 1 (w * star w), mul_one,
    ← mul_assoc (1 - w * star w) w (star w), absorb_proj_mul_isometry hw, zero_mul, sub_zero]

theorem absorb_proj_mul_left {w : A} (hw : star w * w = 1) (t : A) :
    (1 - w * star w) * (w * t * star w) = 0 := by
  rw [← mul_assoc (1 - w * star w) (w * t) (star w), ← mul_assoc (1 - w * star w) w t,
    absorb_proj_mul_isometry hw, zero_mul, zero_mul]

theorem absorb_mul_proj {w : A} (hw : star w * w = 1) (t : A) :
    (w * t * star w) * (1 - w * star w) = 0 := by
  rw [mul_assoc (w * t) (star w) (1 - w * star w), absorb_isometry_star_mul_proj hw, mul_zero]

theorem absorb_conj_mul_conj {w : A} (hw : star w * w = 1) (t t' : A) :
    (w * t * star w) * (w * t' * star w) = w * (t * t') * star w := by
  simp only [mul_assoc]
  rw [← mul_assoc (star w) w, hw, one_mul]

theorem absorb_star_s₁ (T : BusbyCuntzPair A) (w : A) :
    star (1 - w * star w + w * T.s₁ * star w) = 1 - w * star w + w * star T.s₁ * star w := by
  simp only [star_add, star_sub, star_one, star_mul, star_star, mul_assoc]

theorem absorb_star_mul_self₁ (T : BusbyCuntzPair A) {w : A} (hw : star w * w = 1) :
    star (1 - w * star w + w * T.s₁ * star w) * (1 - w * star w + w * T.s₁ * star w) = 1 := by
  rw [absorb_star_s₁ T w, add_mul, mul_add, mul_add, absorb_proj_mul_proj hw,
    absorb_proj_mul_left hw, absorb_mul_proj hw, absorb_conj_mul_conj hw, T.star_mul_self₁, mul_one,
    add_zero, zero_add, sub_add_cancel]

theorem absorb_star_mul_self₂ (T : BusbyCuntzPair A) {w : A} (hw : star w * w = 1) :
    star (w * T.s₂) * (w * T.s₂) = 1 := by
  rw [star_mul, mul_assoc (star T.s₂) (star w) (w * T.s₂), ← mul_assoc (star w) w T.s₂, hw, one_mul,
    T.star_mul_self₂]

theorem absorb_sum_eq_one (T : BusbyCuntzPair A) {w : A} (hw : star w * w = 1) :
    (1 - w * star w + w * T.s₁ * star w) * star (1 - w * star w + w * T.s₁ * star w) +
      w * T.s₂ * star (w * T.s₂) = 1 := by
  have h2 : w * T.s₂ * star (w * T.s₂) = w * (T.s₂ * star T.s₂) * star w := by
    simp only [star_mul, mul_assoc]
  rw [absorb_star_s₁ T w, add_mul, mul_add, mul_add, absorb_proj_mul_proj hw,
    absorb_proj_mul_left hw, absorb_mul_proj hw, absorb_conj_mul_conj hw, add_zero, zero_add, h2,
    add_assoc, ← add_mul, ← mul_add, T.sum_eq_one, mul_one, sub_add_cancel]

/-- The Cuntz pair `((1 - w w*) + w t₁ w*, w t₂)` built from an isometry `w` and a Cuntz pair `T`
(Elliott–Kucerovsky 2001, proof of Thm. 6). -/
def absorbPair (T : BusbyCuntzPair A) (w : A) (hw : star w * w = 1) : BusbyCuntzPair A where
  s₁ := 1 - w * star w + w * T.s₁ * star w
  s₂ := w * T.s₂
  star_mul_self₁ := absorb_star_mul_self₁ T hw
  star_mul_self₂ := absorb_star_mul_self₂ T hw
  sum_eq_one := absorb_sum_eq_one T hw

theorem absorbPair_s₁ (T : BusbyCuntzPair A) (w : A) (hw : star w * w = 1) :
    (absorbPair T w hw).s₁ = 1 - w * star w + w * T.s₁ * star w := rfl

theorem absorbPair_s₂ (T : BusbyCuntzPair A) (w : A) (hw : star w * w = 1) :
    (absorbPair T w hw).s₂ = w * T.s₂ := rfl

/-- `x` commutes with the range projection `w w*` once `x w = w y` and `w* x = y w*`. -/
theorem absorb_comm_proj {w x y : A} (hxw : x * w = w * y) (hwx : star w * x = y * star w) :
    x * (1 - w * star w) = (1 - w * star w) * x := by
  have h : x * (w * star w) = w * star w * x := by
    rw [← mul_assoc x w (star w), hxw, mul_assoc w y (star w), mul_assoc w (star w) x, hwx]
  rw [mul_sub, sub_mul, mul_one, one_mul, h]

/-- **The absorption identity.** With `x w = w y`, `w* x = y w*` and `y = t₁ y t₁* + t₂ z t₂*`,
the pair `absorbPair T w` satisfies `A x A* + B z B* = x`. -/
theorem absorb_diag_eq (T : BusbyCuntzPair A) {w : A} (hw : star w * w = 1) {x y z : A}
    (hxw : x * w = w * y) (hwx : star w * x = y * star w) (hy : y = T.diag y z) :
    (1 - w * star w + w * T.s₁ * star w) * x * star (1 - w * star w + w * T.s₁ * star w) +
      w * T.s₂ * z * star (w * T.s₂) = x := by
  have hcq := absorb_comm_proj hxw hwx
  have hA : (1 - w * star w) * x * (1 - w * star w) = (1 - w * star w) * x := by
    rw [mul_assoc (1 - w * star w) x (1 - w * star w), hcq,
      ← mul_assoc (1 - w * star w) (1 - w * star w) x, absorb_proj_mul_proj hw]
  have hB : w * T.s₁ * star w * x * (1 - w * star w) = 0 := by
    rw [mul_assoc (w * T.s₁ * star w) x (1 - w * star w), hcq,
      ← mul_assoc (w * T.s₁ * star w) (1 - w * star w) x, absorb_mul_proj hw, zero_mul]
  have hxm : x * (w * star T.s₁ * star w) = w * (y * star T.s₁) * star w := by
    rw [← mul_assoc x (w * star T.s₁) (star w), ← mul_assoc x w (star T.s₁), hxw,
      mul_assoc w y (star T.s₁)]
  have hC : (1 - w * star w) * x * (w * star T.s₁ * star w) = 0 := by
    rw [mul_assoc (1 - w * star w) x (w * star T.s₁ * star w), hxm, absorb_proj_mul_left hw]
  have hD : w * T.s₁ * star w * x * (w * star T.s₁ * star w) =
      w * (T.s₁ * y * star T.s₁) * star w := by
    simp only [mul_assoc]
    rw [← mul_assoc (star w) x, hwx, mul_assoc y (star w), ← mul_assoc (star w) w, hw, one_mul]
  have hE : w * T.s₂ * z * star (w * T.s₂) = w * (T.s₂ * z * star T.s₂) * star w := by
    simp only [star_mul, mul_assoc]
  have hy' : T.s₁ * y * star T.s₁ + T.s₂ * z * star T.s₂ = y := hy.symm
  have hwy : w * y * star w = w * star w * x := by
    rw [mul_assoc w y (star w), ← hwx, ← mul_assoc w (star w) x]
  rw [absorb_star_s₁ T w, hE]
  simp only [add_mul, mul_add]
  rw [hA, hB, hC, hD]
  simp only [add_zero, zero_add]
  rw [add_assoc, ← add_mul, ← mul_add, hy', hwy, ← add_mul, sub_add_cancel, one_mul]

theorem absorbPair_diag (T : BusbyCuntzPair A) {w : A} (hw : star w * w = 1) {x y z : A}
    (hxw : x * w = w * y) (hwx : star w * x = y * star w) (hy : y = T.diag y z) :
    (absorbPair T w hw).diag x z = x :=
  absorb_diag_eq T hw hxw hwx hy

end Elements

section Busby

variable {R : Type*} [CommSemiring R]
variable {S : Type*} [Semiring S] [Algebra R S] [Star S]
variable {E : Type*} [Ring E] [StarRing E] [Algebra R E]
variable {Q : Type*} [Ring Q] [StarRing Q] [Algebra R Q]

/-- The image of a transfer unitary is the transfer unitary of the image pairs. -/
theorem absorb_map_transfer (P P' : BusbyCuntzPair E) (f : E →⋆ₐ[R] Q) :
    f (BusbyCuntzPair.transfer P P') = BusbyCuntzPair.transfer (P.map f) (P'.map f) := by
  show f (P'.s₁ * star P.s₁ + P'.s₂ * star P.s₂) =
    f P'.s₁ * star (f P.s₁) + f P'.s₂ * star (f P.s₂)
  simp only [map_add, map_mul, map_star]

/-- If `θ w = w σ` for `⋆`-homomorphisms, then also `w* θ = σ w*`. -/
theorem busby_star_isometry_mul {θ σ : S →⋆ₐ[R] Q} {a : Q} (hxw : ∀ s, θ s * a = a * σ s)
    (s : S) : star a * θ s = σ s * star a := by
  have h := congrArg star (hxw (star s))
  rwa [star_mul, star_mul, map_star θ, map_star σ, star_star, star_star] at h

/-- **Compression by an isometry forces intertwining** (Elliott–Kucerovsky 2001, §2). In a ring
where `d* d = 0 ⇒ d = 0`, for example a C⋆-algebra, `a* θ(s) a = σ(s)` for `⋆`-homomorphisms and
an isometry `a` gives `θ(s) a = a σ(s)`. -/
theorem busby_mul_isometry_of_compress (hQ : ∀ d : Q, star d * d = 0 → d = 0)
    {θ σ : S →⋆ₐ[R] Q} {a : Q} (ha : star a * a = 1) (h : ∀ s, star a * θ s * a = σ s) (s : S) :
    θ s * a = a * σ s := by
  apply sub_eq_zero.mp
  apply hQ
  have hst : star (θ s * a - a * σ s) = star a * θ (star s) - σ (star s) * star a := by
    rw [star_sub, star_mul, star_mul, map_star θ s, map_star σ s]
  have t1 : star a * θ (star s) * (θ s * a) = σ (star s) * σ s := by
    rw [← map_mul σ, ← h (star s * s), map_mul θ]
    simp only [mul_assoc]
  have t2 : star a * θ (star s) * (a * σ s) = σ (star s) * σ s := by
    rw [← mul_assoc (star a * θ (star s)) a (σ s), h (star s)]
  have t3 : σ (star s) * star a * (θ s * a) = σ (star s) * σ s := by
    rw [mul_assoc (σ (star s)) (star a) (θ s * a), ← mul_assoc (star a) (θ s) a, h s]
  have t4 : σ (star s) * star a * (a * σ s) = σ (star s) * σ s := by
    rw [mul_assoc (σ (star s)) (star a) (a * σ s), ← mul_assoc (star a) a (σ s), ha, one_mul]
  rw [hst, sub_mul, mul_sub, mul_sub, t1, t2, t3, t4]
  simp only [sub_self]

/-- **Domination of an infinite repeat gives strong absorption** (Elliott–Kucerovsky 2001, Thm. 6;
Kasparov 1980, §7). `ρ = T.diag ρ σ` in `E`, `w ∈ E` is an isometry and `θ(s) π(w) = π(w) π(ρ(s))`.
Then `θ ⊕ π ∘ σ` (formed with any Cuntz pair of `E`) is strongly unitarily equivalent to `θ`. -/
theorem isStronglyUnitarilyEquivalentBusby_sumBusby_of_intertwine (π : E →⋆ₐ[R] Q)
    (P : BusbyCuntzPair E) (θ : S →⋆ₐ[R] Q) (σ ρ : S →⋆ₐ[R] E) (T : BusbyCuntzPair E)
    (hT : ∀ s, ρ s = T.diag (ρ s) (σ s)) {w : E} (hw : star w * w = 1)
    (hint : ∀ s, θ s * π w = π w * π (ρ s)) :
    IsStronglyUnitarilyEquivalentBusby π ((P.map π).sumBusby θ (π.comp σ)) θ := by
  have hw' : star (π w) * π w = 1 := by
    rw [← map_star π w, ← map_mul π (star w) w, hw, map_one π]
  have hint' : ∀ s, θ s * π w = π w * (π.comp ρ) s := fun s => hint s
  refine ⟨BusbyCuntzPair.transfer P (absorbPair T w hw),
    BusbyCuntzPair.transfer_mem_unitary P (absorbPair T w hw), fun s => ?_⟩
  rw [BusbyCuntzPair.sumBusby_apply, absorb_map_transfer, BusbyCuntzPair.transfer_conj_diag]
  have hy : π (ρ s) = (T.map π).diag (π (ρ s)) (π (σ s)) := by
    rw [← T.map_diag π (ρ s) (σ s), ← hT s]
  have key := absorb_diag_eq (T.map π) hw' (hint s) (busby_star_isometry_mul hint' s) hy
  have e₁ : π (1 - w * star w + w * T.s₁ * star w) =
      1 - π w * star (π w) + π w * (T.map π).s₁ * star (π w) := by
    show π (1 - w * star w + w * T.s₁ * star w) = 1 - π w * star (π w) + π w * π T.s₁ * star (π w)
    simp only [map_add, map_sub, map_one, map_mul, map_star]
  have e₂ : π (w * T.s₂) = π w * (T.map π).s₂ := map_mul π w T.s₂
  show θ s = π (1 - w * star w + w * T.s₁ * star w) * θ s *
      star (π (1 - w * star w + w * T.s₁ * star w)) + π (w * T.s₂) * π (σ s) * star (π (w * T.s₂))
  rw [e₁, e₂]
  exact key.symm

/-- **Strong absorption from domination** (Elliott–Kucerovsky 2001, Thm. 6, algebraic half). Every
`σ ∈ 𝒯` needs an infinite repeat `ρ = T.diag ρ σ` in `E` that `θ` dominates through an isometry of
`E`. -/
theorem isStronglyAbsorbingBusby_of_dominates (π : E →⋆ₐ[R] Q) (P : BusbyCuntzPair E)
    {𝒯 : Set (S →⋆ₐ[R] E)} {θ : S →⋆ₐ[R] Q}
    (hdom : ∀ σ ∈ 𝒯, ∃ ρ : S →⋆ₐ[R] E, ∃ T : BusbyCuntzPair E, (∀ s, ρ s = T.diag (ρ s) (σ s)) ∧
      ∃ w : E, star w * w = 1 ∧ ∀ s, θ s * π w = π w * π (ρ s)) :
    IsStronglyAbsorbingBusby π (P.map π) 𝒯 θ := by
  intro σ hσ
  obtain ⟨ρ, T, hT, w, hw, hint⟩ := hdom σ hσ
  exact isStronglyUnitarilyEquivalentBusby_sumBusby_of_intertwine π P θ σ ρ T hT hw hint

/-- The compression form: domination `π(w)* θ(s) π(w) = π(ρ(s))` in a quotient where
`d* d = 0 ⇒ d = 0`. -/
theorem isStronglyAbsorbingBusby_of_compress_dominates (hQ : ∀ d : Q, star d * d = 0 → d = 0)
    (π : E →⋆ₐ[R] Q) (P : BusbyCuntzPair E) {𝒯 : Set (S →⋆ₐ[R] E)} {θ : S →⋆ₐ[R] Q}
    (hdom : ∀ σ ∈ 𝒯, ∃ ρ : S →⋆ₐ[R] E, ∃ T : BusbyCuntzPair E, (∀ s, ρ s = T.diag (ρ s) (σ s)) ∧
      ∃ w : E, star w * w = 1 ∧ ∀ s, star (π w) * θ s * π w = π (ρ s)) :
    IsStronglyAbsorbingBusby π (P.map π) 𝒯 θ := by
  refine isStronglyAbsorbingBusby_of_dominates π P fun σ hσ => ?_
  obtain ⟨ρ, T, hT, w, hw, hcomp⟩ := hdom σ hσ
  have hw' : star (π w) * π w = 1 := by
    rw [← map_star π w, ← map_mul π (star w) w, hw, map_one π]
  have hcomp' : ∀ s, star (π w) * θ s * π w = (π.comp ρ) s := fun s => hcomp s
  exact ⟨ρ, T, hT, w, hw, fun s => busby_mul_isometry_of_compress hQ hw' hcomp' s⟩

end Busby

end GroupApproximation.Full.TWWSchafhauser
