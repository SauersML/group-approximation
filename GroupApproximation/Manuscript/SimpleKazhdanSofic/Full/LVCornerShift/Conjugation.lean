import GroupApproximation.Steinberg.Basic

/-!
# Conjugating Steinberg generators by a corner element (lane LVCornerShift)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii.  Step 3 of the proof of
Ara–Brustenga–Cortiñas, Thm `thm:skewyao` (Münster J. Math. 2 (2009)), uses that the corner
endomorphism `a ↦ u a v` of a ring `S` with `v u = 1` acts trivially on stable `K₂(S)`.  Its
Steinberg-level core is the element

`cornerConj A B u v = x_{AB}(u) x_{BA}(-v) x_{AB}(u-1) x_{BA}(1) x_{AB}(-1)`

of `St_I(S)`, which lifts the matrix `[[u, uv-1], [0, v]]` supported on the indices `A`, `B`.  This
file computes its conjugation action on generators that avoid the index `B`:

* `cornerConj_x_left`: `x_{AK}(b) ↦ x_{AK}(u b)`;
* `cornerConj_x_right`: `x_{JA}(b) ↦ x_{JA}(b v)`;
* `cornerConj_x_other`: generators avoiding `A` and `B` are fixed.

Everything follows from the Steinberg relations alone.
-/

namespace GroupApproximation.Full.LVCornerShift

open SteinbergGroup

section Group

variable {G : Type*} [Group G]

/-- Conjugation by a product is the composite of the conjugations.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem corner_conj_mul (a b h : G) : a * b * h * (a * b)⁻¹ = a * (b * h * b⁻¹) * a⁻¹ := by
  simp only [mul_inv_rev, mul_assoc]

/-- Conjugation distributes over products.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem conj_mul_right (g a b : G) : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by
  simp only [mul_assoc, inv_mul_cancel_left]

end Group

variable {I : Type*} [Fintype I] [DecidableEq I] {S : Type*} [Ring S]

/-- Conjugating `x_{jk}(b)` by `x_{ij}(a)`.  (`simple_kazhdan_sofic_group.tex` l.733-735,
leaf T1b.iii.) -/
theorem conj_left_x (i j k : I) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : S) :
    x i j hij a * x j k hjk b * (x i j hij a)⁻¹ = x i k hik (a * b) * x j k hjk b := by
  rw [← x_commutator i j k hij hjk hik a b, commutatorElement_def, inv_mul_cancel_right]

/-- Conjugating `x_{ij}(a)` by `x_{jk}(b)`.  (`simple_kazhdan_sofic_group.tex` l.733-735,
leaf T1b.iii.) -/
theorem conj_right_x (i j k : I) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : S) :
    x j k hjk b * x i j hij a * (x j k hjk b)⁻¹ = x i j hij a * x i k hik (-a * b) := by
  rw [← x_commutator i j k hij hjk hik (-a) b, x_neg, commutatorElement_def, inv_inv]
  simp only [mul_assoc, mul_inv_cancel_left]

section States

variable {A B : I} (hAB : A ≠ B)

/-- Column state `x_{AK}(p) x_{BK}(q)` under conjugation by `x_{AB}(t)`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem col_upper {K : I} (hAK : A ≠ K) (hBK : B ≠ K) (p q t p' : S) (hp : p' = p + t * q) :
    x A B hAB t * (x A K hAK p * x B K hBK q) * (x A B hAB t)⁻¹ =
      x A K hAK p' * x B K hBK q := by
  subst hp
  have h1 : x A B hAB t * x A K hAK p * (x A B hAB t)⁻¹ = x A K hAK p :=
    (x_commute_of_ne A B A K hAB hAK hAB.symm hAK.symm t p).mul_inv_cancel
  have h2 : x A B hAB t * x B K hBK q * (x A B hAB t)⁻¹ = x A K hAK (t * q) * x B K hBK q :=
    conj_left_x A B K hAB hBK hAK t q
  rw [conj_mul_right, h1, h2, ← mul_assoc, x_mul]

/-- Column state `x_{AK}(p) x_{BK}(q)` under conjugation by `x_{BA}(t)`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem col_lower {K : I} (hAK : A ≠ K) (hBK : B ≠ K) (p q t q' : S) (hq : q' = t * p + q) :
    x B A hAB.symm t * (x A K hAK p * x B K hBK q) * (x B A hAB.symm t)⁻¹ =
      x A K hAK p * x B K hBK q' := by
  subst hq
  have h1 : x B A hAB.symm t * x A K hAK p * (x B A hAB.symm t)⁻¹ =
      x B K hBK (t * p) * x A K hAK p :=
    conj_left_x B A K hAB.symm hAK hBK t p
  have h2 : x B A hAB.symm t * x B K hBK q * (x B A hAB.symm t)⁻¹ = x B K hBK q :=
    (x_commute_of_ne B A B K hAB.symm hBK hAB hBK.symm t q).mul_inv_cancel
  rw [conj_mul_right, h1, h2,
    (x_commute_of_ne B K A K hBK hAK hAK.symm hBK.symm (t * p) p).eq, mul_assoc, x_mul]

/-- Row state `x_{JA}(p) x_{JB}(q)` under conjugation by `x_{AB}(t)`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem row_upper {J : I} (hJA : J ≠ A) (hJB : J ≠ B) (p q t q' : S) (hq : q' = -p * t + q) :
    x A B hAB t * (x J A hJA p * x J B hJB q) * (x A B hAB t)⁻¹ =
      x J A hJA p * x J B hJB q' := by
  subst hq
  have h1 : x A B hAB t * x J A hJA p * (x A B hAB t)⁻¹ = x J A hJA p * x J B hJB (-p * t) :=
    conj_right_x J A B hJA hAB hJB p t
  have h2 : x A B hAB t * x J B hJB q * (x A B hAB t)⁻¹ = x J B hJB q :=
    (x_commute_of_ne A B J B hAB hJB hJB.symm hAB.symm t q).mul_inv_cancel
  rw [conj_mul_right, h1, h2, mul_assoc, x_mul]

/-- Row state `x_{JA}(p) x_{JB}(q)` under conjugation by `x_{BA}(t)`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem row_lower {J : I} (hJA : J ≠ A) (hJB : J ≠ B) (p q t p' : S) (hp : p' = p + -q * t) :
    x B A hAB.symm t * (x J A hJA p * x J B hJB q) * (x B A hAB.symm t)⁻¹ =
      x J A hJA p' * x J B hJB q := by
  subst hp
  have h1 : x B A hAB.symm t * x J A hJA p * (x B A hAB.symm t)⁻¹ = x J A hJA p :=
    (x_commute_of_ne B A J A hAB.symm hJA hJA.symm hAB t p).mul_inv_cancel
  have h2 : x B A hAB.symm t * x J B hJB q * (x B A hAB.symm t)⁻¹ =
      x J B hJB q * x J A hJA (-q * t) :=
    conj_right_x J B A hJB hAB.symm hJA q t
  rw [conj_mul_right, h1, h2,
    (x_commute_of_ne J B J A hJB hJA hJB.symm hJA.symm q (-q * t)).eq, ← mul_assoc, x_mul]

end States

/-- The corner element `x_{AB}(u) x_{BA}(-v) x_{AB}(u-1) x_{BA}(1) x_{AB}(-1)` of `St_I(S)`,
a lift of the matrix `[[u, uv-1], [0, v]]` on the indices `A`, `B` (`simple_kazhdan_sofic_group.tex`
l.733-735, leaf T1b.iii; ABC 2009, proof of `thm:skewyao`, Step 3). -/
def cornerConj {A B : I} (hAB : A ≠ B) (u v : S) : SteinbergGroup I S :=
  x A B hAB u * x B A hAB.symm (-v) * x A B hAB (u - 1) * x B A hAB.symm 1 * x A B hAB (-1)

section Corner

variable {A B : I} (hAB : A ≠ B) {u v : S}

/-- The corner element multiplies the coefficient of `x_{AK}` on the left by `u`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem cornerConj_x_left {K : I} (hAK : A ≠ K) (hBK : B ≠ K) (hvu : v * u = 1) (b : S) :
    cornerConj hAB u v * x A K hAK b * (cornerConj hAB u v)⁻¹ = x A K hAK (u * b) := by
  have e0 : x A K hAK b = x A K hAK b * x B K hBK 0 := by rw [x_zero, mul_one]
  rw [cornerConj, corner_conj_mul, corner_conj_mul, corner_conj_mul, corner_conj_mul, e0,
    col_upper hAB hAK hBK b 0 (-1) b (by rw [mul_zero, add_zero]),
    col_lower hAB hAK hBK b 0 1 b (by rw [one_mul, add_zero]),
    col_upper hAB hAK hBK b b (u - 1) (u * b) (by rw [sub_mul, one_mul, add_sub_cancel]),
    col_lower hAB hAK hBK (u * b) b (-v) 0
      (by rw [neg_mul, ← mul_assoc, hvu, one_mul, neg_add_cancel]),
    col_upper hAB hAK hBK (u * b) 0 u (u * b) (by rw [mul_zero, add_zero]), x_zero, mul_one]

/-- The corner element multiplies the coefficient of `x_{JA}` on the right by `v`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem cornerConj_x_right {J : I} (hJA : J ≠ A) (hJB : J ≠ B) (hvu : v * u = 1) (b : S) :
    cornerConj hAB u v * x J A hJA b * (cornerConj hAB u v)⁻¹ = x J A hJA (b * v) := by
  have e0 : x J A hJA b = x J A hJA b * x J B hJB 0 := by rw [x_zero, mul_one]
  rw [cornerConj, corner_conj_mul, corner_conj_mul, corner_conj_mul, corner_conj_mul, e0,
    row_upper hAB hJA hJB b 0 (-1) b (by rw [mul_neg, mul_one, neg_neg, add_zero]),
    row_lower hAB hJA hJB b b 1 0 (by rw [mul_one, add_neg_cancel]),
    row_upper hAB hJA hJB 0 b (u - 1) b (by rw [neg_zero, zero_mul, zero_add]),
    row_lower hAB hJA hJB 0 b (-v) (b * v) (by rw [zero_add, neg_mul_neg]),
    row_upper hAB hJA hJB (b * v) b u 0
      (by rw [neg_mul, mul_assoc, hvu, mul_one, neg_add_cancel]), x_zero, mul_one]

/-- The corner element fixes every generator whose indices avoid `A` and `B`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem cornerConj_x_other {i j : I} (hij : i ≠ j) (hiA : i ≠ A) (hiB : i ≠ B)
    (hjA : j ≠ A) (hjB : j ≠ B) (b : S) :
    cornerConj hAB u v * x i j hij b * (cornerConj hAB u v)⁻¹ = x i j hij b := by
  have hU : ∀ t : S, x A B hAB t * x i j hij b * (x A B hAB t)⁻¹ = x i j hij b := fun t =>
    (x_commute_of_ne A B i j hAB hij hiB.symm hjA t b).mul_inv_cancel
  have hL : ∀ t : S, x B A hAB.symm t * x i j hij b * (x B A hAB.symm t)⁻¹ = x i j hij b :=
    fun t => (x_commute_of_ne B A i j hAB.symm hij hiA.symm hjB t b).mul_inv_cancel
  rw [cornerConj, corner_conj_mul, corner_conj_mul, corner_conj_mul, corner_conj_mul, hU (-1), hL 1, hU (u - 1), hL (-v),
    hU u]

end Corner

end GroupApproximation.Full.LVCornerShift
