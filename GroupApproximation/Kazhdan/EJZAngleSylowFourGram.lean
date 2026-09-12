import GroupApproximation.Kazhdan.EJZAngleBessel

/-!
# The Gram sum of the Sylow subgroup `U₄(p)` of `Sp₄(F_p)`

Let `w = [a, b]` and `z = [w, b]` (so `ab = baw`, `wb = bwz`), with `w, z` commuting with `a`, `z`
commuting with `b` and `w`, and `bᵖ = wᵖ = zᵖ = 1`: the relations of
`U₄(p) = ⟨a, b | aᵖ, bᵖ, [a,b,a], [a,b,b,a], [a,b,b,b]⟩` (Caprace--Conder--Kaluba--Witzel,
arXiv:2011.09276, Proposition 7.2(ii)).  Then `a bᵐ = bᵐ a tₘ` with `tₘ = wᵐ z^{m(m-1)/2}`, and
for an `a`-fixed vector `x` orthogonal to the `z`-fixed vectors

  `∑_{0 < m < p} ⟪x, ρ(bᵐ) x⟫ ≤ ‖x‖²`   (`gram_sum_le_sylowFour`).

This is the character-free form of the count in CCKW Proposition 7.3(ii) that the `a`-fixed space
of an irreducible representation has dimension at most two.  Averaging the correlation over
`⟨tₘ⟩` gives `p² ⟪x, ρ(bᵐ) x⟫ = ⟪ρ(b^{p-m}) Sₘ, Tₘ⟫` with `Tₘ`, `Sₘ` the translate sums of `x` over
`⟨tₘ⟩` and `⟨sₘ⟩`, `sₘ = wᵐ z^{m(m-1)/2 + m(p-m)}`.  The cyclic subgroups `⟨tₘ⟩` are pairwise
transversal lines of `⟨w, z⟩ ≅ F_p²`, and so are the `⟨sₘ⟩`; the transversality is supplied as two
exponent tables (hypotheses `tableT`, `tableS`, decided for each prime separately), and Bessel's
inequality for translate sums bounds `∑ ‖Tₘ‖²` and `∑ ‖Sₘ‖²` by `p² ‖x‖²`.
-/

namespace GroupApproximation

universe u v

namespace EJZAngleSylowFourGram

open EJZAngleTranslates EJZAngleBessel

/-- `triangular m = m(m-1)/2`, by its recursion. -/
def triangular : ℕ → ℕ
  | 0 => 0
  | m + 1 => triangular m + m

variable {G : Type u} [Group G]

section Identities

variable {a b w z : G}

/-- From `wb = bwz` with `z` commuting with `w`: `wᵐ b = b wᵐ zᵐ`. -/
theorem pow_mul_eq_of_commutator (hwb : w * b = b * w * z) (hzw : Commute z w) (m : ℕ) :
    w ^ m * b = b * w ^ m * z ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc
      w ^ (m + 1) * b = w * (w ^ m * b) := by rw [pow_succ', mul_assoc]
      _ = w * (b * w ^ m * z ^ m) := by rw [ih]
      _ = (w * b) * w ^ m * z ^ m := by simp only [mul_assoc]
      _ = (b * w * z) * w ^ m * z ^ m := by rw [hwb]
      _ = b * w * (z * w ^ m) * z ^ m := by simp only [mul_assoc]
      _ = b * w * (w ^ m * z) * z ^ m := by rw [(hzw.pow_right m).eq]
      _ = b * (w * w ^ m) * (z * z ^ m) := by simp only [mul_assoc]
      _ = b * w ^ (m + 1) * z ^ (m + 1) := by rw [← pow_succ', ← pow_succ']

/-- `wⁱ bⁿ = bⁿ wⁱ z^{in}`. -/
theorem pow_mul_pow_eq_of_commutator (hwb : w * b = b * w * z) (hzw : Commute z w)
    (hzb : Commute z b) (i n : ℕ) : w ^ i * b ^ n = b ^ n * w ^ i * z ^ (i * n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      w ^ i * b ^ (n + 1) = (w ^ i * b ^ n) * b := by rw [pow_succ, mul_assoc]
      _ = b ^ n * w ^ i * z ^ (i * n) * b := by rw [ih]
      _ = b ^ n * w ^ i * (z ^ (i * n) * b) := by simp only [mul_assoc]
      _ = b ^ n * w ^ i * (b * z ^ (i * n)) := by rw [(hzb.pow_left (i * n)).eq]
      _ = b ^ n * (w ^ i * b) * z ^ (i * n) := by simp only [mul_assoc]
      _ = b ^ n * (b * w ^ i * z ^ i) * z ^ (i * n) := by
        rw [pow_mul_eq_of_commutator hwb hzw i]
      _ = (b ^ n * b) * w ^ i * (z ^ i * z ^ (i * n)) := by simp only [mul_assoc]
      _ = b ^ (n + 1) * w ^ i * z ^ (i * (n + 1)) := by
        rw [← pow_succ, ← pow_add, mul_add, mul_one, add_comm (i * n) i]

/-- **`a bᵐ = bᵐ a (wᵐ z^{m(m-1)/2})`.** -/
theorem mul_pow_eq_sylowFour (hab : a * b = b * a * w) (hwb : w * b = b * w * z)
    (hzw : Commute z w) (hzb : Commute z b) (m : ℕ) :
    a * b ^ m = b ^ m * a * (w ^ m * z ^ triangular m) := by
  induction m with
  | zero => simp [triangular]
  | succ m ih =>
    have htri : triangular (m + 1) = m + triangular m := Nat.add_comm _ _
    calc
      a * b ^ (m + 1) = (a * b ^ m) * b := by rw [pow_succ, mul_assoc]
      _ = b ^ m * a * (w ^ m * z ^ triangular m) * b := by rw [ih]
      _ = b ^ m * a * w ^ m * (z ^ triangular m * b) := by simp only [mul_assoc]
      _ = b ^ m * a * w ^ m * (b * z ^ triangular m) := by
        rw [(hzb.pow_left (triangular m)).eq]
      _ = b ^ m * a * (w ^ m * b) * z ^ triangular m := by simp only [mul_assoc]
      _ = b ^ m * a * (b * w ^ m * z ^ m) * z ^ triangular m := by
        rw [pow_mul_eq_of_commutator hwb hzw m]
      _ = b ^ m * (a * b) * w ^ m * (z ^ m * z ^ triangular m) := by simp only [mul_assoc]
      _ = b ^ m * (b * a * w) * w ^ m * (z ^ m * z ^ triangular m) := by rw [hab]
      _ = (b ^ m * b) * a * (w * w ^ m) * (z ^ m * z ^ triangular m) := by
        simp only [mul_assoc]
      _ = b ^ (m + 1) * a * (w ^ (m + 1) * z ^ triangular (m + 1)) := by
        rw [← pow_succ, ← pow_succ', ← pow_add, htri]
        simp only [mul_assoc]

/-- `(wⁱ zʲ) bⁿ = bⁿ (wⁱ z^{j + in})`. -/
theorem coord_mul_pow_eq (hwb : w * b = b * w * z) (hzw : Commute z w) (hzb : Commute z b)
    (i j n : ℕ) : (w ^ i * z ^ j) * b ^ n = b ^ n * (w ^ i * z ^ (j + i * n)) := by
  calc
    (w ^ i * z ^ j) * b ^ n = w ^ i * (z ^ j * b ^ n) := by rw [mul_assoc]
    _ = w ^ i * (b ^ n * z ^ j) := by rw [(hzb.pow_pow j n).eq]
    _ = (w ^ i * b ^ n) * z ^ j := by simp only [mul_assoc]
    _ = (b ^ n * w ^ i * z ^ (i * n)) * z ^ j := by
      rw [pow_mul_pow_eq_of_commutator hwb hzw hzb i n]
    _ = b ^ n * (w ^ i * (z ^ (i * n) * z ^ j)) := by simp only [mul_assoc]
    _ = b ^ n * (w ^ i * z ^ (j + i * n)) := by rw [← pow_add, add_comm (i * n) j]

/-- `(wⁱ zʲ)ᵏ bⁿ = bⁿ (wⁱ z^{j + in})ᵏ`. -/
theorem coord_pow_mul_pow_eq (hwb : w * b = b * w * z) (hzw : Commute z w) (hzb : Commute z b)
    (i j n k : ℕ) : (w ^ i * z ^ j) ^ k * b ^ n = b ^ n * (w ^ i * z ^ (j + i * n)) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      (w ^ i * z ^ j) ^ (k + 1) * b ^ n = (w ^ i * z ^ j) * ((w ^ i * z ^ j) ^ k * b ^ n) := by
        rw [pow_succ']
        simp only [mul_assoc]
      _ = (w ^ i * z ^ j) * (b ^ n * (w ^ i * z ^ (j + i * n)) ^ k) := by rw [ih]
      _ = ((w ^ i * z ^ j) * b ^ n) * (w ^ i * z ^ (j + i * n)) ^ k := by
        simp only [mul_assoc]
      _ = (b ^ n * (w ^ i * z ^ (j + i * n))) * (w ^ i * z ^ (j + i * n)) ^ k := by
        rw [coord_mul_pow_eq hwb hzw hzb i j n]
      _ = b ^ n * (w ^ i * z ^ (j + i * n)) ^ (k + 1) := by
        rw [pow_succ']
        simp only [mul_assoc]

end Identities

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A vector fixed by `a` stays fixed by `a` after applying an element commuting with `a`. -/
theorem apply_fixed_of_commute (ρ : G →* (E ≃ₗᵢ[ℝ] E)) {a g : G} (h : Commute g a) {x : E}
    (hx : ρ a x = x) : ρ a (ρ g x) = ρ g x := by
  calc
    ρ a (ρ g x) = ρ (a * g) x := by rw [map_mul]; rfl
    _ = ρ (g * a) x := by rw [h.eq]
    _ = ρ g (ρ a x) := by rw [map_mul]; rfl
    _ = ρ g x := by rw [hx]

/-- For an `a`-fixed vector: `ρ(a) ρ(bᵐ) x = ρ(bᵐ) ρ(wᵐ z^{m(m-1)/2}) x`. -/
theorem apply_translate_sylowFour (ρ : G →* (E ≃ₗᵢ[ℝ] E)) {a b w z : G}
    (hab : a * b = b * a * w) (hwb : w * b = b * w * z) (hzw : Commute z w)
    (hzb : Commute z b) (hwa : Commute w a) (hza : Commute z a) (m : ℕ) {x : E}
    (hx : ρ a x = x) :
    ρ a (ρ (b ^ m) x) = ρ (b ^ m) (ρ (w ^ m * z ^ triangular m) x) := by
  have ht : Commute (w ^ m * z ^ triangular m) a :=
    (hwa.pow_left m).mul_left (hza.pow_left (triangular m))
  have h : a * b ^ m = b ^ m * ((w ^ m * z ^ triangular m) * a) := by
    rw [mul_pow_eq_sylowFour hab hwb hzw hzb m, ht.eq, mul_assoc]
  calc
    ρ a (ρ (b ^ m) x) = ρ (a * b ^ m) x := by rw [map_mul]; rfl
    _ = ρ (b ^ m * ((w ^ m * z ^ triangular m) * a)) x := by rw [h]
    _ = ρ (b ^ m) (ρ (w ^ m * z ^ triangular m) (ρ a x)) := by rw [map_mul, map_mul]; rfl
    _ = ρ (b ^ m) (ρ (w ^ m * z ^ triangular m) x) := by rw [hx]

/-- **The Gram sum of `U₄(p)`.** -/
theorem gram_sum_le_sylowFour (ρ : G →* (E ≃ₗᵢ[ℝ] E)) {p : ℕ} (hp0 : 0 < p) {a b w z : G}
    (hab : a * b = b * a * w) (hwb : w * b = b * w * z) (hwa : Commute w a)
    (hza : Commute z a) (hzb : Commute z b) (hzw : Commute z w) (hb : b ^ p = 1)
    (hw : w ^ p = 1) (hz : z ^ p = 1)
    (tableT : ∀ i ∈ (Finset.range p).erase 0, ∀ j ∈ (Finset.range p).erase 0, i ≠ j →
      ∃ α β : ℕ, (i * α + j * β) % p = 0 ∧ (triangular i * α + triangular j * β) % p = 1)
    (tableS : ∀ i ∈ (Finset.range p).erase 0, ∀ j ∈ (Finset.range p).erase 0, i ≠ j →
      ∃ α β : ℕ, (i * α + j * β) % p = 0 ∧
        ((triangular i + i * (p - i)) * α + (triangular j + j * (p - j)) * β) % p = 1)
    {x : E} (hxa : ρ a x = x) (hxz : ∀ g : E, ρ z g = g → inner ℝ x g = 0) :
    ∑ m ∈ (Finset.range p).erase 0, inner ℝ x (ρ (b ^ m) x) ≤ ‖x‖ ^ 2 := by
  have hppos : (0 : ℝ) < p := by exact_mod_cast hp0
  have hwz : Commute w z := hzw.symm
  -- one term
  have hterm : ∀ m ∈ (Finset.range p).erase 0,
      (p : ℝ) ^ 2 * inner ℝ x (ρ (b ^ m) x) ≤
        ‖translateSum ρ (w ^ m * z ^ (triangular m + m * (p - m))) p x‖ *
          ‖translateSum ρ (w ^ m * z ^ triangular m) p x‖ := by
    intro m hm
    have hmp : m ≤ p := (Finset.mem_range.mp (Finset.mem_of_mem_erase hm)).le
    have ht_a : Commute (w ^ m * z ^ triangular m) a :=
      (hwa.pow_left m).mul_left (hza.pow_left (triangular m))
    have hfix : ∀ k : ℕ, ρ a (ρ ((w ^ m * z ^ triangular m) ^ k) x) =
        ρ ((w ^ m * z ^ triangular m) ^ k) x := fun k ↦
      apply_fixed_of_commute ρ (ht_a.pow_left k) hxa
    have stepa : ∀ k : ℕ, inner ℝ x (ρ (b ^ m) (ρ ((w ^ m * z ^ triangular m) ^ k) x)) =
        inner ℝ x (ρ (b ^ m) x) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        calc
          inner ℝ x (ρ (b ^ m) (ρ ((w ^ m * z ^ triangular m) ^ (k + 1)) x)) =
              inner ℝ x (ρ (b ^ m) (ρ (w ^ m * z ^ triangular m)
                (ρ ((w ^ m * z ^ triangular m) ^ k) x))) := by
            rw [pow_succ', map_mul]
            rfl
          _ = inner ℝ x (ρ a (ρ (b ^ m) (ρ ((w ^ m * z ^ triangular m) ^ k) x))) := by
            rw [apply_translate_sylowFour ρ hab hwb hzw hzb hwa hza m (hfix k)]
          _ = inner ℝ (ρ a x) (ρ a (ρ (b ^ m) (ρ ((w ^ m * z ^ triangular m) ^ k) x))) := by
            rw [hxa]
          _ = inner ℝ x (ρ (b ^ m) (ρ ((w ^ m * z ^ triangular m) ^ k) x)) :=
            LinearIsometryEquiv.inner_map_map _ _ _
          _ = inner ℝ x (ρ (b ^ m) x) := ih
    have stepb : (p : ℝ) * inner ℝ x (ρ (b ^ m) x) =
        inner ℝ x (ρ (b ^ m) (translateSum ρ (w ^ m * z ^ triangular m) p x)) := by
      unfold translateSum
      rw [map_sum, inner_sum]
      simp only [stepa, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hbb : ∀ v : E, ρ (b ^ (p - m)) (ρ (b ^ m) v) = v := by
      intro v
      have h1 : b ^ (p - m) * b ^ m = 1 := by rw [← pow_add, Nat.sub_add_cancel hmp, hb]
      calc
        ρ (b ^ (p - m)) (ρ (b ^ m) v) = ρ (b ^ (p - m) * b ^ m) v := by rw [map_mul]; rfl
        _ = v := by rw [h1, map_one]; rfl
    have stepc : inner ℝ x (ρ (b ^ m) (translateSum ρ (w ^ m * z ^ triangular m) p x)) =
        inner ℝ (ρ (b ^ (p - m)) x) (translateSum ρ (w ^ m * z ^ triangular m) p x) := by
      calc
        inner ℝ x (ρ (b ^ m) (translateSum ρ (w ^ m * z ^ triangular m) p x)) =
            inner ℝ (ρ (b ^ (p - m)) x)
              (ρ (b ^ (p - m)) (ρ (b ^ m) (translateSum ρ (w ^ m * z ^ triangular m) p x))) :=
          (LinearIsometryEquiv.inner_map_map _ _ _).symm
        _ = inner ℝ (ρ (b ^ (p - m)) x) (translateSum ρ (w ^ m * z ^ triangular m) p x) := by
          rw [hbb]
    have hTfix : ρ (w ^ m * z ^ triangular m) (translateSum ρ (w ^ m * z ^ triangular m) p x) =
        translateSum ρ (w ^ m * z ^ triangular m) p x :=
      translateSum_fixed ρ (coord_pow_p hwz hw hz m _) x
    have stepd : (p : ℝ) * inner ℝ (ρ (b ^ (p - m)) x)
        (translateSum ρ (w ^ m * z ^ triangular m) p x) =
        inner ℝ (translateSum ρ (w ^ m * z ^ triangular m) p (ρ (b ^ (p - m)) x))
          (translateSum ρ (w ^ m * z ^ triangular m) p x) :=
      (inner_translateSum_of_fixed ρ _ p _ hTfix).symm
    have stepe : translateSum ρ (w ^ m * z ^ triangular m) p (ρ (b ^ (p - m)) x) =
        ρ (b ^ (p - m)) (translateSum ρ (w ^ m * z ^ (triangular m + m * (p - m))) p x) := by
      unfold translateSum
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      have h := congrArg (fun q ↦ ρ q x)
        (coord_pow_mul_pow_eq hwb hzw hzb m (triangular m) (p - m) k)
      simp only [map_mul] at h
      exact h
    have hmain : (p : ℝ) ^ 2 * inner ℝ x (ρ (b ^ m) x) =
        inner ℝ (ρ (b ^ (p - m)) (translateSum ρ (w ^ m * z ^ (triangular m + m * (p - m))) p x))
          (translateSum ρ (w ^ m * z ^ triangular m) p x) := by
      rw [← stepe, ← stepd, ← stepc, ← stepb]
      ring
    rw [hmain]
    calc
      _ ≤ ‖ρ (b ^ (p - m)) (translateSum ρ (w ^ m * z ^ (triangular m + m * (p - m))) p x)‖ *
          ‖translateSum ρ (w ^ m * z ^ triangular m) p x‖ := real_inner_le_norm _ _
      _ = ‖translateSum ρ (w ^ m * z ^ (triangular m + m * (p - m))) p x‖ *
          ‖translateSum ρ (w ^ m * z ^ triangular m) p x‖ := by
        rw [LinearIsometryEquiv.norm_map]
  -- Bessel for the two families
  have hBt : ∑ m ∈ (Finset.range p).erase 0, ‖translateSum ρ (w ^ m * z ^ triangular m) p x‖ ^ 2 ≤
      (p : ℝ) ^ 2 * ‖x‖ ^ 2 :=
    sum_norm_sq_translateSum_le ρ hp0 _ (fun m ↦ w ^ m * z ^ triangular m) z
      (fun i _ ↦ coord_pow_p hwz hw hz i _) (fun i _ j _ ↦ coord_commute hwz i _ j _)
      (fun i _ ↦ (hwz.pow_left i).mul_left ((Commute.refl z).pow_left _))
      (fun i hi j hj hij v hvi hvj ↦ by
        obtain ⟨α, β, h0, h1⟩ := tableT i hi j hj hij
        exact fixed_of_two_coordinates ρ hwz hw hz h0 h1 hvi hvj)
      hxz
  have hBs : ∑ m ∈ (Finset.range p).erase 0,
      ‖translateSum ρ (w ^ m * z ^ (triangular m + m * (p - m))) p x‖ ^ 2 ≤
        (p : ℝ) ^ 2 * ‖x‖ ^ 2 :=
    sum_norm_sq_translateSum_le ρ hp0 _ (fun m ↦ w ^ m * z ^ (triangular m + m * (p - m))) z
      (fun i _ ↦ coord_pow_p hwz hw hz i _) (fun i _ j _ ↦ coord_commute hwz i _ j _)
      (fun i _ ↦ (hwz.pow_left i).mul_left ((Commute.refl z).pow_left _))
      (fun i hi j hj hij v hvi hvj ↦ by
        obtain ⟨α, β, h0, h1⟩ := tableS i hi j hj hij
        exact fixed_of_two_coordinates ρ hwz hw hz h0 h1 hvi hvj)
      hxz
  have hsum : ∑ m ∈ (Finset.range p).erase 0, (p : ℝ) ^ 2 * inner ℝ x (ρ (b ^ m) x) ≤
      ∑ m ∈ (Finset.range p).erase 0,
        (‖translateSum ρ (w ^ m * z ^ (triangular m + m * (p - m))) p x‖ ^ 2 +
          ‖translateSum ρ (w ^ m * z ^ triangular m) p x‖ ^ 2) / 2 := by
    refine Finset.sum_le_sum fun m hm ↦ ?_
    have h := hterm m hm
    nlinarith [sq_nonneg (‖translateSum ρ (w ^ m * z ^ (triangular m + m * (p - m))) p x‖ -
      ‖translateSum ρ (w ^ m * z ^ triangular m) p x‖)]
  rw [← Finset.mul_sum, ← Finset.sum_div, Finset.sum_add_distrib] at hsum
  have hp2 : (0 : ℝ) < (p : ℝ) ^ 2 := by positivity
  have hfinal : (p : ℝ) ^ 2 * ∑ m ∈ (Finset.range p).erase 0, inner ℝ x (ρ (b ^ m) x) ≤
      (p : ℝ) ^ 2 * ‖x‖ ^ 2 := by
    linarith
  exact le_of_mul_le_mul_left hfinal hp2

end EJZAngleSylowFourGram
end GroupApproximation

#audit_axioms GroupApproximation.EJZAngleSylowFourGram.pow_mul_eq_of_commutator
#audit_axioms GroupApproximation.EJZAngleSylowFourGram.pow_mul_pow_eq_of_commutator
#audit_axioms GroupApproximation.EJZAngleSylowFourGram.mul_pow_eq_sylowFour
#audit_axioms GroupApproximation.EJZAngleSylowFourGram.coord_mul_pow_eq
#audit_axioms GroupApproximation.EJZAngleSylowFourGram.coord_pow_mul_pow_eq
#audit_axioms GroupApproximation.EJZAngleSylowFourGram.apply_fixed_of_commute
#audit_axioms GroupApproximation.EJZAngleSylowFourGram.apply_translate_sylowFour
#audit_axioms GroupApproximation.EJZAngleSylowFourGram.gram_sum_le_sylowFour
