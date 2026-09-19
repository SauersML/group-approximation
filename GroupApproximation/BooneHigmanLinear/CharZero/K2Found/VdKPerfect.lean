import GroupApproximation.BooneHigmanLinear.CharZero.K2Found.VdKCentral

/-!
# vdK 3.1–3.4: `St*(n, A)` is perfect for `n ≥ 4` (k2-poly, piece F.1)

W. van der Kallen, *Another presentation for Steinberg groups*, Indag. Math. **39** (1977),
3.1–3.4 (read at source).

* `X_commutator_eq` (3.4): if `(i, j), (v, w) ∈ U` and `w i = 0`, then
  `[X(i, j), X(v, w)] = X(i, (j v) w)`.
* `X_mem_commutator_of_two_zeros` (3.4): if `(i, w) ∈ U` and `w` has two zero coordinates, then
  `X(i, w)` lies in the commutator subgroup. The coordinates of `i` generate the unit ideal.
* `vdkPiece` (3.1–3.3): with `k i = 1`, `j = Σ_{p, q} (j_p k_q)(i_q ε_pᵀ - i_p ε_qᵀ)`. Each summand
  is killed by `i` and vanishes outside the coordinates `p, q`. (vdK sum over `p < q` with the
  symmetric coefficient `j_p k_q - j_q k_p`; the ordered double sum avoids choosing an order.)
* `stStar_perfect` (3.4): if `4 ≤ n`, `St*(n, A)` is perfect.
* `theorem1_of_elements`: with `VdKCentral`, vdK's Theorem 1 follows from the elements `X(v, w)`
  alone (vdK 3.7–3.22, still owed).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false

namespace GroupApproximation
namespace BooneHigmanLinear
namespace K2Found
namespace VdK

open scoped commutatorElement
open GroupApproximation.SteinbergGroup

variable {I A : Type*} [Fintype I] [DecidableEq I] [CommRing A]

/-- **vdK 3.4.** `[X(i, j), X(v, w)] = X(i, (j v) w)` when `w i = 0`. Conjugating by `X(v, w)`
gives `X(v, w) X(i, j) X(v, w)⁻¹ = X(i, j - (j v) w)`, and `X(i, j) = X(i, (j v) w) X(i, j - (j v) w)`
by the first relation. -/
theorem X_commutator_eq (i j v w : I → A) (h₁ : (i, j) ∈ U I A) (h₂ : (v, w) ∈ U I A)
    (hwi : w ⬝ᵥ i = 0) (h₃ : (i, (j ⬝ᵥ v) • w) ∈ U I A) :
    ⁅X (i, j) h₁, X (v, w) h₂⁆ = X (i, (j ⬝ᵥ v) • w) h₃ := by
  have hs' : (i, j - (j ⬝ᵥ v) • w) ∈ U I A := mk_mem_U.2 ⟨(mk_mem_U.1 h₁).1, by
    rw [sub_dotProduct, smul_dotProduct, hwi, smul_zero, (mk_mem_U.1 h₁).2, sub_zero]⟩
  have hs : X (v, w) h₂ * X (i, j) h₁ * (X (v, w) h₂)⁻¹ = X (i, j - (j ⬝ᵥ v) • w) hs' := by
    have hpair : conjPair (v, w) (i, j) = (i, j - (j ⬝ᵥ v) • w) := by
      show (i + (w ⬝ᵥ i) • v, j - (j ⬝ᵥ v) • w) = (i, j - (j ⬝ᵥ v) • w)
      rw [hwi, zero_smul, add_zero]
    rw [X_conj]
    exact X_congr hpair _ _
  have ht : X (i, j) h₁ = X (i, (j ⬝ᵥ v) • w) h₃ * X (i, j - (j ⬝ᵥ v) • w) hs' := by
    have hpair : ((i, j) : (I → A) × (I → A)) = (i, (j ⬝ᵥ v) • w + (j - (j ⬝ᵥ v) • w)) := by
      rw [add_sub_cancel]
    rw [X_mul i _ _ h₃ hs' (add_mem h₃ hs')]
    exact X_congr hpair _ _
  calc ⁅X (i, j) h₁, X (v, w) h₂⁆
      = X (i, j) h₁ * (X (v, w) h₂ * X (i, j) h₁ * (X (v, w) h₂)⁻¹)⁻¹ := by
        rw [commutatorElement_def]; group
    _ = X (i, j) h₁ * (X (i, j - (j ⬝ᵥ v) • w) hs')⁻¹ := by rw [hs]
    _ = X (i, (j ⬝ᵥ v) • w) h₃ := by
        rw [ht]; group

#audit_axioms X_commutator_eq

/-- **vdK 3.4.** If `(i, w) ∈ U` and `w_a = w_b = 0` with `a ≠ b`, then `X(i, w)` is in the
commutator subgroup of `St*(n, A)`. For every row `j` with `j i = 0`, `X(i, j_a w)` is the
commutator `[X(i, j), X(ε_a, w)]`, and similarly at `b`. The rows `ε_a - i_a k` and
`k_a (i_a ε_b - i_b ε_a)` (with `k i = 1`) have `a`-th and `b`-th coordinates summing to `1`. -/
theorem X_mem_commutator_of_two_zeros {i w : I → A} (hw : (i, w) ∈ U I A) {a b : I}
    (hab : a ≠ b) (ha : w a = 0) (hb : w b = 0) :
    X (i, w) hw ∈ _root_.commutator (StStar I A) := by
  obtain ⟨⟨k, hk⟩, hwi⟩ := mk_mem_U.1 hw
  have key : ∀ (c : I), w c = 0 → ∀ (j : I → A), j ⬝ᵥ i = 0 → ∀ (h' : (i, j c • w) ∈ U I A),
      X (i, j c • w) h' ∈ _root_.commutator (StStar I A) := by
    intro c hc j hj h'
    have h₁ : (i, j) ∈ U I A := mk_mem_U.2 ⟨⟨k, hk⟩, hj⟩
    have h₂ : (Pi.single c (1 : A), w) ∈ U I A :=
      mk_mem_U.2 ⟨⟨Pi.single c 1, by rw [single_dotProduct, Pi.single_eq_same, mul_one]⟩,
        by rw [dotProduct_single, hc, mul_one]⟩
    have hjc : j ⬝ᵥ Pi.single c (1 : A) = j c := by rw [dotProduct_single, mul_one]
    have h₃ : (i, (j ⬝ᵥ Pi.single c (1 : A)) • w) ∈ U I A := by rw [hjc]; exact h'
    have hcomm := X_commutator_eq i j (Pi.single c 1) w h₁ h₂ hwi h₃
    rw [X_congr (show (i, (j ⬝ᵥ Pi.single c (1 : A)) • w) = (i, j c • w) by rw [hjc]) h₃ h']
      at hcomm
    rw [← hcomm, _root_.commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  obtain ⟨j, hj, hja⟩ : ∃ j : I → A, j ⬝ᵥ i = 0 ∧ j a = 1 - i a * k a := by
    refine ⟨Pi.single a (1 : A) - i a • k, ?_, ?_⟩
    · rw [sub_dotProduct, smul_dotProduct, single_dotProduct, hk, one_mul, smul_eq_mul,
        mul_one, sub_self]
    · simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul]
  obtain ⟨j', hj', hjb⟩ : ∃ j' : I → A, j' ⬝ᵥ i = 0 ∧ j' b = k a * i a := by
    refine ⟨k a • (i a • Pi.single b (1 : A) - i b • Pi.single a (1 : A)), ?_, ?_⟩
    · simp only [smul_dotProduct, sub_dotProduct, single_dotProduct, one_mul, smul_eq_mul]
      ring
    · simp only [Pi.smul_apply, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hab.symm,
        smul_eq_mul, mul_zero, sub_zero, mul_one]
  have h₁ : (i, j a • w) ∈ U I A :=
    mk_mem_U.2 ⟨⟨k, hk⟩, by rw [smul_dotProduct, hwi, smul_zero]⟩
  have h₂ : (i, j' b • w) ∈ U I A :=
    mk_mem_U.2 ⟨⟨k, hk⟩, by rw [smul_dotProduct, hwi, smul_zero]⟩
  have hsplit : j a • w + j' b • w = w := by
    rw [hja, hjb, ← add_smul, show (1 - i a * k a + k a * i a : A) = 1 by ring, one_smul]
  have hprod := X_mul i (j a • w) (j' b • w) h₁ h₂ (add_mem h₁ h₂)
  rw [X_congr (show (i, j a • w + j' b • w) = (i, w) by rw [hsplit]) (add_mem h₁ h₂) hw]
    at hprod
  rw [← hprod]
  exact mul_mem (key a ha j hj h₁) (key b hb j' hj' h₂)

#audit_axioms X_mem_commutator_of_two_zeros

/-! ### vdK 3.1–3.3: the decomposition of a row into rows with many zeros -/

/-- `(j_p k_q)(i_q ε_pᵀ - i_p ε_qᵀ)`, the `(p, q)` summand of vdK 3.1 (ordered-pair form). -/
def vdkPiece (i j k : I → A) (p q : I) : I → A :=
  (j p * k q) • (i q • Pi.single p (1 : A) - i p • Pi.single q (1 : A))

theorem vdkPiece_dotProduct (i j k : I → A) (p q : I) : vdkPiece i j k p q ⬝ᵥ i = 0 := by
  simp only [vdkPiece, smul_dotProduct, sub_dotProduct, single_dotProduct, one_mul, smul_eq_mul]
  ring

theorem vdkPiece_apply (i j k : I → A) (p q r : I) :
    vdkPiece i j k p q r =
      j p * k q * i q * (Pi.single p (1 : A) : I → A) r - j p * k q * i p * (Pi.single q (1 : A) : I → A) r := by
  simp only [vdkPiece, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

theorem vdkPiece_apply_of_ne (i j k : I → A) {p q r : I} (hp : r ≠ p) (hq : r ≠ q) :
    vdkPiece i j k p q r = 0 := by
  rw [vdkPiece_apply, Pi.single_eq_of_ne hp, Pi.single_eq_of_ne hq, mul_zero, mul_zero, sub_zero]

/-- **vdK 3.2–3.3.** If `j i = 0` and `k i = 1`, then `j = Σ_p Σ_q vdkPiece i j k p q`. -/
theorem sum_vdkPiece {i j k : I → A} (hji : j ⬝ᵥ i = 0) (hk : k ⬝ᵥ i = 1) :
    ∑ p, ∑ q, vdkPiece i j k p q = j := by
  ext r
  simp only [Finset.sum_apply, vdkPiece_apply, Finset.sum_sub_distrib]
  have hk' : ∑ q, k q * i q = 1 := hk
  have hji' : ∑ p, j p * i p = 0 := hji
  have h1 : ∑ p, ∑ q, j p * k q * i q * (Pi.single p (1 : A) : I → A) r = j r := by
    have hin : ∀ p, ∑ q, j p * k q * i q * (Pi.single p (1 : A) : I → A) r = j p * (Pi.single p (1 : A) : I → A) r := by
      intro p
      calc ∑ q, j p * k q * i q * (Pi.single p (1 : A) : I → A) r
          = (∑ q, k q * i q) * (j p * (Pi.single p (1 : A) : I → A) r) := by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl (fun q _ => by ring)
        _ = j p * (Pi.single p (1 : A) : I → A) r := by rw [hk', one_mul]
    rw [Finset.sum_congr rfl (fun p _ => hin p), Finset.sum_eq_single r, Pi.single_eq_same, mul_one]
    · intro p _ hp
      rw [Pi.single_eq_of_ne (Ne.symm hp), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ r) h
  have h2 : ∑ p, ∑ q, j p * k q * i p * (Pi.single q (1 : A) : I → A) r = 0 := by
    have hin : ∀ p, ∑ q, j p * k q * i p * (Pi.single q (1 : A) : I → A) r = k r * (j p * i p) := by
      intro p
      rw [Finset.sum_eq_single r, Pi.single_eq_same, mul_one]
      · ring
      · intro q _ hq
        rw [Pi.single_eq_of_ne (Ne.symm hq), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ r) h
    rw [Finset.sum_congr rfl (fun p _ => hin p), ← Finset.mul_sum, hji', mul_zero]
  rw [h1, h2, sub_zero]

#audit_axioms sum_vdkPiece

/-- `u` is killed by `i`, and every `X(i, u)` lies in the commutator subgroup. -/
def GoodRow (i u : I → A) : Prop :=
  u ⬝ᵥ i = 0 ∧ ∀ hu : (i, u) ∈ U I A, X (i, u) hu ∈ _root_.commutator (StStar I A)

theorem goodRow_zero (i : I → A) : GoodRow i (0 : I → A) :=
  ⟨by rw [zero_dotProduct], fun hu => by rw [X_zero]; exact one_mem _⟩

theorem goodRow_add {i u u' : I → A} (hu : GoodRow i u) (hu' : GoodRow i u') :
    GoodRow i (u + u') := by
  refine ⟨by rw [add_dotProduct, hu.1, hu'.1, add_zero], fun h => ?_⟩
  have h₁ : (i, u) ∈ U I A := mk_mem_U.2 ⟨(mk_mem_U.1 h).1, hu.1⟩
  have h₂ : (i, u') ∈ U I A := mk_mem_U.2 ⟨(mk_mem_U.1 h).1, hu'.1⟩
  rw [← X_mul i u u' h₁ h₂ h]
  exact mul_mem (hu.2 h₁) (hu'.2 h₂)

/-- In a type with at least four elements, any two elements `p, q` leave two further elements. -/
theorem exists_two_ne_of_four_le (h4 : 4 ≤ Fintype.card I) (p q : I) :
    ∃ a b : I, a ≠ b ∧ a ≠ p ∧ a ≠ q ∧ b ≠ p ∧ b ≠ q := by
  have hcard : 1 < ((Finset.univ : Finset I) \ {p, q}).card := by
    rw [Finset.card_univ_sdiff]
    have := Finset.card_le_two (a := p) (b := q)
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hcard
  simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_and,
    not_or] at ha hb
  exact ⟨a, b, hab, ha.1, ha.2, hb.1, hb.2⟩

theorem goodRow_vdkPiece (h4 : 4 ≤ Fintype.card I) (i j k : I → A) (p q : I) :
    GoodRow i (vdkPiece i j k p q) := by
  refine ⟨vdkPiece_dotProduct i j k p q, fun hu => ?_⟩
  obtain ⟨a, b, hab, hap, haq, hbp, hbq⟩ := exists_two_ne_of_four_le h4 p q
  exact X_mem_commutator_of_two_zeros hu hab (vdkPiece_apply_of_ne i j k hap haq)
    (vdkPiece_apply_of_ne i j k hbp hbq)

/-- **vdK 3.3–3.4.** For `n ≥ 4`, every generator `X(i, j)` lies in the commutator subgroup. -/
theorem X_mem_commutator (h4 : 4 ≤ Fintype.card I) (q : (I → A) × (I → A)) (hq : q ∈ U I A) :
    X q hq ∈ _root_.commutator (StStar I A) := by
  obtain ⟨i, j⟩ := q
  obtain ⟨⟨k, hk⟩, hji⟩ := mk_mem_U.1 hq
  have hgood : GoodRow i (∑ p, ∑ q, vdkPiece i j k p q) :=
    Finset.sum_induction _ (GoodRow i) (fun _ _ => goodRow_add) (goodRow_zero i)
      (fun p _ => Finset.sum_induction _ (GoodRow i) (fun _ _ => goodRow_add) (goodRow_zero i)
        (fun q _ => goodRow_vdkPiece h4 i j k p q))
  rw [sum_vdkPiece hji hk] at hgood
  exact hgood.2 hq

#audit_axioms X_mem_commutator

/-- **vdK Lemma 3.4.** For `n ≥ 4`, `St*(n, A)` is perfect. -/
theorem stStar_perfect (h4 : 4 ≤ Fintype.card I) : _root_.commutator (StStar I A) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  exact PresentedGroup.generated_by _ _ (fun g => X_mem_commutator h4 g.1 g.2) x

#audit_axioms stStar_perfect

/-- **vdK's Theorem 1 from the elements `X(v, w)` alone.** For `n ≥ 4`, if elements
`X(v, w) ∈ St(n, A)` meeting vdK's requirements 3.6 (a)–(d) exist, then `φ : St(n, A) → St*(n, A)`
is an isomorphism. The elements are vdK 3.7–3.22. -/
theorem theorem1_of_elements (h4 : 4 ≤ Fintype.card I) (E : Elements I A) : Theorem1At I A :=
  theorem1_of_perfect_of_elements (stStar_perfect h4) E

#audit_axioms theorem1_of_elements

end VdK
end K2Found
end BooneHigmanLinear
end GroupApproximation
