import GroupApproximation.Sofic.Asymptotics
import GroupApproximation.Sofic.Sofic
import GroupApproximation.Sofic.SoficTransfer
import GroupApproximation.Sofic.InfranormalCompressionPair

/-!
# Sequential centralizer normalization and its generation step

Kun--Thom's Theorem 4.1 (arXiv:2608.06222) says: if `Γ ≤ G` is infranormal and
both groups have property `(T)`, then every sofic representation `σ` of `G`
normalizes the permutation centralizer of `σ(Γ)`.  This module fixes the
sequential form of that statement consumed by the Bowen--Chapman endpoint, and
proves the algebraic half of it.

`HasSequentialCentralizerNormalization Γ` quantifies over sofic approximations
`A` of `G`.  These are free: `SoficApproximation.asymptoticallyFaithful` sends
the normalized Hamming distance from `A(g)` to the identity to one for every
`g ≠ 1`, which is the trace-zero condition of a sofic representation.  It also
quantifies over sequences `v` of model permutations that almost commute with
`A(γ)` for every `γ ∈ Γ`, meaning that the normalized Hamming distance between
`v n * A(γ)` and `A(γ) * v n` tends to zero along `Filter.atTop`.  The
conclusion is the same almost-commutation for `A(g) v A(g)⁻¹`, for every
`g ∈ G`.

The generation step reduces the statement to compressors.  For a compressor
`t`, meaning `t γ t⁻¹ ∈ Γ` for all `γ ∈ Γ`, the inverse direction
`A(t)⁻¹ v A(t)` is automatic (`seqNormalizes_inv_of_mem_compressionSubmonoid`).
The elements for which both directions hold form a subgroup
(`seqNormalizerSubgroup`).  Consequently, once every compressor satisfies the
forward direction, infranormality spreads normalization to the whole group
(`hasSequentialCentralizerNormalization_of_compressorNormalization`).  The
forward direction for compressors, `HasSequentialCompressorNormalization`, is
the analytic content of Theorem 4.1.

The module also collects the elementary Hamming estimates that turn group
relations into vanishing model defects, in the form used by the free-lamp,
double and wreath consumers.
-/

namespace GroupApproximation

namespace SequentialNormalization

variable {Y : FiniteModel}

/-- Products of close permutations are close. -/
theorem hammingDistance_mul_mul_le (p₁ p₂ q₁ q₂ : Equiv.Perm Y) :
    hammingDistance Y (p₁ * q₁) (p₂ * q₂) ≤
      hammingDistance Y p₁ p₂ + hammingDistance Y q₁ q₂ := by
  have h₁ := hammingDistance_triangle Y (p₁ * q₁) (p₁ * q₂) (p₂ * q₂)
  have e₁ : hammingDistance Y (p₁ * q₁) (p₁ * q₂) = hammingDistance Y q₁ q₂ :=
    hammingDistance_left_invariant Y p₁ q₁ q₂
  have e₂ : hammingDistance Y (p₁ * q₂) (p₂ * q₂) = hammingDistance Y p₁ p₂ :=
    hammingDistance_right_invariant Y p₁ p₂ q₂
  linarith

/-- Inversion preserves the normalized Hamming distance. -/
theorem hammingDistance_inv_inv (p q : Equiv.Perm Y) :
    hammingDistance Y p⁻¹ q⁻¹ = hammingDistance Y p q := by
  have e₁ : hammingDistance Y (q * p⁻¹) (q * q⁻¹) = hammingDistance Y p⁻¹ q⁻¹ :=
    hammingDistance_left_invariant Y q p⁻¹ q⁻¹
  have e₂ : hammingDistance Y (q * p⁻¹ * p) (q * q⁻¹ * p) =
      hammingDistance Y (q * p⁻¹) (q * q⁻¹) :=
    hammingDistance_right_invariant Y (q * p⁻¹) (q * q⁻¹) p
  have e₃ : q * p⁻¹ * p = q := by group
  have e₄ : q * q⁻¹ * p = p := by group
  rw [e₃, e₄] at e₂
  rw [← e₁, ← e₂]
  exact hammingDistance_comm Y q p

/-- Conjugating by close permutations changes the result by at most twice their
distance. -/
theorem hammingDistance_conj_le (a b v w : Equiv.Perm Y) :
    hammingDistance Y (a * v * a⁻¹) (b * w * b⁻¹) ≤
      2 * hammingDistance Y a b + hammingDistance Y v w := by
  have h₁ := hammingDistance_mul_mul_le (a * v) (b * w) a⁻¹ b⁻¹
  have h₂ := hammingDistance_mul_mul_le a b v w
  have e : hammingDistance Y a⁻¹ b⁻¹ = hammingDistance Y a b :=
    hammingDistance_inv_inv a b
  linarith

/-- The commutator defect with a fixed permutation moves by at most twice the
distance of the varying factor. -/
theorem hammingDistance_commutator_le (v w p : Equiv.Perm Y) :
    hammingDistance Y (w * p) (p * w) ≤
      hammingDistance Y (v * p) (p * v) + 2 * hammingDistance Y v w := by
  have h₁ := hammingDistance_triangle Y (w * p) (v * p) (p * w)
  have h₂ := hammingDistance_triangle Y (v * p) (p * v) (p * w)
  have e₁ : hammingDistance Y (w * p) (v * p) = hammingDistance Y w v :=
    hammingDistance_right_invariant Y w v p
  have e₂ : hammingDistance Y w v = hammingDistance Y v w :=
    hammingDistance_comm Y w v
  have e₃ : hammingDistance Y (p * v) (p * w) = hammingDistance Y v w :=
    hammingDistance_left_invariant Y p v w
  linarith

/-- The commutator defect of a fixed permutation moves by at most twice the
distance of the other factor. -/
theorem hammingDistance_commutator_le_right (v c c' : Equiv.Perm Y) :
    hammingDistance Y (v * c) (c * v) ≤
      hammingDistance Y (v * c') (c' * v) + 2 * hammingDistance Y c c' := by
  have h₁ := hammingDistance_triangle Y (v * c) (v * c') (c * v)
  have h₂ := hammingDistance_triangle Y (v * c') (c' * v) (c * v)
  have e₁ : hammingDistance Y (v * c) (v * c') = hammingDistance Y c c' :=
    hammingDistance_left_invariant Y v c c'
  have e₂ : hammingDistance Y (c' * v) (c * v) = hammingDistance Y c' c :=
    hammingDistance_right_invariant Y c' c v
  have e₃ : hammingDistance Y c' c = hammingDistance Y c c' :=
    hammingDistance_comm Y c' c
  linarith

/-- Eventual smallness of a nonnegative sequence is vanishing. -/
theorem vanishing_of_eventually_lt {a : ℕ → ℝ} (hnonneg : ∀ n, 0 ≤ a n)
    (h : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, a n < ε) : Vanishing a := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [abs_of_nonneg (hnonneg n)]
  exact hN n hn

end SequentialNormalization

namespace SoficApproximation

variable {G : Type} [Group G]

/-- A sequence of model permutations almost commutes with the model permutation
of `g`: the normalized Hamming distance between `v n * A(g)` and `A(g) * v n`
tends to zero along `Filter.atTop`. -/
def AlmostCommutes (A : SoficApproximation G) (v : ∀ n, Equiv.Perm (A.model n))
    (g : G) : Prop :=
  Vanishing fun n ↦ hammingDistance (A.model n) (v n * A.map n g) (A.map n g * v n)

/-- The conjugated sequence `A(g) v A(g)⁻¹`. -/
def conjSeq (A : SoficApproximation G) (g : G) (v : ∀ n, Equiv.Perm (A.model n)) :
    ∀ n, Equiv.Perm (A.model n) :=
  fun n ↦ A.map n g * v n * (A.map n g)⁻¹

variable (A : SoficApproximation G)

/-- The multiplication defect of a sofic approximation vanishes. -/
theorem hamming_mul_vanishing (g h : G) :
    Vanishing fun n ↦
      hammingDistance (A.model n) (A.map n (g * h)) (A.map n g * A.map n h) :=
  SequentialNormalization.vanishing_of_eventually_lt
    (fun _ ↦ hammingDistance_nonnegative _ _ _)
    (A.asymptoticallyMultiplicative g h)

/-- The model permutation of the identity approaches the identity. -/
theorem hamming_one_vanishing :
    Vanishing fun n ↦ hammingDistance (A.model n) (A.map n 1) 1 :=
  SequentialNormalization.vanishing_of_eventually_lt
    (fun _ ↦ hammingDistance_nonnegative _ _ _) A.map_one_close

/-- The model permutation of an inverse approaches the inverse permutation. -/
theorem hamming_inv_vanishing (g : G) :
    Vanishing fun n ↦
      hammingDistance (A.model n) (A.map n g⁻¹) (A.map n g)⁻¹ := by
  refine Vanishing.squeeze (fun _ ↦ hammingDistance_nonnegative _ _ _) (fun n ↦ ?_)
    ((A.hamming_mul_vanishing g g⁻¹).add A.hamming_one_vanishing)
  show hammingDistance (A.model n) (A.map n g⁻¹) (A.map n g)⁻¹ ≤
    hammingDistance (A.model n) (A.map n (g * g⁻¹)) (A.map n g * A.map n g⁻¹) +
      hammingDistance (A.model n) (A.map n 1) 1
  have e₁ : hammingDistance (A.model n) (A.map n g * A.map n g⁻¹)
      (A.map n g * (A.map n g)⁻¹) =
      hammingDistance (A.model n) (A.map n g⁻¹) (A.map n g)⁻¹ :=
    hammingDistance_left_invariant _ _ _ _
  have e₂ : A.map n g * (A.map n g)⁻¹ = 1 := mul_inv_cancel _
  rw [e₂] at e₁
  have h₁ := hammingDistance_triangle (A.model n) (A.map n g * A.map n g⁻¹)
    (A.map n (g * g⁻¹)) 1
  have e₃ : hammingDistance (A.model n) (A.map n g * A.map n g⁻¹) (A.map n (g * g⁻¹)) =
      hammingDistance (A.model n) (A.map n (g * g⁻¹)) (A.map n g * A.map n g⁻¹) :=
    hammingDistance_comm _ _ _
  have e₄ : hammingDistance (A.model n) (A.map n (g * g⁻¹)) 1 =
      hammingDistance (A.model n) (A.map n 1) 1 := by
    rw [mul_inv_cancel]
  linarith

/-- Commuting group elements have asymptotically commuting model permutations. -/
theorem hamming_commute_vanishing {a b : G} (hab : Commute a b) :
    Vanishing fun n ↦
      hammingDistance (A.model n) (A.map n a * A.map n b) (A.map n b * A.map n a) := by
  refine Vanishing.squeeze (fun _ ↦ hammingDistance_nonnegative _ _ _) (fun n ↦ ?_)
    ((A.hamming_mul_vanishing a b).add (A.hamming_mul_vanishing b a))
  show hammingDistance (A.model n) (A.map n a * A.map n b) (A.map n b * A.map n a) ≤
    hammingDistance (A.model n) (A.map n (a * b)) (A.map n a * A.map n b) +
      hammingDistance (A.model n) (A.map n (b * a)) (A.map n b * A.map n a)
  have h₁ := hammingDistance_triangle (A.model n) (A.map n a * A.map n b)
    (A.map n (a * b)) (A.map n b * A.map n a)
  have e₁ : hammingDistance (A.model n) (A.map n a * A.map n b) (A.map n (a * b)) =
      hammingDistance (A.model n) (A.map n (a * b)) (A.map n a * A.map n b) :=
    hammingDistance_comm _ _ _
  have e₂ : hammingDistance (A.model n) (A.map n (a * b)) (A.map n b * A.map n a) =
      hammingDistance (A.model n) (A.map n (b * a)) (A.map n b * A.map n a) := by
    rw [hab.eq]
  linarith

/-- The model permutation of a conjugate approaches the conjugate of the model
permutations. -/
theorem hamming_conj_vanishing (x y : G) :
    Vanishing fun n ↦ hammingDistance (A.model n) (A.map n (x * y * x⁻¹))
      (A.map n x * A.map n y * (A.map n x)⁻¹) := by
  refine Vanishing.squeeze (fun _ ↦ hammingDistance_nonnegative _ _ _) (fun n ↦ ?_)
    (((A.hamming_mul_vanishing (x * y) x⁻¹).add (A.hamming_mul_vanishing x y)).add
      (A.hamming_inv_vanishing x))
  show hammingDistance (A.model n) (A.map n (x * y * x⁻¹))
      (A.map n x * A.map n y * (A.map n x)⁻¹) ≤
    hammingDistance (A.model n) (A.map n (x * y * x⁻¹)) (A.map n (x * y) * A.map n x⁻¹) +
      hammingDistance (A.model n) (A.map n (x * y)) (A.map n x * A.map n y) +
      hammingDistance (A.model n) (A.map n x⁻¹) (A.map n x)⁻¹
  have h₁ := hammingDistance_triangle (A.model n) (A.map n (x * y * x⁻¹))
    (A.map n (x * y) * A.map n x⁻¹) (A.map n x * A.map n y * (A.map n x)⁻¹)
  have h₂ := hammingDistance_triangle (A.model n) (A.map n (x * y) * A.map n x⁻¹)
    (A.map n x * A.map n y * A.map n x⁻¹) (A.map n x * A.map n y * (A.map n x)⁻¹)
  have e₁ : hammingDistance (A.model n) (A.map n (x * y) * A.map n x⁻¹)
      (A.map n x * A.map n y * A.map n x⁻¹) =
      hammingDistance (A.model n) (A.map n (x * y)) (A.map n x * A.map n y) :=
    hammingDistance_right_invariant _ _ _ _
  have e₂ : hammingDistance (A.model n) (A.map n x * A.map n y * A.map n x⁻¹)
      (A.map n x * A.map n y * (A.map n x)⁻¹) =
      hammingDistance (A.model n) (A.map n x⁻¹) (A.map n x)⁻¹ :=
    hammingDistance_left_invariant _ _ _ _
  linarith

/-- **Generic commutator step.**  If the conjugate of the model of `y` by the
model of `x` almost commutes with the model of `z`, then the models of the two
group elements `x y x⁻¹ z` and `z x y x⁻¹` approach each other.  Combined with
`not_hamming_vanishing_of_ne` this forces `x y x⁻¹` to commute with `z`. -/
theorem hamming_conj_commute_vanishing (x y z : G)
    (hconj : Vanishing fun n ↦ hammingDistance (A.model n)
      (A.map n x * A.map n y * (A.map n x)⁻¹ * A.map n z)
      (A.map n z * (A.map n x * A.map n y * (A.map n x)⁻¹))) :
    Vanishing fun n ↦ hammingDistance (A.model n)
      (A.map n (x * y * x⁻¹ * z)) (A.map n (z * (x * y * x⁻¹))) := by
  refine Vanishing.squeeze (fun _ ↦ hammingDistance_nonnegative _ _ _) (fun n ↦ ?_)
    (((((A.hamming_mul_vanishing (x * y * x⁻¹) z).add (A.hamming_conj_vanishing x y)).add
      hconj).add (A.hamming_conj_vanishing x y)).add
      (A.hamming_mul_vanishing z (x * y * x⁻¹)))
  show hammingDistance (A.model n) (A.map n (x * y * x⁻¹ * z)) (A.map n (z * (x * y * x⁻¹))) ≤
    hammingDistance (A.model n) (A.map n (x * y * x⁻¹ * z))
        (A.map n (x * y * x⁻¹) * A.map n z) +
      hammingDistance (A.model n) (A.map n (x * y * x⁻¹))
        (A.map n x * A.map n y * (A.map n x)⁻¹) +
      hammingDistance (A.model n) (A.map n x * A.map n y * (A.map n x)⁻¹ * A.map n z)
        (A.map n z * (A.map n x * A.map n y * (A.map n x)⁻¹)) +
      hammingDistance (A.model n) (A.map n (x * y * x⁻¹))
        (A.map n x * A.map n y * (A.map n x)⁻¹) +
      hammingDistance (A.model n) (A.map n (z * (x * y * x⁻¹)))
        (A.map n z * A.map n (x * y * x⁻¹))
  have h₁ := hammingDistance_triangle (A.model n) (A.map n (x * y * x⁻¹ * z))
    (A.map n (x * y * x⁻¹) * A.map n z) (A.map n (z * (x * y * x⁻¹)))
  have h₂ := hammingDistance_triangle (A.model n) (A.map n (x * y * x⁻¹) * A.map n z)
    (A.map n x * A.map n y * (A.map n x)⁻¹ * A.map n z) (A.map n (z * (x * y * x⁻¹)))
  have h₃ := hammingDistance_triangle (A.model n)
    (A.map n x * A.map n y * (A.map n x)⁻¹ * A.map n z)
    (A.map n z * (A.map n x * A.map n y * (A.map n x)⁻¹)) (A.map n (z * (x * y * x⁻¹)))
  have h₄ := hammingDistance_triangle (A.model n)
    (A.map n z * (A.map n x * A.map n y * (A.map n x)⁻¹))
    (A.map n z * A.map n (x * y * x⁻¹)) (A.map n (z * (x * y * x⁻¹)))
  have e₁ : hammingDistance (A.model n) (A.map n (x * y * x⁻¹) * A.map n z)
      (A.map n x * A.map n y * (A.map n x)⁻¹ * A.map n z) =
      hammingDistance (A.model n) (A.map n (x * y * x⁻¹))
        (A.map n x * A.map n y * (A.map n x)⁻¹) :=
    hammingDistance_right_invariant _ _ _ _
  have e₂ : hammingDistance (A.model n) (A.map n z * (A.map n x * A.map n y * (A.map n x)⁻¹))
      (A.map n z * A.map n (x * y * x⁻¹)) =
      hammingDistance (A.model n) (A.map n x * A.map n y * (A.map n x)⁻¹)
        (A.map n (x * y * x⁻¹)) :=
    hammingDistance_left_invariant _ _ _ _
  have e₃ : hammingDistance (A.model n) (A.map n x * A.map n y * (A.map n x)⁻¹)
      (A.map n (x * y * x⁻¹)) =
      hammingDistance (A.model n) (A.map n (x * y * x⁻¹))
        (A.map n x * A.map n y * (A.map n x)⁻¹) :=
    hammingDistance_comm _ _ _
  have e₄ : hammingDistance (A.model n) (A.map n z * A.map n (x * y * x⁻¹))
      (A.map n (z * (x * y * x⁻¹))) =
      hammingDistance (A.model n) (A.map n (z * (x * y * x⁻¹)))
        (A.map n z * A.map n (x * y * x⁻¹)) :=
    hammingDistance_comm _ _ _
  linarith

/-- Distinct group elements cannot have asymptotically equal model
permutations. -/
theorem not_hamming_vanishing_of_ne {g h : G} (hgh : g ≠ h) :
    ¬ Vanishing fun n ↦ hammingDistance (A.model n) (A.map n g) (A.map n h) := by
  intro hvan
  obtain ⟨N₁, hN₁⟩ := A.pair_separated_eventually hgh (1 / 2) (by norm_num)
  obtain ⟨N₂, hN₂⟩ := hvan (1 / 2) (by norm_num)
  have h₁ := hN₁ (max N₁ N₂) (le_max_left _ _)
  have h₂ := lt_of_abs_lt (hN₂ (max N₁ N₂) (le_max_right _ _))
  linarith

/-- Almost commutation survives replacing the sequence by a close one. -/
theorem almostCommutes_of_close {v w : ∀ n, Equiv.Perm (A.model n)} {g : G}
    (hv : A.AlmostCommutes v g)
    (hvw : Vanishing fun n ↦ hammingDistance (A.model n) (v n) (w n)) :
    A.AlmostCommutes w g := by
  unfold AlmostCommutes at hv ⊢
  exact Vanishing.squeeze (fun _ ↦ hammingDistance_nonnegative _ _ _)
    (fun n ↦ SequentialNormalization.hammingDistance_commutator_le (v n) (w n) (A.map n g))
    (hv.add (hvw.const_mul 2))

/-- Conjugating close sequences by close sequences gives close sequences. -/
theorem hamming_conj_close {a b v w : ∀ n, Equiv.Perm (A.model n)}
    (hab : Vanishing fun n ↦ hammingDistance (A.model n) (a n) (b n))
    (hvw : Vanishing fun n ↦ hammingDistance (A.model n) (v n) (w n)) :
    Vanishing fun n ↦
      hammingDistance (A.model n) (a n * v n * (a n)⁻¹) (b n * w n * (b n)⁻¹) :=
  Vanishing.squeeze (fun _ ↦ hammingDistance_nonnegative _ _ _)
    (fun n ↦ SequentialNormalization.hammingDistance_conj_le (a n) (b n) (v n) (w n))
    ((hab.const_mul 2).add hvw)

/-- A sequence of model permutations of an ambient element commuting with the
image of `δ` almost commutes with `δ` in the restricted approximation. -/
theorem almostCommutes_comap_of_commute {H : Type} [Group H] (S : SoficApproximation H)
    (f : G →* H) (hf : Function.Injective f) {k : H} {δ : G} (hcomm : Commute k (f δ)) :
    (S.comap f hf).AlmostCommutes (fun n ↦ S.map n k) δ :=
  S.hamming_commute_vanishing hcomm

end SoficApproximation

variable {G : Type} [Group G]

/-- `g` carries sequential almost-centralizers of `Γ` to almost-centralizers of
`Γ`, in every sofic approximation of `G`. -/
def SeqNormalizes (Γ : Subgroup G) (g : G) : Prop :=
  ∀ (A : SoficApproximation G) (v : ∀ n, Equiv.Perm (A.model n)),
    (∀ γ ∈ Γ, A.AlmostCommutes v γ) → ∀ γ ∈ Γ, A.AlmostCommutes (A.conjSeq g v) γ

/-- **Kun--Thom Theorem 4.1, sequential form.**  For every sofic approximation
`A` of `G` and every sequence `v` of model permutations whose commutator with
`A(γ)` vanishes in normalized Hamming distance along `Filter.atTop` for each
`γ ∈ Γ`, the conjugated sequence `A(g) v A(g)⁻¹` has the same property, for every
`g ∈ G`.  Spelled out, the conclusion is

`Vanishing fun n ↦ hammingDistance (A.model n)
  (A.map n g * v n * (A.map n g)⁻¹ * A.map n γ)
  (A.map n γ * (A.map n g * v n * (A.map n g)⁻¹))`. -/
def HasSequentialCentralizerNormalization (Γ : Subgroup G) : Prop :=
  ∀ (A : SoficApproximation G) (v : ∀ n, Equiv.Perm (A.model n)),
    (∀ γ ∈ Γ, A.AlmostCommutes v γ) →
    ∀ g γ : G, γ ∈ Γ → A.AlmostCommutes (A.conjSeq g v) γ

/-- The forward inclusion for compressors: the analytic content of Kun--Thom
Theorem 4.1. -/
def HasSequentialCompressorNormalization (Γ : Subgroup G) : Prop :=
  ∀ t ∈ compressionSubmonoid Γ, SeqNormalizes Γ t

theorem hasSequentialCentralizerNormalization_iff {Γ : Subgroup G} :
    HasSequentialCentralizerNormalization Γ ↔ ∀ g : G, SeqNormalizes Γ g :=
  ⟨fun h g A v hv γ hγ ↦ h A v hv g γ hγ, fun h A v hv g γ hγ ↦ h g A v hv γ hγ⟩

/-- The identity normalizes, up to the identity defect of the approximation. -/
theorem seqNormalizes_one (Γ : Subgroup G) : SeqNormalizes Γ 1 := by
  intro A v hv γ hγ
  apply A.almostCommutes_of_close (hv γ hγ)
  have hclose := A.hamming_conj_close
    (a := fun n ↦ (1 : Equiv.Perm (A.model n))) (b := fun n ↦ A.map n 1)
    (v := v) (w := v)
    (A.hamming_one_vanishing.congr fun _ ↦ hammingDistance_comm _ _ _)
    (Vanishing.zero.congr fun _ ↦ (hammingDistance_self _ _).symm)
  refine hclose.congr fun n ↦ ?_
  simp only [SoficApproximation.conjSeq, one_mul, inv_one, mul_one]

/-- Normalizing elements are closed under multiplication. -/
theorem seqNormalizes_mul {Γ : Subgroup G} {g h : G}
    (hg : SeqNormalizes Γ g) (hh : SeqNormalizes Γ h) : SeqNormalizes Γ (g * h) := by
  intro A v hv γ hγ
  have hw := hg A (A.conjSeq h v) (hh A v hv) γ hγ
  apply A.almostCommutes_of_close hw
  have hclose := A.hamming_conj_close
    (a := fun n ↦ A.map n g * A.map n h) (b := fun n ↦ A.map n (g * h))
    (v := v) (w := v)
    ((A.hamming_mul_vanishing g h).congr fun _ ↦ hammingDistance_comm _ _ _)
    (Vanishing.zero.congr fun _ ↦ (hammingDistance_self _ _).symm)
  refine hclose.congr fun n ↦ ?_
  simp only [SoficApproximation.conjSeq, mul_inv_rev, mul_assoc]

/-- **The automatic direction.**  The inverse of a compressor normalizes: for
`t γ t⁻¹ ∈ Γ`, the sequence `A(t⁻¹) v A(t⁻¹)⁻¹` almost commutes with `A(γ)`
because `v` almost commutes with `A(t γ t⁻¹)`. -/
theorem seqNormalizes_inv_of_mem_compressionSubmonoid {Γ : Subgroup G} {t : G}
    (ht : t ∈ compressionSubmonoid Γ) : SeqNormalizes Γ t⁻¹ := by
  intro A v hv γ hγ
  have hcomp : t * γ * t⁻¹ ∈ Γ := (mem_compressionSubmonoid.mp ht) γ hγ
  have hv' := hv _ hcomp
  unfold SoficApproximation.AlmostCommutes at hv' ⊢
  have hc : Vanishing fun n ↦ hammingDistance (A.model n)
      ((A.map n t⁻¹)⁻¹ * A.map n γ * A.map n t⁻¹) (A.map n (t * γ * t⁻¹)) := by
    refine Vanishing.squeeze (fun _ ↦ hammingDistance_nonnegative _ _ _) (fun n ↦ ?_)
      (((A.hamming_inv_vanishing t).add (A.hamming_mul_vanishing t γ)).add
        (A.hamming_mul_vanishing (t * γ) t⁻¹))
    show hammingDistance (A.model n) ((A.map n t⁻¹)⁻¹ * A.map n γ * A.map n t⁻¹)
        (A.map n (t * γ * t⁻¹)) ≤
      hammingDistance (A.model n) (A.map n t⁻¹) (A.map n t)⁻¹ +
        hammingDistance (A.model n) (A.map n (t * γ)) (A.map n t * A.map n γ) +
        hammingDistance (A.model n) (A.map n (t * γ * t⁻¹))
          (A.map n (t * γ) * A.map n t⁻¹)
    have h₁ := hammingDistance_triangle (A.model n)
      ((A.map n t⁻¹)⁻¹ * A.map n γ * A.map n t⁻¹)
      (A.map n t * A.map n γ * A.map n t⁻¹) (A.map n (t * γ * t⁻¹))
    have h₂ := hammingDistance_triangle (A.model n) (A.map n t * A.map n γ * A.map n t⁻¹)
      (A.map n (t * γ) * A.map n t⁻¹) (A.map n (t * γ * t⁻¹))
    have e₁ : hammingDistance (A.model n) ((A.map n t⁻¹)⁻¹ * A.map n γ * A.map n t⁻¹)
        (A.map n t * A.map n γ * A.map n t⁻¹) =
        hammingDistance (A.model n) ((A.map n t⁻¹)⁻¹ * A.map n γ)
          (A.map n t * A.map n γ) :=
      hammingDistance_right_invariant _ _ _ _
    have e₂ : hammingDistance (A.model n) ((A.map n t⁻¹)⁻¹ * A.map n γ)
        (A.map n t * A.map n γ) =
        hammingDistance (A.model n) (A.map n t⁻¹)⁻¹ (A.map n t) :=
      hammingDistance_right_invariant _ _ _ _
    have e₃ : hammingDistance (A.model n) (A.map n t⁻¹)⁻¹ ((A.map n t)⁻¹)⁻¹ =
        hammingDistance (A.model n) (A.map n t⁻¹) (A.map n t)⁻¹ :=
      SequentialNormalization.hammingDistance_inv_inv _ _
    rw [inv_inv] at e₃
    have e₄ : hammingDistance (A.model n) (A.map n t * A.map n γ * A.map n t⁻¹)
        (A.map n (t * γ) * A.map n t⁻¹) =
        hammingDistance (A.model n) (A.map n t * A.map n γ) (A.map n (t * γ)) :=
      hammingDistance_right_invariant _ _ _ _
    have e₅ : hammingDistance (A.model n) (A.map n t * A.map n γ) (A.map n (t * γ)) =
        hammingDistance (A.model n) (A.map n (t * γ)) (A.map n t * A.map n γ) :=
      hammingDistance_comm _ _ _
    have e₆ : hammingDistance (A.model n) (A.map n (t * γ) * A.map n t⁻¹)
        (A.map n (t * γ * t⁻¹)) =
        hammingDistance (A.model n) (A.map n (t * γ * t⁻¹))
          (A.map n (t * γ) * A.map n t⁻¹) :=
      hammingDistance_comm _ _ _
    linarith
  refine Vanishing.squeeze (fun _ ↦ hammingDistance_nonnegative _ _ _) (fun n ↦ ?_)
    (hv'.add (hc.const_mul 2))
  show hammingDistance (A.model n)
      (A.map n t⁻¹ * v n * (A.map n t⁻¹)⁻¹ * A.map n γ)
      (A.map n γ * (A.map n t⁻¹ * v n * (A.map n t⁻¹)⁻¹)) ≤
    hammingDistance (A.model n) (v n * A.map n (t * γ * t⁻¹))
        (A.map n (t * γ * t⁻¹) * v n) +
      2 * hammingDistance (A.model n) ((A.map n t⁻¹)⁻¹ * A.map n γ * A.map n t⁻¹)
        (A.map n (t * γ * t⁻¹))
  have e₁ : A.map n t⁻¹ * v n * (A.map n t⁻¹)⁻¹ * A.map n γ =
      A.map n t⁻¹ * (v n * ((A.map n t⁻¹)⁻¹ * A.map n γ * A.map n t⁻¹)) *
        (A.map n t⁻¹)⁻¹ := by
    group
  have e₂ : A.map n γ * (A.map n t⁻¹ * v n * (A.map n t⁻¹)⁻¹) =
      A.map n t⁻¹ * (((A.map n t⁻¹)⁻¹ * A.map n γ * A.map n t⁻¹) * v n) *
        (A.map n t⁻¹)⁻¹ := by
    group
  rw [e₁, e₂, hammingDistance_right_invariant, hammingDistance_left_invariant]
  exact SequentialNormalization.hammingDistance_commutator_le_right (v n) _ _

/-- The elements normalizing in both directions form a subgroup. -/
def seqNormalizerSubgroup (Γ : Subgroup G) : Subgroup G where
  carrier := {g | SeqNormalizes Γ g ∧ SeqNormalizes Γ g⁻¹}
  one_mem' := by
    show SeqNormalizes Γ 1 ∧ SeqNormalizes Γ 1⁻¹
    rw [inv_one]
    exact ⟨seqNormalizes_one Γ, seqNormalizes_one Γ⟩
  mul_mem' := by
    intro g h hg hh
    have hg' : SeqNormalizes Γ g ∧ SeqNormalizes Γ g⁻¹ := hg
    have hh' : SeqNormalizes Γ h ∧ SeqNormalizes Γ h⁻¹ := hh
    show SeqNormalizes Γ (g * h) ∧ SeqNormalizes Γ (g * h)⁻¹
    rw [mul_inv_rev]
    exact ⟨seqNormalizes_mul hg'.1 hh'.1, seqNormalizes_mul hh'.2 hg'.2⟩
  inv_mem' := by
    intro g hg
    have hg' : SeqNormalizes Γ g ∧ SeqNormalizes Γ g⁻¹ := hg
    show SeqNormalizes Γ g⁻¹ ∧ SeqNormalizes Γ g⁻¹⁻¹
    rw [inv_inv]
    exact ⟨hg'.2, hg'.1⟩

/-- **The generation step.**  If every compressor of an infranormal subgroup
normalizes sequential almost-centralizers, then every element of the ambient
group does. -/
theorem hasSequentialCentralizerNormalization_of_compressorNormalization
    {Γ : Subgroup G} (hinf : IsInfranormal Γ)
    (hcomp : HasSequentialCompressorNormalization Γ) :
    HasSequentialCentralizerNormalization Γ := by
  intro A v hv g γ hγ
  have hle : Subgroup.closure (compressionSubmonoid Γ : Set G) ≤
      seqNormalizerSubgroup Γ := by
    rw [Subgroup.closure_le]
    intro t ht
    have ht' : t ∈ compressionSubmonoid Γ := ht
    show SeqNormalizes Γ t ∧ SeqNormalizes Γ t⁻¹
    exact ⟨hcomp t ht', seqNormalizes_inv_of_mem_compressionSubmonoid ht'⟩
  have htop : Subgroup.closure (compressionSubmonoid Γ : Set G) = ⊤ := hinf
  have hg : g ∈ seqNormalizerSubgroup Γ := by
    apply hle
    rw [htop]
    exact Subgroup.mem_top g
  have hg' : SeqNormalizes Γ g ∧ SeqNormalizes Γ g⁻¹ := hg
  exact hg'.1 A v hv γ hγ

end GroupApproximation
