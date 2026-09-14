import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedModelSeparationConverse
import GroupApproximation.Meta.AxiomGuard

/-!
# Korchagin's full-sequence reformulation, over the printed models

`non_mf_groups_exist.tex`, `\section{Introduction}`, lines 88-102 (origin/main):

> A countable group `G` is MF~\cite{CDE} if there are positive integers `d_n`
> and maps `V_n : G → U(d_n)`, with `V_n(1)=1`, such that
> `‖V_n(gh) - V_n(g)V_n(h)‖ → 0` `(g,h ∈ G)`, and
> `limsup_n ‖V_n(g) - 1‖ > 0` `(g ∈ G \ {1})`.
> For countable `G`, the second condition may equivalently be required along
> the full sequence with a constant independent of
> `g`~\cite[Propositions~2 and~7]{Korchagin}.

`KorchaginFullSequenceSentence.lean` proves that `IsOperatorMF` is equivalent
to a `WeakMFApproximation`.  There the separation clause is pairwise and
eventual, and the models carry no `V_n(1) = 1` clause, so it is not the
printed object.  This module states the sentence over the printed models
themselves: the same data `(d_n, V_n)`, with `V_n(1) = 1` and the same
multiplicativity clause, and with the second condition replaced by
`∃ c > 0, ∀ g ≠ 1, ∀ n, c ≤ ‖V_n(g) - 1‖`.

## Route (Korchagin, Propositions 2 and 7)

Korchagin's Proposition 7 normalizes the separation of an MF group to a fixed
constant at every nontrivial element.  Proposition 2 passes between the
sequential and the local formulations.  In the development these steps are:

* `OperatorMFLocalNormalization.isNormApproximable_one`: constant `1` on every
  finite set, by tensor amplification and block sums.
* `exists_weakMFApproximation`: the sequential assembly.
* `isCDEOperatorMF_iff_nonempty_weakMFApproximation`: packages the two.

From the resulting sequence `A` we get the printed models in two steps:

1. Normalize `V_n(1) = 1` by left multiplication with `A_n(1)⁻¹`.
2. Replace `V_n(g)` by `-1` at the finitely many indices where `g ≠ 1` is not
   yet separated by the constant of `A`.

For fixed `g, h` this changes only finitely many terms, so multiplicativity
survives.  Since `‖-1 - 1‖ = 2`, every index then carries the constant
`min(separation, 2)`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMFSentences
namespace KorchaginFullSequenceLiteral

open Filter Matrix
open scoped Matrix.Norms.L2Operator
open GroupApproximation.Manuscript.OneSidedMFRadical

noncomputable section

/-! ### Norm facts on a positive-dimensional model -/

theorem norm_unitary_sub_one_le_two {Y : FiniteModel} (u : Matrix.unitaryGroup Y ℂ)
    (hY : 0 < Fintype.card Y) : ‖(u : Matrix Y Y ℂ) - 1‖ ≤ 2 := by
  letI : Nonempty Y := Fintype.card_pos_iff.mp hY
  have hv : ‖(u : Matrix Y Y ℂ)‖ = 1 := CStarRing.norm_of_mem_unitary u.2
  have hone : ‖(1 : Matrix Y Y ℂ)‖ = 1 := CStarRing.norm_one
  have htri := norm_sub_le (u : Matrix Y Y ℂ) (1 : Matrix Y Y ℂ)
  rw [hv, hone] at htri
  linarith

theorem norm_neg_one_sub_one {Y : FiniteModel} (hY : 0 < Fintype.card Y) :
    ‖(-1 : Matrix Y Y ℂ) - 1‖ = 2 := by
  letI : Nonempty Y := Fintype.card_pos_iff.mp hY
  have h : (-1 : Matrix Y Y ℂ) - 1 = (-2 : ℂ) • (1 : Matrix Y Y ℂ) := by
    rw [neg_smul, two_smul]
    abel
  rw [h, norm_smul, CStarRing.norm_one, mul_one, norm_neg]
  simp

theorem neg_one_mem_unitaryGroup {Y : Type} [Fintype Y] [DecidableEq Y] :
    (-1 : Matrix Y Y ℂ) ∈ Matrix.unitaryGroup Y ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', star_neg, star_one, neg_mul_neg, one_mul]

/-! ### Normalizing `V_n(1) = 1` -/

section Normalized

variable {G : Type} [Group G]

theorem norm_conjTranspose_mul_sub_conjTranspose_mul_mul_le
    {Y : Type} [Fintype Y] [DecidableEq Y] {u p q w : Matrix Y Y ℂ}
    (hu : u ∈ Matrix.unitaryGroup Y ℂ) (hp : p ∈ Matrix.unitaryGroup Y ℂ)
    (hq : q ∈ Matrix.unitaryGroup Y ℂ) :
    ‖Matrix.conjTranspose u * w -
        (Matrix.conjTranspose u * p) * (Matrix.conjTranspose u * q)‖ ≤
      ‖w - p * q‖ + ‖u - u * u‖ := by
  have hustar : Matrix.conjTranspose u ∈ Matrix.unitaryGroup Y ℂ := by
    rw [← Matrix.star_eq_conjTranspose]; exact Unitary.star_mem hu
  have hone : ‖(1 : Matrix Y Y ℂ) - Matrix.conjTranspose u‖ = ‖u - u * u‖ := by
    rw [show (1 : Matrix Y Y ℂ) - Matrix.conjTranspose u =
        Matrix.conjTranspose ((1 : Matrix Y Y ℂ) - u) by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one],
      Matrix.l2_opNorm_conjTranspose,
      show u - u * u = u * ((1 : Matrix Y Y ℂ) - u) by rw [mul_sub, mul_one],
      CStarRing.norm_mem_unitary_mul _ hu]
  have hsplit : Matrix.conjTranspose u * w -
      (Matrix.conjTranspose u * p) * (Matrix.conjTranspose u * q) =
        Matrix.conjTranspose u * (w - p * (Matrix.conjTranspose u * q)) := by
    rw [mul_sub]; simp only [mul_assoc]
  have hmid : ‖p * q - p * (Matrix.conjTranspose u * q)‖ =
      ‖(1 : Matrix Y Y ℂ) - Matrix.conjTranspose u‖ := by
    rw [show p * q - p * (Matrix.conjTranspose u * q) =
        p * (((1 : Matrix Y Y ℂ) - Matrix.conjTranspose u) * q) by
      rw [sub_mul, one_mul, mul_sub],
      CStarRing.norm_mem_unitary_mul _ hp,
      CStarRing.norm_mul_mem_unitary _ hq]
  calc ‖Matrix.conjTranspose u * w -
          (Matrix.conjTranspose u * p) * (Matrix.conjTranspose u * q)‖
      = ‖w - p * (Matrix.conjTranspose u * q)‖ := by
        rw [hsplit, CStarRing.norm_mem_unitary_mul _ hustar]
    _ ≤ ‖w - p * q‖ + ‖p * q - p * (Matrix.conjTranspose u * q)‖ := by
        rw [← sub_add_sub_cancel w (p * q) (p * (Matrix.conjTranspose u * q))]
        exact norm_add_le _ _
    _ = ‖w - p * q‖ + ‖(1 : Matrix Y Y ℂ) - Matrix.conjTranspose u‖ := by rw [hmid]
    _ = ‖w - p * q‖ + ‖u - u * u‖ := by rw [hone]

theorem norm_conjTranspose_mul_sub_one {Y : Type} [Fintype Y] [DecidableEq Y]
    {u p : Matrix Y Y ℂ} (hu : u ∈ Matrix.unitaryGroup Y ℂ) :
    ‖Matrix.conjTranspose u * p - 1‖ = ‖p - u‖ := by
  have hstar : Matrix.conjTranspose u * u = 1 := by
    have h := hu
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at h
    exact h
  have hustar : Matrix.conjTranspose u ∈ Matrix.unitaryGroup Y ℂ := by
    rw [← Matrix.star_eq_conjTranspose]; exact Unitary.star_mem hu
  rw [show Matrix.conjTranspose u * p - 1 = Matrix.conjTranspose u * (p - u) by
    rw [mul_sub, hstar],
    CStarRing.norm_mem_unitary_mul _ hustar]

/-- `A_n(1)⁻¹ A_n(g)`, read with `u⁻¹ = uᴴ` for a unitary `u`. -/
def normalizedMap (A : WeakMFApproximation G) (n : ℕ) (g : G) :
    Matrix (A.model n) (A.model n) ℂ :=
  Matrix.conjTranspose (A.map n 1 : Matrix (A.model n) (A.model n) ℂ) *
    (A.map n g : Matrix (A.model n) (A.model n) ℂ)

theorem normalizedMap_isUnitary (A : WeakMFApproximation G) (n : ℕ) (g : G) :
    normalizedMap A n g ∈ Matrix.unitaryGroup (A.model n) ℂ := by
  have hustar : Matrix.conjTranspose (A.map n 1 : Matrix (A.model n) (A.model n) ℂ) ∈
      Matrix.unitaryGroup (A.model n) ℂ := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.star_mem (A.map n 1).property
  exact mul_mem hustar (A.map n g).property

theorem normalizedMap_one (A : WeakMFApproximation G) (n : ℕ) :
    normalizedMap A n 1 = 1 := by
  have h := (A.map n 1).property
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at h
  exact h

theorem norm_normalizedMap_sub_one (A : WeakMFApproximation G) (n : ℕ) (g : G) :
    ‖normalizedMap A n g - 1‖ =
      ‖(A.map n g : Matrix (A.model n) (A.model n) ℂ) -
        (A.map n 1 : Matrix (A.model n) (A.model n) ℂ)‖ :=
  norm_conjTranspose_mul_sub_one (A.map n 1).property

theorem norm_normalizedMap_mul_sub_le (A : WeakMFApproximation G) (n : ℕ) (g h : G) :
    ‖normalizedMap A n (g * h) - normalizedMap A n g * normalizedMap A n h‖ ≤
      ‖(A.map n (g * h) : Matrix (A.model n) (A.model n) ℂ) -
          (A.map n g : Matrix (A.model n) (A.model n) ℂ) *
            (A.map n h : Matrix (A.model n) (A.model n) ℂ)‖ +
      ‖(A.map n 1 : Matrix (A.model n) (A.model n) ℂ) -
          (A.map n 1 : Matrix (A.model n) (A.model n) ℂ) *
            (A.map n 1 : Matrix (A.model n) (A.model n) ℂ)‖ :=
  norm_conjTranspose_mul_sub_conjTranspose_mul_mul_le
    (A.map n 1).property (A.map n g).property (A.map n h).property

/-! ### Separating along the full sequence -/

open Classical in
/-- The printed full-sequence models: the normalized map, with `V_n(g)`
replaced by `-1` wherever `g ≠ 1` is not yet separated by `A.separation`. -/
def fullSequenceMap (A : WeakMFApproximation G) (n : ℕ) (g : G) :
    Matrix (A.model n) (A.model n) ℂ :=
  if g ≠ 1 ∧ ‖normalizedMap A n g - 1‖ < A.separation then -1 else normalizedMap A n g

theorem fullSequenceMap_eq_of_le (A : WeakMFApproximation G) (n : ℕ) (g : G)
    (h : A.separation ≤ ‖normalizedMap A n g - 1‖) :
    fullSequenceMap A n g = normalizedMap A n g := by
  unfold fullSequenceMap
  exact if_neg fun hc ↦ (not_lt.mpr h) hc.2

theorem fullSequenceMap_one (A : WeakMFApproximation G) (n : ℕ) :
    fullSequenceMap A n 1 = 1 := by
  unfold fullSequenceMap
  rw [if_neg fun hc ↦ hc.1 rfl, normalizedMap_one]

theorem fullSequenceMap_isUnitary (A : WeakMFApproximation G) (n : ℕ) (g : G) :
    fullSequenceMap A n g ∈ Matrix.unitaryGroup (A.model n) ℂ := by
  unfold fullSequenceMap
  split_ifs
  · exact neg_one_mem_unitaryGroup
  · exact normalizedMap_isUnitary A n g

theorem min_separation_le_fullSequenceMap (A : WeakMFApproximation G) (n : ℕ) {g : G}
    (hg : g ≠ 1) : min A.separation 2 ≤ ‖fullSequenceMap A n g - 1‖ := by
  by_cases hlt : ‖normalizedMap A n g - 1‖ < A.separation
  · have hval : fullSequenceMap A n g = -1 := by
      unfold fullSequenceMap
      exact if_pos ⟨hg, hlt⟩
    rw [hval, norm_neg_one_sub_one (A.modelNonempty n)]
    exact min_le_right _ _
  · rw [fullSequenceMap_eq_of_le A n g (not_lt.mp hlt)]
    exact le_trans (min_le_left _ _) (not_lt.mp hlt)

theorem eventually_fullSequenceMap_eq (A : WeakMFApproximation G) (g : G) :
    ∀ᶠ n in atTop, fullSequenceMap A n g = normalizedMap A n g := by
  by_cases hg : g = 1
  · subst hg
    exact Filter.Eventually.of_forall fun n ↦ by
      rw [fullSequenceMap_one, normalizedMap_one]
  · obtain ⟨N, hN⟩ := A.separatedEventually g 1 hg
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    refine fullSequenceMap_eq_of_le A n g ?_
    rw [norm_normalizedMap_sub_one A n g]
    exact hN n hn

theorem fullSequenceMap_mul (A : WeakMFApproximation G) (g h : G) (ε : ℝ) (hε : 0 < ε) :
    ∃ N, ∀ n ≥ N,
      ‖fullSequenceMap A n (g * h) - fullSequenceMap A n g * fullSequenceMap A n h‖ ≤ ε := by
  obtain ⟨N1, hN1⟩ := A.asymptoticallyMultiplicative g h (ε / 2) (by linarith)
  obtain ⟨N2, hN2⟩ := A.asymptoticallyMultiplicative 1 1 (ε / 2) (by linarith)
  have hev : ∀ᶠ n in atTop,
      ‖fullSequenceMap A n (g * h) - fullSequenceMap A n g * fullSequenceMap A n h‖ ≤ ε := by
    filter_upwards [eventually_fullSequenceMap_eq A (g * h), eventually_fullSequenceMap_eq A g,
      eventually_fullSequenceMap_eq A h, Filter.eventually_ge_atTop (max N1 N2)]
      with n hgh hg hh hn
    rw [hgh, hg, hh]
    have h1 := hN1 n (le_trans (le_max_left N1 N2) hn)
    have h2 := hN2 n (le_trans (le_max_right N1 N2) hn)
    simp only [one_mul] at h2
    calc ‖normalizedMap A n (g * h) - normalizedMap A n g * normalizedMap A n h‖
        ≤ ‖(A.map n (g * h) : Matrix (A.model n) (A.model n) ℂ) -
              (A.map n g : Matrix (A.model n) (A.model n) ℂ) *
                (A.map n h : Matrix (A.model n) (A.model n) ℂ)‖ +
            ‖(A.map n 1 : Matrix (A.model n) (A.model n) ℂ) -
              (A.map n 1 : Matrix (A.model n) (A.model n) ℂ) *
                (A.map n 1 : Matrix (A.model n) (A.model n) ℂ)‖ :=
          norm_normalizedMap_mul_sub_le A n g h
      _ ≤ ε / 2 + ε / 2 := add_le_add h1 h2
      _ = ε := by ring
  exact Filter.eventually_atTop.mp hev

end Normalized

/-! ### The two directions -/

/-- **Forward.**  A countable MF group has printed models with `V_n(1) = 1`
whose nonidentity elements are separated from `1` by one constant at every
index. -/
theorem exists_uniformModels_of_isCDEOperatorMF (G : Type) [Group G] [Countable G]
    (hG : IsCDEOperatorMF G) :
    ∃ (X : ℕ → FiniteModel) (V : ∀ n, G → Matrix.unitaryGroup (X n) ℂ),
      (∀ n, 0 < Fintype.card (X n)) ∧
        (∀ n, V n 1 = 1) ∧
        (∀ g h : G, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
          ‖(V n (g * h) : Matrix (X n) (X n) ℂ) -
            (V n g : Matrix (X n) (X n) ℂ) * V n h‖ ≤ ε) ∧
        ∃ c : ℝ, 0 < c ∧ ∀ g : G, g ≠ 1 → ∀ n,
          c ≤ ‖(V n g : Matrix (X n) (X n) ℂ) - 1‖ := by
  obtain ⟨A⟩ := (isCDEOperatorMF_iff_nonempty_weakMFApproximation G).mp hG
  refine ⟨A.model, fun n g ↦ ⟨fullSequenceMap A n g, fullSequenceMap_isUnitary A n g⟩,
    A.modelNonempty, fun n ↦ Subtype.ext (fullSequenceMap_one A n), ?_,
    min A.separation 2, lt_min A.separation_pos two_pos, ?_⟩
  · intro g h ε hε
    exact fullSequenceMap_mul A g h ε hε
  · intro g hg n
    exact min_separation_le_fullSequenceMap A n hg

/-- **Backward.**  A constant valid at every index bounds the `limsup`. -/
theorem limsup_pos_of_forall_le {G : Type} {X : ℕ → FiniteModel}
    (V : ∀ n, G → Matrix.unitaryGroup (X n) ℂ) (hX : ∀ n, 0 < Fintype.card (X n))
    {g : G} {c : ℝ} (hc : 0 < c) (hsep : ∀ n, c ≤ ‖(V n g : Matrix (X n) (X n) ℂ) - 1‖) :
    0 < Filter.limsup (fun n ↦ ‖(V n g : Matrix (X n) (X n) ℂ) - 1‖) Filter.atTop := by
  have hbdd : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (fun n ↦ ‖(V n g : Matrix (X n) (X n) ℂ) - 1‖) :=
    Filter.isBoundedUnder_of ⟨2, fun n ↦ norm_unitary_sub_one_le_two (V n g) (hX n)⟩
  exact lt_of_lt_of_le hc
    (Filter.le_limsup_of_frequently_le (Filter.Eventually.of_forall hsep).frequently hbdd)

/-! ### The printed sentence -/

/-- **Printed** (tex lines 88-102): "For countable `G`, the second condition
may equivalently be required along the full sequence with a constant
independent of `g`~\cite[Propositions~2 and~7]{Korchagin}."

The first conjunct is the sentence over the printed models.  The left side is
the printed definition's data `(d_n, V_n)`, with `V_n(1)=1`, the
multiplicativity clause, and `limsup_n ‖V_n(g) - 1‖ > 0` for `g ≠ 1`.  The right
side is the same data with the second condition "along the full sequence with
a constant independent of `g`": one `c > 0` with `c ≤ ‖V_n(g) - 1‖` for every
`g ≠ 1` and every `n`.  The second conjunct is the same equivalence with the
left side read as the defined notion `IsCDEOperatorMF`. -/
def PrintedKorchaginFullSequenceLiteral : Prop :=
  ∀ (G : Type) [Group G] [Countable G],
    ((∃ (X : ℕ → FiniteModel) (V : ∀ n, G → Matrix.unitaryGroup (X n) ℂ),
        (∀ n, 0 < Fintype.card (X n)) ∧
          (∀ n, V n 1 = 1) ∧
          (∀ g h : G, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
            ‖(V n (g * h) : Matrix (X n) (X n) ℂ) -
              (V n g : Matrix (X n) (X n) ℂ) * V n h‖ ≤ ε) ∧
          (∀ g : G, g ≠ 1 → 0 < Filter.limsup
            (fun n ↦ ‖(V n g : Matrix (X n) (X n) ℂ) - 1‖) Filter.atTop)) ↔
      (∃ (X : ℕ → FiniteModel) (V : ∀ n, G → Matrix.unitaryGroup (X n) ℂ),
        (∀ n, 0 < Fintype.card (X n)) ∧
          (∀ n, V n 1 = 1) ∧
          (∀ g h : G, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
            ‖(V n (g * h) : Matrix (X n) (X n) ℂ) -
              (V n g : Matrix (X n) (X n) ℂ) * V n h‖ ≤ ε) ∧
          ∃ c : ℝ, 0 < c ∧ ∀ g : G, g ≠ 1 → ∀ n,
            c ≤ ‖(V n g : Matrix (X n) (X n) ℂ) - 1‖)) ∧
    (IsCDEOperatorMF G ↔
      ∃ (X : ℕ → FiniteModel) (V : ∀ n, G → Matrix.unitaryGroup (X n) ℂ),
        (∀ n, 0 < Fintype.card (X n)) ∧
          (∀ n, V n 1 = 1) ∧
          (∀ g h : G, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
            ‖(V n (g * h) : Matrix (X n) (X n) ℂ) -
              (V n g : Matrix (X n) (X n) ℂ) * V n h‖ ≤ ε) ∧
          ∃ c : ℝ, 0 < c ∧ ∀ g : G, g ≠ 1 → ∀ n,
            c ≤ ‖(V n g : Matrix (X n) (X n) ℂ) - 1‖)

theorem manuscriptSentence_korchaginFullSequenceLiteral :
    PrintedKorchaginFullSequenceLiteral := by
  intro G _ _
  refine ⟨⟨?_, ?_⟩, ⟨exists_uniformModels_of_isCDEOperatorMF G, ?_⟩⟩
  · rintro ⟨X, V, hX, -, hmul, hsep⟩
    exact exists_uniformModels_of_isCDEOperatorMF G
      (isCDEOperatorMF_of_limsup_separating_unitary_models G X V hX hmul hsep)
  · rintro ⟨X, V, hX, h1, hmul, c, hc, hsep⟩
    exact ⟨X, V, hX, h1, hmul, fun g hg ↦ limsup_pos_of_forall_le V hX hc (hsep g hg)⟩
  · rintro ⟨X, V, hX, -, hmul, c, hc, hsep⟩
    exact isCDEOperatorMF_of_limsup_separating_unitary_models G X V hX hmul
      fun g hg ↦ limsup_pos_of_forall_le V hX hc (hsep g hg)

end

end KorchaginFullSequenceLiteral
end NonMFSentences
end Manuscript
end GroupApproximation

open GroupApproximation.Manuscript.NonMFSentences.KorchaginFullSequenceLiteral

#audit_axioms exists_uniformModels_of_isCDEOperatorMF
#audit_axioms limsup_pos_of_forall_le
#audit_closed_axioms manuscriptSentence_korchaginFullSequenceLiteral
