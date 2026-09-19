import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedDefinitions
import GroupApproximation.Manuscript.OneSidedMFRadical.SentenceNormalizedAlmostRepresentationClosure

/-!
# The printed model-separation sentence, as a genuine equivalence

`non_mf_groups_exist.tex`, `\section{Introduction}`:

> Equivalently, an MF group admits finite-dimensional unitary models whose
> multiplicative defects tend to zero in operator norm and which asymptotically
> separate its nonidentity elements: for each `g ≠ 1`, the quantity
> `limsup_n ‖V_n(g) - 1‖` is positive, with a lower bound that may depend
> on `g`.

`PrintedDefinitions.PrintedMFUnitaryModels` proves an equivalence of this shape
with the separation clause in its *all-pairs* form and with a single *uniform*
`delta > 0`; `isCDEOperatorMF_exists_separating_unitary_models` delivers the
printed nonidentity form in the forward direction only, and its docstring
records that the converse from nonidentity separation alone was not proved
there.  This module proves that converse and states the printed sentence as a
genuine equivalence in the printed form: separation from the identity only, and
a lower bound that may depend on `g` -- which is what positivity of a `limsup`
says, no uniform constant being asserted.

The route is the one the printed sentence describes.

* A family of unitary models whose multiplicative defects tend to zero in
  operator norm *is* a homomorphism into the unitary group of the cofinite norm
  matrix corona: the defects are exactly what the quotient kills.  That
  homomorphism is already built, as
  `opAlmostRepresentationCofiniteCoronaHom`.
* A class in that corona is trivial exactly when its coordinate distances to
  the identity tend to zero -- that is the definition of
  `IsNullCofiniteOpSeq`, and `opLength Y u` is literally `‖u - 1‖`.
* Hence positivity of `limsup_n ‖V_n(g) - 1‖` is precisely nontriviality of the
  image of `g` (`limsup_norm_sub_one_pos_iff_not_isNullCofiniteOpSeq`), and the
  printed separation clause is precisely injectivity of the induced
  homomorphism.
* `isCDEOperatorMF_iff_isOperatorMF` then supplies the strictly increasing
  positive dimension sequence demanded by `IsCDEOperatorMF`; no padding step is
  introduced here.

Two points of honesty about the statement below.

1.  The models are required to be nonzero (`∀ n, 0 < Fintype.card (X n)`), on
    both sides of the equivalence.  This is the printed reading of
    "finite-dimensional unitary models" -- the printed corona is built from
    matrix algebras `M_{d_n}(ℂ)` -- and it is the same clause that
    `PrintedMFUnitaryModels` already carries.  It is produced, not assumed, in
    the forward direction.
2.  Nothing else is added: the separation hypothesis of the converse is the
    printed one, `0 < limsup_n ‖V_n(g) - 1‖` for each `g ≠ 1`, with no uniform
    lower bound and with the identity matrix -- not `V_n(1)` -- as the
    comparison point.

No theorem from the literature is an input.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open Filter Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

/-! ## The printed separation quantity is a corona nontriviality test -/

/-- **The printed `limsup` measures nontriviality in the corona.**  For a
sequence of unitary models on nonzero coordinates, the printed quantity
`limsup_n ‖v_n - 1‖` is positive exactly when the sequence is *not* null along
the cofinite filter -- that is, exactly when its class in the norm matrix
corona is not the identity.

Both directions are elementary and both are used: the forward one converts the
printed separation clause into injectivity, the backward one converts an
eventual separation into the printed clause.  The uniform bound
`‖v_n - 1‖ ≤ 2` is what makes the `limsup` a genuine bound rather than a junk
value. -/
theorem limsup_norm_sub_one_pos_iff_not_isNullCofiniteOpSeq
    (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n))
    (v : ∀ n, Matrix.unitaryGroup (X n) ℂ) :
    0 < Filter.limsup (fun n ↦ ‖(v n : Matrix (X n) (X n) ℂ) - 1‖) Filter.atTop ↔
      ¬ IsNullCofiniteOpSeq X v := by
  have hbdd : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (fun n ↦ ‖(v n : Matrix (X n) (X n) ℂ) - 1‖) := by
    refine Filter.isBoundedUnder_of ⟨2, fun n ↦ ?_⟩
    letI : Nonempty (X n) := Fintype.card_pos_iff.mp (hX n)
    show ‖(v n : Matrix (X n) (X n) ℂ) - 1‖ ≤ (2 : ℝ)
    have hv : ‖(v n : Matrix (X n) (X n) ℂ)‖ = 1 :=
      CStarRing.norm_of_mem_unitary (v n).2
    have hone : ‖(1 : Matrix (X n) (X n) ℂ)‖ = 1 := CStarRing.norm_one
    have htri := norm_sub_le (v n : Matrix (X n) (X n) ℂ)
      (1 : Matrix (X n) (X n) ℂ)
    rw [hv, hone] at htri
    linarith
  constructor
  · intro hpos hnull
    have htend : Filter.Tendsto
        (fun n ↦ ‖(v n : Matrix (X n) (X n) ℂ) - 1‖) Filter.atTop (nhds 0) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      rw [← Nat.cofinite_eq_atTop]
      filter_upwards [hnull ε hε] with n hn
      calc dist ‖(v n : Matrix (X n) (X n) ℂ) - 1‖ (0 : ℝ)
          = ‖(v n : Matrix (X n) (X n) ℂ) - 1‖ := by
            rw [Real.dist_eq, sub_zero, abs_norm]
        _ < ε := hn
    rw [htend.limsup_eq] at hpos
    exact lt_irrefl 0 hpos
  · intro hnull
    have hex : ∃ ε : ℝ, 0 < ε ∧
        ¬ (∀ᶠ n in Filter.cofinite, opLength (X n) (v n) < ε) := by
      by_contra hcon
      apply hnull
      intro ε hε
      by_contra hbad
      exact hcon ⟨ε, hε, hbad⟩
    obtain ⟨ε, hε, hbad⟩ := hex
    have hfreq : ∃ᶠ n in Filter.atTop,
        ε ≤ ‖(v n : Matrix (X n) (X n) ℂ) - 1‖ := by
      rw [← Nat.cofinite_eq_atTop]
      exact (Filter.not_eventually.mp hbad).mono fun n hn ↦ not_lt.mp hn
    exact lt_of_lt_of_le hε (Filter.le_limsup_of_frequently_le hfreq hbdd)

/-! ## The missing converse -/

/-- **The converse of the printed sentence.**  A countable group carrying
finite-dimensional unitary models whose multiplicative defects tend to zero in
operator norm, and for which `limsup_n ‖V_n(g) - 1‖` is positive at every
nonidentity `g`, is MF.

This is the implication whose absence
`isCDEOperatorMF_exists_separating_unitary_models` records.  No uniform
separation constant is assumed: the lower bound is allowed to depend on `g`,
exactly as printed, and it is never named.

The proof reads the models as the corona homomorphism they induce, which is
`opAlmostRepresentationCofiniteCoronaHom` of the almost representation they
form, and reads the printed separation clause as triviality of no nonidentity
image. -/
theorem isCDEOperatorMF_of_limsup_separating_unitary_models (G : Type) [Group G]
    [Countable G] (X : ℕ → FiniteModel)
    (V : ∀ n, G → Matrix.unitaryGroup (X n) ℂ)
    (hX : ∀ n, 0 < Fintype.card (X n))
    (hmul : ∀ g h : G, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      ‖(V n (g * h) : Matrix (X n) (X n) ℂ) -
        (V n g : Matrix (X n) (X n) ℂ) * V n h‖ ≤ ε)
    (hsep : ∀ g : G, g ≠ 1 → 0 < Filter.limsup
      (fun n ↦ ‖(V n g : Matrix (X n) (X n) ℂ) - 1‖) Filter.atTop) :
    IsCDEOperatorMF G := by
  refine (isCDEOperatorMF_iff_isOperatorMF G).mpr ⟨X, hX,
    opAlmostRepresentationCofiniteCoronaHom
      ({ model := X, modelNonempty := hX, map := V,
          asymptoticallyMultiplicative := hmul } : OpAlmostRepresentation G),
    ?_⟩
  refine (injective_iff_map_eq_one _).mpr ?_
  intro g hg
  by_contra hgne
  have hquot : (QuotientGroup.mk (fun n ↦ V n g) :
      NormMatrixCoronaUnitary X) = 1 := hg
  have hmem : IsNullCofiniteOpSeq X (fun n ↦ V n g) :=
    (QuotientGroup.eq_one_iff (N := nullCofiniteOpSubgroup X)
      (fun n ↦ V n g)).mp hquot
  exact (limsup_norm_sub_one_pos_iff_not_isNullCofiniteOpSeq X hX
    (fun n ↦ V n g)).mp (hsep g hgne) hmem

/-! ## The printed sentence, both directions -/

/-- **The printed sentence in its own form, forward direction.**  An MF group
admits finite-dimensional unitary models whose multiplicative defects tend to
zero in operator norm and for which `limsup_n ‖V_n(g) - 1‖` is positive at
every nonidentity `g`.

`PrintedMFUnitaryModels` supplies models separating *pairs* at a uniform
`delta`; the printed clause compares `V_n(g)` with the identity matrix rather
than with `V_n(1)`, and the two differ by
`KazhdanCornerMatrices.map_one_vanishing`, which says that any asymptotically
multiplicative unitary family already satisfies `‖V_n(1) - 1‖ → 0`.  Half the
uniform gap survives that comparison, and half a positive constant is a
positive lower bound for the `limsup`. -/
theorem exists_limsup_separating_unitary_models_of_isCDEOperatorMF (G : Type)
    [Group G] [Countable G] (h : IsCDEOperatorMF G) :
    ∃ (X : ℕ → FiniteModel) (V : ∀ n, G → Matrix.unitaryGroup (X n) ℂ),
      (∀ n, 0 < Fintype.card (X n)) ∧
        (∀ g h : G, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
          ‖(V n (g * h) : Matrix (X n) (X n) ℂ) -
            (V n g : Matrix (X n) (X n) ℂ) * V n h‖ ≤ ε) ∧
        (∀ g : G, g ≠ 1 → 0 < Filter.limsup
          (fun n ↦ ‖(V n g : Matrix (X n) (X n) ℂ) - 1‖) Filter.atTop) := by
  obtain ⟨X, V, delta, hX, hdelta, hmul, hsep⟩ :=
    (manuscriptMFUnitaryModels G).mp h
  refine ⟨X, V, hX, hmul, ?_⟩
  intro g hg
  have hone : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      ‖(V n 1 : Matrix (X n) (X n) ℂ) - 1‖ ≤ ε :=
    KazhdanCornerMatrices.map_one_vanishing
      ({ model := X, modelNonempty := hX, map := V,
          asymptoticallyMultiplicative := hmul } : OpAlmostRepresentation G)
  obtain ⟨N₁, hN₁⟩ := hone (delta / 2) (by linarith)
  obtain ⟨N₂, hN₂⟩ := hsep g 1 hg
  have hev : ∀ᶠ n in Filter.atTop,
      delta / 2 ≤ ‖(V n g : Matrix (X n) (X n) ℂ) - 1‖ := by
    filter_upwards [Filter.eventually_ge_atTop (max N₁ N₂)] with n hn
    show delta / 2 ≤ ‖(V n g : Matrix (X n) (X n) ℂ) - 1‖
    have h₁ := hN₁ n (le_trans (le_max_left N₁ N₂) hn)
    have h₂ := hN₂ n (le_trans (le_max_right N₁ N₂) hn)
    have hsplit : (V n g : Matrix (X n) (X n) ℂ) - V n 1 =
        ((V n g : Matrix (X n) (X n) ℂ) - 1) -
          ((V n 1 : Matrix (X n) (X n) ℂ) - 1) := by
      abel
    have htri : ‖(V n g : Matrix (X n) (X n) ℂ) - V n 1‖ ≤
        ‖(V n g : Matrix (X n) (X n) ℂ) - 1‖ +
          ‖(V n 1 : Matrix (X n) (X n) ℂ) - 1‖ := by
      rw [hsplit]
      exact norm_sub_le _ _
    linarith
  have hbdd : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (fun n ↦ ‖(V n g : Matrix (X n) (X n) ℂ) - 1‖) := by
    refine Filter.isBoundedUnder_of ⟨2, fun n ↦ ?_⟩
    letI : Nonempty (X n) := Fintype.card_pos_iff.mp (hX n)
    show ‖(V n g : Matrix (X n) (X n) ℂ) - 1‖ ≤ (2 : ℝ)
    have hv : ‖(V n g : Matrix (X n) (X n) ℂ)‖ = 1 :=
      CStarRing.norm_of_mem_unitary (V n g).2
    have hid : ‖(1 : Matrix (X n) (X n) ℂ)‖ = 1 := CStarRing.norm_one
    have htri := norm_sub_le (V n g : Matrix (X n) (X n) ℂ)
      (1 : Matrix (X n) (X n) ℂ)
    rw [hv, hid] at htri
    linarith
  exact lt_of_lt_of_le (by linarith : (0 : ℝ) < delta / 2)
    (Filter.le_limsup_of_frequently_le hev.frequently hbdd)

/-- **The printed "equivalently" sentence, as printed.**  A countable group is
MF exactly when it admits finite-dimensional unitary models on nonzero
coordinates whose multiplicative defects tend to zero in operator norm and
which asymptotically separate its nonidentity elements in the printed sense:
for each `g ≠ 1`, the quantity `limsup_n ‖V_n(g) - 1‖` is positive.

This is `PrintedMFUnitaryModels` with the two gaps between that statement and
the printed one closed: the separation clause is the printed nonidentity form
rather than the all-pairs form, and the lower bound is per element rather than
one uniform `delta`.  Both directions are proved. -/
def PrintedMFModelSeparation : Prop :=
  ∀ (G : Type) [Group G] [Countable G],
    IsCDEOperatorMF G ↔
      ∃ (X : ℕ → FiniteModel) (V : ∀ n, G → Matrix.unitaryGroup (X n) ℂ),
        (∀ n, 0 < Fintype.card (X n)) ∧
          (∀ g h : G, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
            ‖(V n (g * h) : Matrix (X n) (X n) ℂ) -
              (V n g : Matrix (X n) (X n) ℂ) * V n h‖ ≤ ε) ∧
          (∀ g : G, g ≠ 1 → 0 < Filter.limsup
            (fun n ↦ ‖(V n g : Matrix (X n) (X n) ℂ) - 1‖) Filter.atTop)

/-- Closed proof of the printed "equivalently" sentence in its printed form. -/
theorem manuscriptPrintedMFModelSeparation : PrintedMFModelSeparation := by
  intro G _ _
  constructor
  · exact exists_limsup_separating_unitary_models_of_isCDEOperatorMF G
  · rintro ⟨X, V, hX, hmul, hsep⟩
    exact isCDEOperatorMF_of_limsup_separating_unitary_models G X V hX hmul hsep

end

end OneSidedMFRadical
end Manuscript
end GroupApproximation
