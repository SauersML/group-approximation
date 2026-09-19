import GroupApproximation.GGT.OsinTheorem54SepSymmetric
import GroupApproximation.GGT.WPDElementaryEmbedding

/-!
# `SepData.sep_comm` is false for the separating-coset count

`GGT/OsinTheorem54SeparatingCosets.lean` raised the question and
`GGT/OsinTheorem54SepSymmetric.lean` supplied the repair.  This module settles
the question: **the canonical `sep := OsinComponents.sepCard D lam Dc` does not
satisfy `SepData.sep_comm`**, because `sepSet` itself is not symmetric.

## The model

Take a group with an element `t` of infinite order, and

    X = {t},   H = G,   Λ a point.

`oneLetterRelGenSet` is that relative generating set, and
`isHyperbolicallyEmbedded_oneLetter` proves `H ↪_h (G,X)` for it:

* `Γ(G, X ⊔ H)` has diameter one, `H` being everything, so it is hyperbolic by
  `GGT.isHyperbolicSpace_of_bounded`;
* `d̂` is *not* degenerate even so.  Every vertex lies in `H`, so an avoiding path
  may never read an `H`-letter, and its letters are all `base t`
  (`listVal_eq_pow`).  So `relBall () n = {t^k : k ≤ n}`, which is finite: local
  finiteness holds.

That last point is the whole example.  `t` is an `X`-letter, so `d̂(1,t) ≤ 1`;
but `t⁻¹` is *not* an `X`-letter, and the only way to reach it would be through
an `H`-letter, which the avoidance condition forbids at every vertex.  So
`d̂(1,t⁻¹) = ∞` while `d̂(1,t) ≤ 1`, and the two directions of one edge are not
alike.

## The consequence

* `sepSet_one_t` --- `S(1,t;D) = ∅`, by `sepSet_eq_empty_of_mem_base`: the
  penetration of the one-letter geodesic `comp () t` spans `t`, which lies in the
  radius-one ball, so it is not essential.
* `mem_sepSet_t_one` --- `S(t,1;D) ≠ ∅`: the *only* geodesic from `t` to `1` is
  `comp () t⁻¹`, `t⁻¹` not being an `X`-letter, and its penetration spans `t⁻¹`,
  which is in no ball.
* `not_sepSet_comm`, `not_forall_sepSet_comm` --- so symmetry fails, and fails at
  `Type 0` for `Multiplicative ℤ`, closing the universal statement.

## What the corrected field must be

`sep_comm` is not repaired by choosing a different `sep`: the asymmetry is in the
geometry the field is supposed to describe.  It is repaired by the hypothesis the
model violates.  `X = {t}` is not closed under inversion, and
`OsinTheorem54SepSymmetric.exists_symmetric_base` shows that no generality is
lost by assuming it is --- the failure is confined to the finite set `X ∩ H_λ`,
and Dahmani--Guirardel--Osin's Corollary 4.27 absorbs it.  So the honest form of
the field is `sep_comm` **for a base closed under inversion**, which is the
setting Osin works in throughout, his `Γ(G, X ⊔ ℋ)` being a graph with unoriented
edges.  A construction of `SepData` should symmetrise `X` first; the enlarged
base `Y` Osin builds is symmetric by construction, so the field is unaffected at
the point where `SepData` is consumed.

The model is degenerate --- `H = G` --- which is what makes it cheap.  The same
failure occurs at a non-degenerate family: in `G = ⟨t⟩ ∗ ⟨s⟩` with `H = ⟨t⟩` and
`X = {s, s⁻¹, t}`, again `d̂(1,t) ≤ 1` while a negative power of `t` cannot be
reached by an avoiding path.  That example is not formalised here; the degenerate
one refutes the field as stated, `SepDataStatement` quantifying over every
hyperbolically embedded family.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

section Model

variable {G : Type u} [Group G]

/-- **The model**: base `{t}`, family the whole group, one component. -/
def oneLetterRelGenSet (t : G) : RelGenSet G Unit where
  base := {t}
  fam := fun _ => ⊤
  symmetricGenerating := by
    constructor
    · intro x _
      exact Or.inr (Set.mem_iUnion.mpr ⟨(), Subgroup.mem_top x⁻¹⟩)
    · refine eq_top_iff.mpr ?_
      intro x _
      exact Subgroup.subset_closure
        (Or.inr (Set.mem_iUnion.mpr ⟨(), Subgroup.mem_top x⟩))

/-- Every element is a letter: the family is everything. -/
theorem mem_alphabet_oneLetter (t g : G) :
    g ∈ (oneLetterRelGenSet t).alphabet.carrier :=
  Or.inr (Set.mem_iUnion.mpr ⟨(), Subgroup.mem_top g⟩)

/-- `Γ(G, X ⊔ H)` has diameter one. -/
theorem dist_le_one_oneLetter (t : G)
    (p q : Cayley (oneLetterRelGenSet t).alphabet) : dist p q ≤ (1 : ℝ) := by
  have hnorm : wordDist (oneLetterRelGenSet t).alphabet.carrier
      (Cayley.val p) (Cayley.val q) ≤ 1 :=
    wordNorm_le_one_of_mem (mem_alphabet_oneLetter t _)
  show ((wordDist (oneLetterRelGenSet t).alphabet.carrier
    (Cayley.val p) (Cayley.val q) : ℕ) : ℝ) ≤ 1
  exact_mod_cast hnorm

/-- **An avoiding path spells a nonnegative power of `t`.**

Every vertex lies in `H = G`, so the avoidance condition forbids an `H`-letter at
every vertex, and each letter is the single base letter `t`. -/
theorem listVal_eq_pow (t : G) :
    ∀ (w : List (RelLetter G Unit)) (v : G),
      (∀ a ∈ w, (oneLetterRelGenSet t).IsLetter a) →
        AvoidsFrom (oneLetterRelGenSet t).fam () w v →
          RelLetter.listVal w = t ^ w.length := by
  intro w
  induction w with
  | nil =>
      intro _ _ _
      rw [RelLetter.listVal_nil, List.length_nil, pow_zero]
  | cons a s ih =>
      intro v hlet hav
      obtain ⟨hhead, htail⟩ := hav
      have hnc : ¬ a.IsCompOf () := fun hc => hhead ⟨hc, Subgroup.mem_top v⟩
      have hval : a.val = t := by
        cases a with
        | base x =>
            have hx : x ∈ ({t} : Set G) := hlet _ List.mem_cons_self
            exact Set.mem_singleton_iff.mp hx
        | comp mu y => exact absurd (Subsingleton.elim mu ()) hnc
      rw [listVal_cons, hval,
        ih (v * a.val) (fun b hb => hlet b (List.mem_cons_of_mem a hb)) htail,
        List.length_cons]
      group

/-- So every relative ball is a set of nonnegative powers of `t`. -/
theorem relBall_subset_powers (t : G) (n : ℕ) :
    (oneLetterRelGenSet t).relBall () n
      ⊆ (fun k : ℕ => t ^ k) '' (↑(Finset.range (n + 1)) : Set ℕ) := by
  rintro h ⟨-, w, hlet, hval, hav, hlen⟩
  refine ⟨w.length, Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega)), ?_⟩
  show t ^ w.length = h
  rw [← listVal_eq_pow t w 1 hlet hav]
  exact hval

/-- Local finiteness. -/
theorem locallyFinite_oneLetter (t : G) (lam : Unit) (n : ℕ) :
    ((oneLetterRelGenSet t).relBall lam n).Finite := by
  cases lam
  exact Set.Finite.subset
    (((Finset.range (n + 1)).finite_toSet).image _) (relBall_subset_powers t n)

/-- **The model is hyperbolically embedded.**  Bounded, hence hyperbolic; and
locally finite because the avoidance condition confines avoiding paths to the
positive powers of `t`. -/
theorem isHyperbolicallyEmbedded_oneLetter (t : G) :
    (oneLetterRelGenSet t).IsHyperbolicallyEmbedded where
  hyperbolic := ⟨1, isHyperbolicSpace_of_bounded (dist_le_one_oneLetter t)⟩
  locallyFinite := locallyFinite_oneLetter t

/-- **No negative power of `t` is reachable by an avoiding path.** -/
theorem inv_notMem_relBall (t : G) (ht : ¬ IsOfFinOrder t) (n : ℕ) :
    t⁻¹ ∉ (oneLetterRelGenSet t).relBall () n := by
  intro hmem
  obtain ⟨k, -, hk⟩ := relBall_subset_powers t n hmem
  have hk' : t ^ k = t⁻¹ := hk
  have h1 : t ^ (k + 1) = 1 := by
    rw [pow_succ, hk', inv_mul_cancel]
  exact ht (isOfFinOrder_iff_pow_eq_one.mpr ⟨k + 1, by omega, h1⟩)

/-! ## The two directions of one edge -/

/-- `S(1,t;D) = ∅`: the geodesic from `1` to `t` penetrates only inside the
radius-one ball, `t` being an `X`-letter. -/
theorem sepSet_one_t (t : G) {Dc : ℕ} (hDc : 1 ≤ Dc) :
    sepSet (oneLetterRelGenSet t) () Dc 1 t
      = (∅ : Set (G ⧸ (oneLetterRelGenSet t).fam ())) :=
  sepSet_eq_empty_of_mem_base (oneLetterRelGenSet t) () hDc rfl

/-- `S(t,1;D) ≠ ∅`: the only geodesic from `t` to `1` is the `H`-letter `t⁻¹`,
whose span lies in no ball. -/
theorem mem_sepSet_t_one (t : G) (ht : ¬ IsOfFinOrder t) (Dc : ℕ) :
    (QuotientGroup.mk t : G ⧸ (oneLetterRelGenSet t).fam ())
      ∈ sepSet (oneLetterRelGenSet t) () Dc t 1 := by
  have htne : t ≠ 1 := by
    intro h
    apply ht
    rw [h]
    exact IsOfFinOrder.one
  have htinv : t⁻¹ ≠ 1 := fun h => htne (inv_eq_one.mp h)
  have hnorm1 : wordNorm (oneLetterRelGenSet t).alphabet.carrier t⁻¹ = 1 := by
    have hle : wordNorm (oneLetterRelGenSet t).alphabet.carrier t⁻¹ ≤ 1 :=
      wordNorm_le_one_of_mem (mem_alphabet_oneLetter t t⁻¹)
    have hge : 1 ≤ wordNorm (oneLetterRelGenSet t).alphabet.carrier t⁻¹ :=
      one_le_wordNorm (oneLetterRelGenSet t).symmetricGenerating htinv
    omega
  -- the geodesic word
  have hlet : ∀ a ∈ [RelLetter.comp () t⁻¹], (oneLetterRelGenSet t).IsLetter a := by
    intro a ha
    have hae : a = RelLetter.comp () t⁻¹ := List.eq_of_mem_singleton ha
    rw [hae]
    exact Subgroup.mem_top t⁻¹
  have hprod : t * RelLetter.listVal [RelLetter.comp (Λ := Unit) () t⁻¹] = 1 := by
    rw [listVal_cons, RelLetter.listVal_nil, mul_one]
    exact mul_inv_cancel t
  have hlen : [RelLetter.comp (Λ := Unit) () t⁻¹].length
      = wordDist (oneLetterRelGenSet t).alphabet.carrier t 1 := by
    show (1 : ℕ) = wordNorm (oneLetterRelGenSet t).alphabet.carrier (t⁻¹ * 1)
    rw [mul_one]
    exact hnorm1.symm
  -- the component
  have hcomp : IsComp () [RelLetter.comp (Λ := Unit) () t⁻¹] 0 1 := by
    refine ⟨by omega, by simp, ?_, ?_, ?_⟩
    · intro j _ hj1 _
      have hj0 : j = 0 := by omega
      subst hj0
      show (RelLetter.comp (Λ := Unit) () t⁻¹).IsCompOf ()
      rfl
    · intro j hj
      exact absurd hj (by omega)
    · intro hk
      simp at hk
  -- the span
  have hspan : (vertex t [RelLetter.comp (Λ := Unit) () t⁻¹] 0)⁻¹ *
      vertex t [RelLetter.comp (Λ := Unit) () t⁻¹] 1 = t⁻¹ := by
    show t⁻¹ * (t * t⁻¹) = t⁻¹
    group
  exact ⟨[RelLetter.comp () t⁻¹], 0, 1, ⟨hlet, hprod, hlen⟩,
    ⟨hcomp, by rw [hspan]; exact inv_notMem_relBall t ht Dc⟩, rfl⟩

/-- **`sepSet` is not symmetric.** -/
theorem not_sepSet_comm (t : G) (ht : ¬ IsOfFinOrder t) {Dc : ℕ} (hDc : 1 ≤ Dc) :
    sepSet (oneLetterRelGenSet t) () Dc 1 t
      ≠ sepSet (oneLetterRelGenSet t) () Dc t 1 := by
  intro heq
  have hmem := mem_sepSet_t_one t ht Dc
  rw [← heq, sepSet_one_t t hDc] at hmem
  exact absurd hmem (Set.notMem_empty _)

end Model

/-- **`SepData.sep_comm` fails for the separating-coset count**, at `Type 0`, for
the generator of `ℤ`.

So a `SepData` cannot take `sep := sepCard` unless the base is closed under
inversion; see the module docstring for what the field must become.  The
infinite-order computation is the one of
`Sofic.SoundIterateInstances.not_isOfFinOrder_generator`, reproved here rather
than imported, that module belonging to an unrelated development. -/
theorem not_forall_sepSet_comm :
    ¬ ∀ (G : Type) [Group G] (D : RelGenSet G Unit) (Dc : ℕ), 1 ≤ Dc →
        D.IsHyperbolicallyEmbedded →
          ∀ f g : G, sepSet D () Dc f g = sepSet D () Dc g f := by
  intro hcon
  have hinf : ¬ IsOfFinOrder (Multiplicative.ofAdd (1 : ℤ)) := by
    rw [isOfFinOrder_iff_pow_eq_one]
    rintro ⟨n, hn, hpow⟩
    rw [← ofAdd_nsmul, ofAdd_eq_one, Int.nsmul_eq_mul, mul_one] at hpow
    omega
  refine not_sepSet_comm (Multiplicative.ofAdd (1 : ℤ)) hinf (Dc := 1)
    (le_refl 1) ?_
  exact hcon (Multiplicative ℤ)
    (oneLetterRelGenSet (Multiplicative.ofAdd (1 : ℤ))) 1 (le_refl 1)
    (isHyperbolicallyEmbedded_oneLetter _) 1 (Multiplicative.ofAdd (1 : ℤ))

end OsinComponents
end GGT
end GroupApproximation
