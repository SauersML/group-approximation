import GroupApproximation.Algebra.PeirceUnitFactorization

/-!
# Item (a) of the printed proof, in full

`non_mf_groups_exist.tex`, proof of `thm:mf-quotient-units`, item (a)
(tex line 1210):

> There are orthogonal idempotents `e_1, …, e_m` with sum `1`, `m ≥ 4`, such
> that `e_1, …, e_{m-1}` are pairwise equivalent and `e_m` is equivalent to an
> idempotent `f ≤ e_1`.  Then `R` is the ring of `m × m` matrices over
> `T = e_1Re_1`, with identity `diag(1_T, …, 1_T, f)`, whose last column has
> entries in `Tf` and whose last row has entries in `fT`, and every unit `u` of
> `R` factors as `u = gvh` with `g` and `h` products of elementary matrices
> `e_{ij}(x)` of this matrix ring and `v = e_1 + (1-e_1)v(1-e_1)`.

`PrintedItemA` below is that whole sentence, existential and all, as one closed
proposition, and `printedItemA` proves it for every purely infinite simple ring
and every `m ≥ 4`.

## Where each clause comes from

* **The decomposition.**  `Algebra/PurelyInfiniteUnitFamily.lean` supplies
  `m - 1` orthogonal idempotents each equivalent to `1`; `peirceBlocks` adds the
  remainder `1 - ∑ r j` as the last block.  So the first `m - 1` blocks are
  pairwise equivalent because each is equivalent to `1`, and the last block is
  equivalent to `f = s (e_m) t ≤ e_1`, the copy of it pushed into `e_1` along
  the isometry that witnesses `e_1 ~ 1`.
* **The matrix identification.**  `Algebra/PeirceTwistedMatrixRing.lean`, applied
  to exactly this data.
* **The factorisation.**  `Algebra/PeirceUnitFactorization.lean`, instantiated
  at `N = peirceElementarySubgroup`.  The two transvection families it asks for
  are `Algebra/PeirceElementaryUnits.lean`'s `peirceOneAdd_of_left` and
  `peirceOneAdd_of_right`: a transvection along a whole block row is already a
  product of single-block elementary matrices.

## The one place this is stronger than printed

Nothing is weakened.  The printed `f ≤ e_1` is not taken to be `e_1` itself,
which would satisfy the printed hypothesis while collapsing the twisting the
sentence is about; `f` here is a genuine copy of the last block inside `e_1`.
-/

namespace GroupApproximation
namespace MFQuotientUnits

open Peirce

variable {R : Type} [Ring R]

/-! ### A frame from two orthogonal idempotents equivalent to `1` -/

/-- Two orthogonal idempotents, each equivalent to `1`, carry a frame whose
corners are exactly those idempotents. -/
theorem exists_frame_of_two (r : Fin 2 → R)
    (hidem : ∀ i, IsIdempotentElem (r i))
    (hortho : ∀ i j : Fin 2, i ≠ j → r i * r j = 0)
    (hequiv : ∀ i, IsEquivalentIdempotent R (r i) 1) :
    ∃ F : Frame R, ∀ i, F.e i = r i := by
  have hc : ∀ i : Fin 2, ∃ s t : R, t * s = 1 ∧ s * t = r i := by
    intro i
    obtain ⟨s, t, hts, hst, -, -, -, -⟩ :=
      exists_normalized_isometry IsIdempotentElem.one (hidem i)
        (one_mul _) (mul_one _) (hequiv i).symm
    exact ⟨s, t, hts, hst⟩
  choose s t hts hst using hc
  refine ⟨⟨s, t, hts, ?_⟩, fun i => hst i⟩
  intro i j hij
  have hs : r j * s j = s j := by rw [← hst j, mul_assoc, hts j, mul_one]
  have ht : t i * r i = t i := by rw [← hst i, ← mul_assoc, hts i, one_mul]
  calc t i * s j = (t i * r i) * (r j * s j) := by rw [ht, hs]
    _ = t i * (r i * r j) * s j := by noncomm_ring
    _ = 0 := by rw [hortho i j hij]; simp

/-! ### The printed decomposition -/

section Blocks

variable {n : ℕ} (r : Fin n → R)

/-- **The printed `e_1, …, e_m`**: the given orthogonal copies of `1`, together
with the remainder as the last block. -/
def peirceBlocks : Fin (n + 1) → R := fun i =>
  if h : (i : ℕ) < n then r ⟨i, h⟩ else 1 - ∑ j, r j

theorem peirceBlocks_castSucc (j : Fin n) : peirceBlocks r j.castSucc = r j := by
  have h : ((j.castSucc : Fin (n + 1)) : ℕ) < n := by simp
  simp only [peirceBlocks, dif_pos h]
  congr 1

theorem peirceBlocks_last : peirceBlocks r (Fin.last n) = 1 - ∑ j, r j := by
  have h : ¬ ((Fin.last n : Fin (n + 1)) : ℕ) < n := by simp
  simp only [peirceBlocks, dif_neg h]

theorem peirceBlocks_sum : ∑ i, peirceBlocks r i = 1 := by
  rw [Fin.sum_univ_castSucc, peirceBlocks_last,
    Finset.sum_congr rfl fun j _ => peirceBlocks_castSucc r j]
  abel

variable (hidem : ∀ i, IsIdempotentElem (r i))
  (hortho : ∀ i j : Fin n, i ≠ j → r i * r j = 0)

include hidem hortho

theorem r_mul_sum (i : Fin n) : r i * (∑ j, r j) = r i := by
  rw [Finset.mul_sum, Finset.sum_eq_single i]
  · exact hidem i
  · intro j _ hji; exact hortho i j (Ne.symm hji)
  · intro h; exact absurd (Finset.mem_univ i) h

theorem sum_mul_r (i : Fin n) : (∑ j, r j) * r i = r i := by
  rw [Finset.sum_mul, Finset.sum_eq_single i]
  · exact hidem i
  · intro j _ hji; exact hortho j i hji
  · intro h; exact absurd (Finset.mem_univ i) h

theorem sum_r_isIdempotentElem : (∑ j, r j) * (∑ j, r j) = ∑ j, r j := by
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => r_mul_sum r hidem hortho i

theorem peirceBlocks_isIdempotentElem :
    ∀ i, IsIdempotentElem (peirceBlocks r i) := by
  intro i
  rcases eq_or_ne i (Fin.last n) with rfl | hi
  · rw [peirceBlocks_last]
    show (1 - ∑ j, r j) * (1 - ∑ j, r j) = 1 - ∑ j, r j
    calc (1 - ∑ j, r j) * (1 - ∑ j, r j)
        = 1 - (∑ j, r j) - (∑ j, r j) + (∑ j, r j) * (∑ j, r j) := by noncomm_ring
      _ = 1 - ∑ j, r j := by rw [sum_r_isIdempotentElem r hidem hortho]; abel
  · obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
    rw [peirceBlocks_castSucc]
    exact hidem j

theorem peirceBlocks_orthogonal : ∀ i j : Fin (n + 1), i ≠ j →
    peirceBlocks r i * peirceBlocks r j = 0 := by
  intro i j hij
  rcases eq_or_ne i (Fin.last n) with rfl | hi
  · obtain ⟨b, rfl⟩ := Fin.eq_castSucc_of_ne_last (Ne.symm hij)
    rw [peirceBlocks_last, peirceBlocks_castSucc, sub_mul, one_mul,
      sum_mul_r r hidem hortho b, sub_self]
  · obtain ⟨a, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
    rcases eq_or_ne j (Fin.last n) with rfl | hj
    · rw [peirceBlocks_castSucc, peirceBlocks_last, mul_sub, mul_one,
        r_mul_sum r hidem hortho a, sub_self]
    · obtain ⟨b, rfl⟩ := Fin.eq_castSucc_of_ne_last hj
      rw [peirceBlocks_castSucc, peirceBlocks_castSucc]
      exact hortho a b fun h => hij (by rw [h])

variable (hequiv : ∀ i, IsEquivalentIdempotent R (r i) 1)

include hequiv

omit hortho in
theorem peirceBlocks_pairwise_equivalent : ∀ i j : Fin (n + 1),
    i ≠ Fin.last n → j ≠ Fin.last n →
      IsEquivalentIdempotent R (peirceBlocks r i) (peirceBlocks r j) := by
  intro i j hi hj
  obtain ⟨a, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
  obtain ⟨b, rfl⟩ := Fin.eq_castSucc_of_ne_last hj
  rw [peirceBlocks_castSucc, peirceBlocks_castSucc]
  exact IsEquivalentIdempotent.trans (hidem a) (hidem b) (hequiv a)
    (hequiv b).symm

end Blocks

/-! ### The printed sentence -/

/-- **Item (a) of the printed proof, as a closed proposition.**

The printed `m ≥ 4` is carried, even though the matrix identification does not
need it, because the sentence states it. -/
def PrintedItemA : Prop :=
  ∀ (R : Type) [Ring R], IsPurelyInfiniteSimpleRing R →
    ∀ m : ℕ, 4 ≤ m →
      ∃ (e : Fin m → R) (hidem : ∀ i, IsIdempotentElem (e i)) (i₀ last : Fin m)
        (f : R) (hfi : IsIdempotentElem f) (hfle : IdempotentLE f (e i₀)),
        i₀ ≠ last ∧
        (∀ i j : Fin m, i ≠ j → e i * e j = 0) ∧
        (∑ i, e i = 1) ∧
        (∀ i j : Fin m, i ≠ last → j ≠ last →
          IsEquivalentIdempotent R (e i) (e j)) ∧
        IsEquivalentIdempotent R (e last) f ∧
        Nonempty (R ≃+*
          Corner (Matrix (Fin m) (Fin m) (Corner R (e i₀) (hidem i₀)))
            (twistedIdentity (hidem i₀) hfle last)
            (isIdempotentElem_twistedIdentity (hidem i₀) hfi hfle last)) ∧
        ∀ u : Rˣ, ∃ v : Rˣ,
          FactorsThrough (peirceElementarySubgroup e) u v ∧
          (v : R) = e i₀ + (1 - e i₀) * (v : R) * (1 - e i₀)

/-- **The printed sentence, proved.** -/
theorem printedItemA : PrintedItemA := by
  intro R _ hR m hm
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have h2 : 2 ≤ n := by omega
  obtain ⟨r, hridem, hrorth, hrequiv⟩ := exists_orthogonal_unit_family hR n
  -- the blocks and their printed properties
  have hidem := peirceBlocks_isIdempotentElem r hridem hrorth
  have horth := peirceBlocks_orthogonal r hridem hrorth
  have hsum := peirceBlocks_sum r
  have hpair := peirceBlocks_pairwise_equivalent r hridem hrequiv
  -- the two frame indices, and the frame
  have hidx : ∀ i j : Fin 2, i ≠ j →
      r (Fin.castLE h2 i) * r (Fin.castLE h2 j) = 0 := fun i j hij =>
    hrorth _ _ fun h => hij (Fin.castLE_injective h2 h)
  obtain ⟨F, hF⟩ := exists_frame_of_two (fun i => r (Fin.castLE h2 i))
    (fun i => hridem _) hidx (fun i => hrequiv _)
  have hFe : ∀ i : Fin 2,
      F.e i = peirceBlocks r (Fin.castSucc (Fin.castLE h2 i)) := fun i =>
    (hF i).trans (peirceBlocks_castSucc r (Fin.castLE h2 i)).symm
  -- the distinguished indices
  have hne : Fin.castSucc (Fin.castLE h2 (1 : Fin 2)) ≠ Fin.last n :=
    ne_of_lt (Fin.castSucc_lt_last _)
  -- the sub-idempotent `f ≤ e_1` equivalent to the last block
  obtain ⟨s, t, hts, hst, -, -, -, -⟩ :=
    exists_normalized_isometry IsIdempotentElem.one (hridem (Fin.castLE h2 1))
      (one_mul _) (mul_one _) (hrequiv (Fin.castLE h2 1)).symm
  have hL : IsIdempotentElem (peirceBlocks r (Fin.last n)) := hidem _
  have hLL : peirceBlocks r (Fin.last n) * peirceBlocks r (Fin.last n)
      = peirceBlocks r (Fin.last n) := hL
  have hblock1 : peirceBlocks r (Fin.castSucc (Fin.castLE h2 (1 : Fin 2)))
      = s * t := by rw [peirceBlocks_castSucc, hst]
  have hfi : IsIdempotentElem (s * peirceBlocks r (Fin.last n) * t) := by
    show s * peirceBlocks r (Fin.last n) * t * (s * peirceBlocks r (Fin.last n) * t)
      = s * peirceBlocks r (Fin.last n) * t
    calc s * peirceBlocks r (Fin.last n) * t * (s * peirceBlocks r (Fin.last n) * t)
        = s * (peirceBlocks r (Fin.last n) * (t * s) *
            peirceBlocks r (Fin.last n)) * t := by noncomm_ring
      _ = s * peirceBlocks r (Fin.last n) * t := by
          rw [hts, mul_one, hLL]
  have hfle : IdempotentLE (s * peirceBlocks r (Fin.last n) * t)
      (peirceBlocks r (Fin.castSucc (Fin.castLE h2 (1 : Fin 2)))) := by
    constructor
    · rw [hblock1]
      calc s * t * (s * peirceBlocks r (Fin.last n) * t)
          = s * (t * s) * peirceBlocks r (Fin.last n) * t := by noncomm_ring
        _ = s * peirceBlocks r (Fin.last n) * t := by rw [hts, mul_one]
    · rw [hblock1]
      calc s * peirceBlocks r (Fin.last n) * t * (s * t)
          = s * peirceBlocks r (Fin.last n) * (t * s) * t := by noncomm_ring
        _ = s * peirceBlocks r (Fin.last n) * t := by rw [hts, mul_one]
  have hlastequiv : IsEquivalentIdempotent R (peirceBlocks r (Fin.last n))
      (s * peirceBlocks r (Fin.last n) * t) := by
    refine ⟨peirceBlocks r (Fin.last n) * t, s * peirceBlocks r (Fin.last n),
      ?_, ?_⟩
    · calc peirceBlocks r (Fin.last n)
          = peirceBlocks r (Fin.last n) * peirceBlocks r (Fin.last n) := hLL.symm
        _ = peirceBlocks r (Fin.last n) * (t * s) * peirceBlocks r (Fin.last n) := by
            rw [hts, mul_one]
        _ = peirceBlocks r (Fin.last n) * t * (s * peirceBlocks r (Fin.last n)) := by
            noncomm_ring
    · calc s * peirceBlocks r (Fin.last n) * t
          = s * (peirceBlocks r (Fin.last n) * peirceBlocks r (Fin.last n)) * t := by
            rw [hLL]
        _ = s * peirceBlocks r (Fin.last n) * (peirceBlocks r (Fin.last n) * t) := by
            noncomm_ring
  -- the two transvection families, at the printed elementary subgroup
  have hupper : UpperFamily F (peirceElementarySubgroup (peirceBlocks r)) := by
    intro i x hx hxx
    rw [hFe i] at hx hxx
    exact peirceOneAdd_of_left (peirceBlocks r) hidem horth hsum _ hx hxx
  have hlower : LowerFamily F (peirceElementarySubgroup (peirceBlocks r)) := by
    intro i x hx hxx
    rw [hFe i] at hx hxx
    exact peirceOneAdd_of_right (peirceBlocks r) hidem horth hsum _ hxx hx
  refine ⟨peirceBlocks r, hidem, Fin.castSucc (Fin.castLE h2 (1 : Fin 2)),
    Fin.last n, s * peirceBlocks r (Fin.last n) * t, hfi, hfle, hne, horth,
    hsum, fun i j hi hj => hpair i j hi hj, hlastequiv,
    exists_ringEquiv_twistedMatrixCorner (peirceBlocks r) hidem horth hsum _ _
      hne (fun i j hi hj => hpair i j hi hj) _ hfi hfle hlastequiv _, ?_⟩
  intro u
  obtain ⟨v, hfac, hsupp⟩ := exists_supported_factorization F hR hupper hlower u
  refine ⟨v, hfac, ?_⟩
  rw [← hFe 1]
  exact hsupp

end MFQuotientUnits
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.MFQuotientUnits.exists_frame_of_two
#audit_axioms GroupApproximation.MFQuotientUnits.peirceBlocks_isIdempotentElem
#audit_axioms GroupApproximation.MFQuotientUnits.peirceBlocks_orthogonal
#audit_closed_axioms GroupApproximation.MFQuotientUnits.printedItemA
