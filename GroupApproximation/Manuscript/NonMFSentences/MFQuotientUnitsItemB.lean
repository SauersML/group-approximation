import GroupApproximation.Manuscript.OneSidedMFRadical.MFQuotientUnitsStepOne
import GroupApproximation.Algebra.PurelyInfiniteUnitFamily
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:mf-quotient-units`, item (b), at the printed objects

`non_mf_groups_exist.tex`, proof of Theorem `thm:mf-quotient-units` (tex 1268–1274):

> (b) For a nonzero idempotent `e` and `n ≥ 2` there are an idempotent `f < e` equivalent
> to `e` and orthogonal idempotents `r_2, …, r_n ≤ e - f`, each equivalent to `1`, such that,
> with `r_1 = 1 - e + f` and `P = r_1 + ⋯ + r_n`, some ring isomorphism `θ : M_n(R) → PRP`
> sends `diag(v,1,…,1)` to `(1-e)v(1-e) + f + r_2 + ⋯ + r_n` for every unit
> `v = e + (1-e)v(1-e)`.

The census row of this sentence cites `agpStepOne`, which proves the consumed conclusion by
a two-coordinate Whitehead route and never builds `f`, the `r_i`, `P` or `θ`.  This module
builds every printed object and proves every printed clause (`manuscriptSentence_itemB`).

## The construction

* `e = f + g` with `f ~ e`, `g ≠ 0` (Ara--Goodearl--Pardo Proposition 1.5,
  `isInfiniteIdempotent_of_ne_zero`), normalized to `T₀S₀ = e`, `S₀T₀ = f` inside `eRe`.
* A sandwich `x g y = 1` (`exists_sandwich_of_isPurelyInfiniteSimpleRing`) makes
  `g y` and `x g` an isometry pair below `g`, and it carries an orthogonal family of `n`
  idempotents equivalent to `1` (`exists_orthogonal_unit_family`) below `g = e - f`.
* The coordinate `1` uses `s₁ = (1-e) + S₀`, `t₁ = (1-e) + T₀`, so `t₁s₁ = 1`,
  `s₁t₁ = 1 - e + f = r_1` and `s₁ v t₁ = (1-e)v(1-e) + f` for `v = e + (1-e)v(1-e)`.
* `θ(A) = ∑ s_i A_ij t_j` is a ring isomorphism onto the corner at `P = ∑ s_i t_i = ∑ r_i`
  (`matrixCornerEquiv`: injective by `t_i θ(A) s_j = A_ij`, surjective by
  `θ((t_i x s_j)_{ij}) = P x P`).

Nothing is assumed.
-/

namespace GroupApproximation
namespace MFQuotientUnitsItemB

open MFQuotientUnits

section Embedding

variable {R : Type} [Ring R] {n : ℕ} {s t : Fin n → R}

/-- The matrix coordinates of the embedding are recovered by `t_i · θ(A) · s_j`. -/
theorem t_mul_matrixEmbed_mul_s (hts : ∀ i, t i * s i = 1)
    (hcross : ∀ i j : Fin n, i ≠ j → t i * s j = 0) (A : Matrix (Fin n) (Fin n) R)
    (i j : Fin n) : t i * matrixEmbed s t A * s j = A i j := by
  calc t i * matrixEmbed s t A * s j
      = ∑ k, ∑ l, t i * s k * A k l * (t l * s j) := by
        unfold matrixEmbed
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun l _ => ?_
        noncomm_ring
    _ = t i * s i * A i j * (t j * s j) := by
        rw [Finset.sum_eq_single i]
        · rw [Finset.sum_eq_single j]
          · intro l _ hl
            rw [hcross l j hl, mul_zero]
          · intro h
            exact absurd (Finset.mem_univ j) h
        · intro k _ hk
          refine Finset.sum_eq_zero fun l _ => ?_
          rw [hcross i k (Ne.symm hk), zero_mul, zero_mul]
        · intro h
          exact absurd (Finset.mem_univ i) h
    _ = A i j := by rw [hts i, hts j, one_mul, mul_one]

/-- The embedding of the coordinate matrix `(t_i x s_j)` is `P x P`. -/
theorem matrixEmbed_coords (x : R) :
    matrixEmbed s t (Matrix.of fun i j => t i * x * s j) =
      matrixWitnessSum s t * x * matrixWitnessSum s t := by
  unfold matrixEmbed matrixWitnessSum
  rw [Finset.sum_mul, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.of_apply]
  noncomm_ring

/-- The embedding of a diagonal matrix. -/
theorem matrixEmbed_diagonal (d : Fin n → R) :
    matrixEmbed s t (Matrix.diagonal d) = ∑ i, s i * d i * t i := by
  unfold matrixEmbed
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [Matrix.diagonal_apply_eq]
  · intro j _ hj
    rw [Matrix.diagonal_apply_ne d (Ne.symm hj), mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- **The printed `θ : M_n(R) → PRP`.**  The matrix embedding of a complete family of
isometry pairs is a ring isomorphism onto the corner at `P = ∑ s_i t_i`. -/
noncomputable def matrixCornerEquiv (hts : ∀ i, t i * s i = 1)
    (hcross : ∀ i j : Fin n, i ≠ j → t i * s j = 0) :
    Matrix (Fin n) (Fin n) R ≃+*
      Corner R (matrixWitnessSum s t) (isIdempotentElem_matrixWitnessSum hts hcross) :=
  RingEquiv.ofBijective (matrixCornerHom s t hts hcross)
    ⟨fun A B hAB => by
      ext i j
      have h := congrArg (fun z : Corner R (matrixWitnessSum s t)
        (isIdempotentElem_matrixWitnessSum hts hcross) => t i * (z : R) * s j) hAB
      change t i * matrixEmbed s t A * s j = t i * matrixEmbed s t B * s j at h
      rwa [t_mul_matrixEmbed_mul_s hts hcross, t_mul_matrixEmbed_mul_s hts hcross] at h,
     fun z => ⟨Matrix.of fun i j => t i * (z : R) * s j, corner_ext (by
      change matrixEmbed s t (Matrix.of fun i j => t i * (z : R) * s j) = (z : R)
      rw [matrixEmbed_coords, z.2.1, z.2.2])⟩⟩

@[simp] theorem coe_matrixCornerEquiv (hts : ∀ i, t i * s i = 1)
    (hcross : ∀ i j : Fin n, i ≠ j → t i * s j = 0) (A : Matrix (Fin n) (Fin n) R) :
    ((matrixCornerEquiv hts hcross A : Corner R (matrixWitnessSum s t)
      (isIdempotentElem_matrixWitnessSum hts hcross)) : R) = matrixEmbed s t A := rfl

end Embedding

/-- **Printed item (b) (tex 1268–1274), every clause, at the printed objects.**  For a
nonzero idempotent `e` of a countable purely infinite simple ring `R` and `n ≥ 2` there are
an idempotent `f < e` equivalent to `e`, and idempotents `r_1, …, r_n` (index `0` is the
printed `r_1`), pairwise orthogonal, with `r_2, …, r_n ≤ e - f` each equivalent to `1` and
`r_1 = 1 - e + f`, such that with `P = r_1 + ⋯ + r_n` some ring isomorphism
`θ : M_n(R) → PRP` sends `diag(v,1,…,1)` to `(1-e)v(1-e) + f + r_2 + ⋯ + r_n` for every
unit `v = e + (1-e)v(1-e)`. -/
def PrintedItemB : Prop :=
  ∀ (R : Type) [Ring R] [Countable R], IsPurelyInfiniteSimpleRing R →
    ∀ (e : R), IsIdempotentElem e → e ≠ 0 → ∀ (n : ℕ) (hn : 2 ≤ n),
      ∃ (f : R) (r : Fin n → R),
        IsIdempotentElem f ∧ IdempotentLE f e ∧ f ≠ e ∧ IsEquivalentIdempotent R f e ∧
        (∀ i, IsIdempotentElem (r i)) ∧ (∀ i j, i ≠ j → r i * r j = 0) ∧
        (∀ i, i ≠ (⟨0, by omega⟩ : Fin n) →
          IdempotentLE (r i) (e - f) ∧ IsEquivalentIdempotent R (r i) 1) ∧
        r ⟨0, by omega⟩ = 1 - e + f ∧
        ∃ (P : R) (hP : IsIdempotentElem P)
          (θ : Matrix (Fin n) (Fin n) R ≃+* Corner R P hP),
          P = ∑ i, r i ∧
          ∀ v : Rˣ, (v : R) = e + (1 - e) * (v : R) * (1 - e) →
            ((θ (RankNElimination.diagAt (⟨0, by omega⟩ : Fin n) v :
                Matrix (Fin n) (Fin n) R) : Corner R P hP) : R) =
              (1 - e) * (v : R) * (1 - e) + f +
                ∑ i ∈ Finset.univ.erase (⟨0, by omega⟩ : Fin n), r i

theorem manuscriptSentence_itemB : PrintedItemB := by
  intro R _ _ hR e he hne n hn
  obtain ⟨f, g, hf, hg, hfg, hgf, hsum, hequiv, hgne⟩ :=
    isInfiniteIdempotent_of_ne_zero hR he hne
  have hef : e * f = f := by rw [hsum, add_mul, hf, hgf, add_zero]
  have hfe : f * e = f := by rw [hsum, mul_add, hf, hfg, add_zero]
  have heg : e * g = g := by rw [hsum, add_mul, hfg, hg, zero_add]
  have hge : g * e = g := by rw [hsum, mul_add, hgf, hg, zero_add]
  have hgdef : e - f = g := by rw [hsum]; abel
  obtain ⟨S₀, T₀, hTS, hST, heS, hSe, heT, hTe⟩ :=
    exists_normalized_isometry he hf hef hfe hequiv
  have hfS : f * S₀ = S₀ := by rw [← hST, mul_assoc, hTS, hSe]
  have hTf : T₀ * f = T₀ := by rw [← hST, ← mul_assoc, hTS, heT]
  have hgS : g * S₀ = 0 := by rw [← hgdef, sub_mul, heS, hfS, sub_self]
  have hTg : T₀ * g = 0 := by rw [← hgdef, mul_sub, hTe, hTf, sub_self]
  have hoe : IsIdempotentElem (1 - e) := IsIdempotentElem.one_sub he
  have hoeS : (1 - e) * S₀ = 0 := by rw [sub_mul, one_mul, heS, sub_self]
  have hToe : T₀ * (1 - e) = 0 := by rw [mul_sub, mul_one, hTe, sub_self]
  have hoeT : (1 - e) * T₀ = 0 := by rw [sub_mul, one_mul, heT, sub_self]
  have hSoe : S₀ * (1 - e) = 0 := by rw [mul_sub, mul_one, hSe, sub_self]
  have hoef : (1 - e) * f = 0 := by rw [sub_mul, one_mul, hef, sub_self]
  have hfoe : f * (1 - e) = 0 := by rw [mul_sub, mul_one, hfe, sub_self]
  have hoeg : (1 - e) * g = 0 := by rw [sub_mul, one_mul, heg, sub_self]
  have hgoe : g * (1 - e) = 0 := by rw [mul_sub, mul_one, hge, sub_self]
  have hoee : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he, sub_self]
  obtain ⟨x, y, hxgy⟩ := exists_sandwich_of_isPurelyInfiniteSimpleRing hR hgne
  have hVU : x * g * (g * y) = 1 := by
    calc x * g * (g * y) = x * (g * g) * y := by noncomm_ring
      _ = 1 := by rw [hg, hxgy]
  obtain ⟨r', hr'idem, hr'orth, hr'equiv⟩ := exists_orthogonal_unit_family hR n
  have hr'eq : ∀ i, ∃ p q : R, r' i = p * q ∧ 1 = q * p := hr'equiv
  choose a b hab hba using hr'eq
  have hra : ∀ i, r' i * a i = a i := fun i => by rw [hab i, mul_assoc, ← hba i, mul_one]
  have hbr : ∀ i, b i * r' i = b i := fun i => by rw [hab i, ← mul_assoc, ← hba i, one_mul]
  set i0 : Fin n := ⟨0, by omega⟩
  let s : Fin n → R := fun i => if i = i0 then (1 - e) + S₀ else g * y * a i
  let t : Fin n → R := fun i => if i = i0 then (1 - e) + T₀ else b i * (x * g)
  let r : Fin n → R := fun i => if i = i0 then 1 - e + f else g * y * r' i * (x * g)
  have hts : ∀ i, t i * s i = 1 := by
    intro i
    show (if i = i0 then (1 - e) + T₀ else b i * (x * g)) *
        (if i = i0 then (1 - e) + S₀ else g * y * a i) = 1
    by_cases hi : i = i0
    · rw [if_pos hi, if_pos hi]
      calc ((1 - e) + T₀) * ((1 - e) + S₀)
          = (1 - e) * (1 - e) + (1 - e) * S₀ + T₀ * (1 - e) + T₀ * S₀ := by noncomm_ring
        _ = 1 := by rw [hoe, hoeS, hToe, hTS]; abel
    · rw [if_neg hi, if_neg hi]
      calc b i * (x * g) * (g * y * a i) = b i * (x * g * (g * y)) * a i := by noncomm_ring
        _ = 1 := by rw [hVU, mul_one, ← hba i]
  have hcross : ∀ i j : Fin n, i ≠ j → t i * s j = 0 := by
    intro i j hij
    show (if i = i0 then (1 - e) + T₀ else b i * (x * g)) *
        (if j = i0 then (1 - e) + S₀ else g * y * a j) = 0
    by_cases hi : i = i0
    · have hj : j ≠ i0 := fun h => hij (hi.trans h.symm)
      rw [if_pos hi, if_neg hj]
      calc ((1 - e) + T₀) * (g * y * a j)
          = ((1 - e) * g) * y * a j + (T₀ * g) * y * a j := by noncomm_ring
        _ = 0 := by rw [hoeg, hTg]; simp
    · by_cases hj : j = i0
      · rw [if_neg hi, if_pos hj]
        calc b i * (x * g) * ((1 - e) + S₀)
            = b i * x * (g * (1 - e)) + b i * x * (g * S₀) := by noncomm_ring
          _ = 0 := by rw [hgoe, hgS]; simp
      · rw [if_neg hi, if_neg hj]
        calc b i * (x * g) * (g * y * a j)
            = b i * (x * g * (g * y)) * a j := by noncomm_ring
          _ = b i * r' i * (r' j * a j) := by rw [hVU, mul_one, hbr i, hra j]
          _ = b i * (r' i * r' j) * a j := by noncomm_ring
          _ = 0 := by rw [hr'orth i j hij]; simp
  have hwit : ∀ i, s i * t i = r i := by
    intro i
    show (if i = i0 then (1 - e) + S₀ else g * y * a i) *
        (if i = i0 then (1 - e) + T₀ else b i * (x * g)) =
      (if i = i0 then 1 - e + f else g * y * r' i * (x * g))
    by_cases hi : i = i0
    · rw [if_pos hi, if_pos hi, if_pos hi]
      calc ((1 - e) + S₀) * ((1 - e) + T₀)
          = (1 - e) * (1 - e) + (1 - e) * T₀ + S₀ * (1 - e) + S₀ * T₀ := by noncomm_ring
        _ = 1 - e + f := by rw [hoe, hoeT, hSoe, hST]; abel
    · rw [if_neg hi, if_neg hi, if_neg hi, hab i]
      noncomm_ring
  refine ⟨f, r, hf, ⟨hef, hfe⟩, ?_, hequiv.symm, ?_, ?_, ?_, if_pos rfl, ?_⟩
  · intro hfe'
    apply hgne
    rw [← hgdef, hfe', sub_self]
  · intro i
    show (if i = i0 then 1 - e + f else g * y * r' i * (x * g)) *
        (if i = i0 then 1 - e + f else g * y * r' i * (x * g)) =
      (if i = i0 then 1 - e + f else g * y * r' i * (x * g))
    by_cases hi : i = i0
    · rw [if_pos hi]
      calc (1 - e + f) * (1 - e + f) = (1 - e) * (1 - e) + (1 - e) * f + f * (1 - e) + f * f := by
            noncomm_ring
        _ = 1 - e + f := by rw [hoe, hoef, hfoe, hf, add_zero, add_zero]
    · rw [if_neg hi]
      calc g * y * r' i * (x * g) * (g * y * r' i * (x * g))
          = g * y * (r' i * (x * g * (g * y)) * r' i) * (x * g) := by noncomm_ring
        _ = g * y * r' i * (x * g) := by rw [hVU, mul_one, hr'idem i]
  · intro i j hij
    show (if i = i0 then 1 - e + f else g * y * r' i * (x * g)) *
        (if j = i0 then 1 - e + f else g * y * r' j * (x * g)) = 0
    by_cases hi : i = i0
    · have hj : j ≠ i0 := fun h => hij (hi.trans h.symm)
      rw [if_pos hi, if_neg hj]
      calc (1 - e + f) * (g * y * r' j * (x * g))
          = ((1 - e) * g) * y * r' j * (x * g) + (f * g) * y * r' j * (x * g) := by noncomm_ring
        _ = 0 := by rw [hoeg, hfg]; simp
    · by_cases hj : j = i0
      · rw [if_neg hi, if_pos hj]
        calc g * y * r' i * (x * g) * (1 - e + f)
            = g * y * r' i * x * (g * (1 - e)) + g * y * r' i * x * (g * f) := by noncomm_ring
          _ = 0 := by rw [hgoe, hgf]; simp
      · rw [if_neg hi, if_neg hj]
        calc g * y * r' i * (x * g) * (g * y * r' j * (x * g))
            = g * y * (r' i * (x * g * (g * y)) * r' j) * (x * g) := by noncomm_ring
          _ = 0 := by rw [hVU, mul_one, hr'orth i j hij]; simp
  · intro i hi
    have hri : r i = g * y * r' i * (x * g) := if_neg hi
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [hri, hgdef]
      calc g * (g * y * r' i * (x * g)) = (g * g) * y * r' i * (x * g) := by noncomm_ring
        _ = g * y * r' i * (x * g) := by rw [hg]
    · rw [hri, hgdef]
      calc g * y * r' i * (x * g) * g = g * y * r' i * (x * (g * g)) := by noncomm_ring
        _ = g * y * r' i * (x * g) := by rw [hg]
    · rw [hri]
      refine ⟨g * y * a i, b i * (x * g), ?_, ?_⟩
      · rw [hab i]
        noncomm_ring
      · symm
        calc b i * (x * g) * (g * y * a i) = b i * (x * g * (g * y)) * a i := by noncomm_ring
          _ = 1 := by rw [hVU, mul_one, ← hba i]
  · refine ⟨matrixWitnessSum s t, isIdempotentElem_matrixWitnessSum hts hcross,
      matrixCornerEquiv hts hcross, Finset.sum_congr rfl fun i _ => hwit i, ?_⟩
    intro v hv
    have hhead : s i0 * (if i0 = i0 then (v : R) else 1) * t i0 =
        (1 - e) * (v : R) * (1 - e) + f := by
      show (if i0 = i0 then (1 - e) + S₀ else g * y * a i0) *
          (if i0 = i0 then (v : R) else 1) *
          (if i0 = i0 then (1 - e) + T₀ else b i0 * (x * g)) = _
      rw [if_pos rfl, if_pos rfl, if_pos rfl]
      have hw1 : (1 - e) * (e + (1 - e) * (v : R) * (1 - e)) =
          (1 - e) * (v : R) * (1 - e) := by
        calc (1 - e) * (e + (1 - e) * (v : R) * (1 - e))
            = (1 - e) * e + (1 - e) * (1 - e) * (v : R) * (1 - e) := by noncomm_ring
          _ = (1 - e) * (v : R) * (1 - e) := by rw [hoee, hoe, zero_add]
      have hw2 : S₀ * (e + (1 - e) * (v : R) * (1 - e)) = S₀ := by
        calc S₀ * (e + (1 - e) * (v : R) * (1 - e))
            = S₀ * e + S₀ * (1 - e) * (v : R) * (1 - e) := by noncomm_ring
          _ = S₀ := by rw [hSe, hSoe, zero_mul, zero_mul, add_zero]
      calc ((1 - e) + S₀) * (v : R) * ((1 - e) + T₀)
          = ((1 - e) * (e + (1 - e) * (v : R) * (1 - e)) +
              S₀ * (e + (1 - e) * (v : R) * (1 - e))) * ((1 - e) + T₀) := by
            rw [← add_mul, ← hv]
        _ = ((1 - e) * (v : R) * (1 - e) + S₀) * ((1 - e) + T₀) := by rw [hw1, hw2]
        _ = (1 - e) * (v : R) * ((1 - e) * (1 - e)) + (1 - e) * (v : R) * ((1 - e) * T₀) +
              S₀ * (1 - e) + S₀ * T₀ := by noncomm_ring
        _ = (1 - e) * (v : R) * (1 - e) + f := by
            rw [hoe, hoeT, hSoe, hST, mul_zero, add_zero, add_zero]
    have herase : ∑ i ∈ Finset.univ.erase i0, s i * (if i = i0 then (v : R) else 1) * t i =
        ∑ i ∈ Finset.univ.erase i0, r i := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [if_neg (Finset.ne_of_mem_erase hi), mul_one]
      exact hwit i
    change matrixEmbed s t (Matrix.diagonal fun i => if i = i0 then (v : R) else 1) = _
    rw [matrixEmbed_diagonal, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i0),
      herase]
    exact congrArg (· + ∑ i ∈ Finset.univ.erase i0, r i) hhead

end MFQuotientUnitsItemB
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.MFQuotientUnitsItemB.t_mul_matrixEmbed_mul_s
#audit_axioms GroupApproximation.MFQuotientUnitsItemB.matrixEmbed_coords
#audit_axioms GroupApproximation.MFQuotientUnitsItemB.matrixEmbed_diagonal
#audit_axioms GroupApproximation.MFQuotientUnitsItemB.coe_matrixCornerEquiv
#audit_closed_axioms GroupApproximation.MFQuotientUnitsItemB.manuscriptSentence_itemB
