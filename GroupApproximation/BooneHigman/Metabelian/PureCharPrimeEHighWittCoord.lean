import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittGroup
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittPolyFun
import GroupApproximation.Meta.AxiomGuard

/-!
# Weighted polynomial functions on `W₂(L)ⁿ` (bh-met-87c, part 6)

Coordinates on `Fin n → eHighWitt_W2 L p` are indexed by `Fin n ⊕ Fin n`:

* `inl i` is the zeroth Witt coordinate of the `i`-th entry, with weight `1`;
* `inr i` is the first Witt coordinate, with weight `p`.

`eHighWitt_trans_isWeightPoly`: every translation `x ↦ x + m` is weight-polynomial.

* The zeroth coordinate of `x + m` is `x₀ + m₀ · t`.
* The first coordinate is `x₁ + m₁ · t^p - ∑ⱼ ⌊C(p,j)/p⌋ m₀^(p-j) · x₀^j t^(p-j)`.

Both are homogeneous of the right degree after homogenizing with `t = 1`.

`eHighWitt_W2_polyFun`: suppose `act q` is weight-polynomial for every `q`.  Then there is a
space `V` of functions on `W₂(L)ⁿ` that is finite-dimensional, stable under translations and
under `act`, and separating.  It is the space of polynomials of weighted degree `≤ p`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Coprimary

open MvPolynomial

noncomputable section

/-- Weights of the Witt coordinates: `1` for `x₀`, `p` for `x₁`. -/
def eHighWitt_wt (p n : ℕ) : Fin n ⊕ Fin n → ℕ := Sum.elim (fun _ => 1) (fun _ => p)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWitt_wt

/-- The Witt coordinates of a point of `W₂(L)ⁿ`. -/
def eHighWitt_coord {L : Type} {p n : ℕ} (x : Fin n → eHighWitt_W2 L p) :
    Fin n ⊕ Fin n → L :=
  Sum.elim (fun i => (x i).x0) (fun i => (x i).x1)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWitt_coord

theorem eHighWitt_coord_injective {L : Type} {p n : ℕ} :
    Function.Injective
      (eHighWitt_coord : (Fin n → eHighWitt_W2 L p) → Fin n ⊕ Fin n → L) := by
  intro x y h
  funext i
  exact eHighWitt_W2.ext (congrFun h (Sum.inl i)) (congrFun h (Sum.inr i))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWitt_coord_injective

/-- Translations of `W₂(L)ⁿ` are weight-polynomial. -/
theorem eHighWitt_trans_isWeightPoly {L : Type} [Field L] {p n : ℕ}
    (m : Fin n → eHighWitt_W2 L p) :
    eHighWitt_IsWeightPoly (eHighWitt_wt p n) eHighWitt_coord (fun x => x + m) := by
  intro v
  cases v with
  | inl i =>
    refine ⟨X (some (Sum.inl i)) + C (m i).x0 * X none, ?_, fun x => ?_⟩
    · have h1 : IsWeightedHomogeneous (eHighWitt_hwt (eHighWitt_wt p n))
          (X (some (Sum.inl i)) : MvPolynomial (Option (Fin n ⊕ Fin n)) L) 1 :=
        isWeightedHomogeneous_X L _ _
      have h2 : IsWeightedHomogeneous (eHighWitt_hwt (eHighWitt_wt p n))
          (C (m i).x0 * X none : MvPolynomial (Option (Fin n ⊕ Fin n)) L) 1 :=
        (isWeightedHomogeneous_X L _ none).C_mul _
      exact h1.add h2
    · simp only [map_add, map_mul, aeval_X, aeval_C, Algebra.algebraMap_self_apply]
      show (x i).x0 + (m i).x0 = (x i).x0 + (m i).x0 * 1
      ring
  | inr i =>
    refine ⟨X (some (Sum.inr i)) + C (m i).x1 * X none ^ p -
      ∑ j ∈ Finset.range (p + 1), C (((p.choose j / p : ℕ) : L) * (m i).x0 ^ (p - j)) *
        (X (some (Sum.inl i)) ^ j * X none ^ (p - j)), ?_, fun x => ?_⟩
    · have h1 : IsWeightedHomogeneous (eHighWitt_hwt (eHighWitt_wt p n))
          (X (some (Sum.inr i)) : MvPolynomial (Option (Fin n ⊕ Fin n)) L) p :=
        isWeightedHomogeneous_X L _ _
      have h2 : IsWeightedHomogeneous (eHighWitt_hwt (eHighWitt_wt p n))
          (C (m i).x1 * X none ^ p : MvPolynomial (Option (Fin n ⊕ Fin n)) L) p :=
        eHighWitt_isWH_of_eq ((eHighWitt_isWH_X_pow _ none p).C_mul _) (one_mul p)
      have h3 : IsWeightedHomogeneous (eHighWitt_hwt (eHighWitt_wt p n))
          (∑ j ∈ Finset.range (p + 1), C (((p.choose j / p : ℕ) : L) * (m i).x0 ^ (p - j)) *
            (X (some (Sum.inl i)) ^ j * X none ^ (p - j)) :
              MvPolynomial (Option (Fin n ⊕ Fin n)) L) p := by
        refine IsWeightedHomogeneous.sum _ _ _ fun j hj => ?_
        refine eHighWitt_isWH_of_eq (((eHighWitt_isWH_X_pow _ (some (Sum.inl i)) j).mul
          (eHighWitt_isWH_X_pow _ none (p - j))).C_mul _) ?_
        have hjp := Finset.mem_range.mp hj
        show 1 * j + 1 * (p - j) = p
        omega
      have h4 := (weightedHomogeneousSubmodule L (eHighWitt_hwt (eHighWitt_wt p n)) p).sub_mem
        ((weightedHomogeneousSubmodule L (eHighWitt_hwt (eHighWitt_wt p n)) p).add_mem
          ((mem_weightedHomogeneousSubmodule L _ _ _).mpr h1)
          ((mem_weightedHomogeneousSubmodule L _ _ _).mpr h2))
        ((mem_weightedHomogeneousSubmodule L _ _ _).mpr h3)
      exact (mem_weightedHomogeneousSubmodule L _ _ _).mp h4
    · simp only [map_add, map_sub, map_mul, map_pow, map_sum, aeval_X, aeval_C,
        Algebra.algebraMap_self_apply]
      show (x i).x1 + (m i).x1 - eHighWitt_carry p (x i).x0 (m i).x0 =
        (x i).x1 + (m i).x1 * 1 ^ p - ∑ j ∈ Finset.range (p + 1),
          ((p.choose j / p : ℕ) : L) * (m i).x0 ^ (p - j) * ((x i).x0 ^ j * 1 ^ (p - j))
      have hs : ∀ j ∈ Finset.range (p + 1),
          ((p.choose j / p : ℕ) : L) * (x i).x0 ^ j * (m i).x0 ^ (p - j) =
            ((p.choose j / p : ℕ) : L) * (m i).x0 ^ (p - j) * ((x i).x0 ^ j * 1 ^ (p - j)) :=
        fun j _ => by ring
      rw [eHighWitt_carry, Finset.sum_congr rfl hs]
      ring

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWitt_trans_isWeightPoly

end

end GroupApproximation.BooneHigman.Metabelian.Coprimary
