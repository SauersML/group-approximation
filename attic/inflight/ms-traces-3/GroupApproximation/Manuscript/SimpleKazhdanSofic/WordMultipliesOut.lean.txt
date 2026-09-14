import GroupApproximation.Manuscript.SimpleKazhdanSofic.WordProblemReducesToLanguageInstance
import GroupApproximation.Manuscript.SimpleKazhdanSofic.WordProblemCriterion
import GroupApproximation.Meta.AxiomGuard

/-!
# Multiplying out a word gives tables on words

`simple_kazhdan_sofic_group.tex`, corollary `cor:wp`, first sentence of the proof (census key
`427203e368c1`):

> Multiplying out a word in the generators in `LC(A^ℤ, F₂) ⋊ ℤ`, which maps onto `R`, gives a matrix
> with entries `∑_j f_j u^j`, each `f_j` given by a table on the words of some length, using
> `uf = (f∘T⁻¹)u`.

`PrintedWordMultipliesOutToTables` states the sentence.  For every word `w` in the generators
`e_ij(s)`, `s ∈ {u, u⁻¹} ∪ {e_a}`, there are a length bound `K`, a finite exponent set `E` and tables `F`
on the words of length `2K + 1`.  None of them depends on `X`: they are computed in `LC(A^ℤ, F₂) ⋊ ℤ`.
For every subshift `X`, the matrix of `w` in `G_X` has entries `∑_{j ∈ E} f_j u^j` with
`f_j(x) = F(x_{[-K,K]})`.

The route is the one of `CylinderTables`.  A word multiplies out to its matrix of cylinder tables
(`val_wordValue`, through `uf = (f∘T⁻¹)u` on cylinders), a table is the Laurent sum of its coefficient
functions (`eval_eq_sum`), and each coefficient function is read off a window (`coeffFun_apply_eq`).
-/

namespace GroupApproximation

namespace CylinderTables

open SkewMonoidAlgebra
open Multiplicative (ofAdd)

variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] {X : Set (ℤ → A)}

/-- A monomial is its coefficient function times a power of `u`. -/
theorem monoEval_eq_coeff_mul (T : ↥X ≃ₜ ↥X) (m : Mono A) :
    monoEval T m = ClopenCrossedProduct.coeff T (ZMod 2) (cylInd X m.2) *
      ((ClopenCrossedProduct.unit T (ZMod 2) ^ m.1 : (ClopenCrossedProduct T (ZMod 2))ˣ) :
        ClopenCrossedProduct T (ZMod 2)) := by
  rw [monoEval, ClopenCrossedProduct.coeff_apply, Pestov91.CrossedProduct.val_unit_zpow,
    Pestov91.CrossedProduct.C_mul_single, mul_one]

/-- **A table is the Laurent sum of its coefficient functions.** -/
theorem eval_eq_sum (T : ↥X ≃ₜ ↥X) (l : Table A) (E : Finset ℤ) (hE : ∀ m ∈ l, m.1 ∈ E) :
    eval T l = ∑ j ∈ E, ClopenCrossedProduct.coeff T (ZMod 2) (coeffFun X l j) *
      ((ClopenCrossedProduct.unit T (ZMod 2) ^ j : (ClopenCrossedProduct T (ZMod 2))ˣ) :
        ClopenCrossedProduct T (ZMod 2)) := by
  induction l with
  | nil =>
    rw [eval_nil]
    refine (Finset.sum_eq_zero fun j _ => ?_).symm
    show ClopenCrossedProduct.coeff T (ZMod 2) 0 * _ = 0
    rw [map_zero, zero_mul]
  | cons m l ih =>
    have hmE : m.1 ∈ E := hE m (List.mem_cons.2 (Or.inl rfl))
    have hlE : ∀ m' ∈ l, m'.1 ∈ E := fun m' h => hE m' (List.mem_cons.2 (Or.inr h))
    rw [eval_cons, ih hlE]
    have hsplit : ∀ j ∈ E,
        ClopenCrossedProduct.coeff T (ZMod 2) (coeffFun X (m :: l) j) *
            ((ClopenCrossedProduct.unit T (ZMod 2) ^ j : (ClopenCrossedProduct T (ZMod 2))ˣ) :
              ClopenCrossedProduct T (ZMod 2)) =
          (if m.1 = j then monoEval T m else 0) +
            ClopenCrossedProduct.coeff T (ZMod 2) (coeffFun X l j) *
              ((ClopenCrossedProduct.unit T (ZMod 2) ^ j : (ClopenCrossedProduct T (ZMod 2))ˣ) :
                ClopenCrossedProduct T (ZMod 2)) := by
      intro j _
      show ClopenCrossedProduct.coeff T (ZMod 2)
          ((if m.1 = j then cylInd X m.2 else 0) + coeffFun X l j) * _ = _
      rw [map_add, add_mul]
      congr 1
      by_cases h : m.1 = j
      · rw [if_pos h, if_pos h, ← h, monoEval_eq_coeff_mul]
      · rw [if_neg h, if_neg h, map_zero, zero_mul]
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq, if_pos hmE]

end CylinderTables

namespace SimpleKazhdanSofic

open CylinderTables SymbolicDynamics.FullShift

/-- **tex l.474–477.**  Multiplying out a word in the generators in `LC(A^ℤ, F₂) ⋊ ℤ`, which maps onto
`R`, gives a matrix with entries `∑_j f_j u^j`, each `f_j` given by a table on the words of some
length.  The bound `K`, the exponents `E` and the tables `F` depend only on the word; for every subshift
`X`, the entries of the matrix of the word in `G_X` are the Laurent sums over `E` of functions read off
the window `x_{[-K,K]}` by `F`. -/
def PrintedWordMultipliesOutToTables : Prop :=
  ∀ (A : Type) [TopologicalSpace A] [DiscreteTopology A] [DecidableEq A] (w : List (Gen A × Bool)),
    ∃ (K : ℕ) (E : Finset ℤ) (F : Fin 3 → Fin 3 → ℤ → List A → Bool),
      ∀ S : Subshift A ℤ, ∃ f : Fin 3 → Fin 3 → ℤ → LocallyConstant S.carrier (ZMod 2),
        (∀ p q : Fin 3,
          (((wordValue (genValue S) w : G S) : (Matrix (Fin 3) (Fin 3) (R S))ˣ) :
              Matrix (Fin 3) (Fin 3) (R S)) p q =
            ∑ j ∈ E, ClopenCrossedProduct.coeff (subshiftHomeo S) (ZMod 2) (f p q j) *
              ((ClopenCrossedProduct.unit (subshiftHomeo S) (ZMod 2) ^ j : (R S)ˣ) : R S)) ∧
        ∀ (p q : Fin 3) (j : ℤ) (x : S.carrier),
          f p q j x = if F p q j (window x.1 K) = true then 1 else 0

theorem printedWordMultipliesOutToTables : PrintedWordMultipliesOutToTables := by
  intro A _ _ _ w
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ p q : Fin 3, tableRadius ((wordM genTable w : Mat A) p q) ≤ K :=
    ⟨(Finset.univ : Finset (Fin 3 × Fin 3)).sup fun pq => tableRadius ((wordM genTable w : Mat A) pq.1 pq.2),
      fun p q => Finset.le_sup (f := fun pq : Fin 3 × Fin 3 =>
        tableRadius ((wordM genTable w : Mat A) pq.1 pq.2)) (Finset.mem_univ (p, q))⟩
  obtain ⟨E, hE⟩ : ∃ E : Finset ℤ, ∀ (p q : Fin 3), ∀ m ∈ (wordM genTable w : Mat A) p q, m.1 ∈ E :=
    ⟨(Finset.univ : Finset (Fin 3 × Fin 3)).biUnion fun pq =>
        (((wordM genTable w : Mat A) pq.1 pq.2).map Prod.fst).toFinset,
      fun p q m hm => Finset.mem_biUnion.2 ⟨(p, q), Finset.mem_univ _,
        List.mem_toFinset.2 (List.mem_map.2 ⟨m, hm, rfl⟩)⟩⟩
  refine ⟨K, E, fun p q j v => windowParity K ((wordM genTable w : Mat A) p q) j v, fun S =>
    ⟨fun p q j => coeffFun S.carrier ((wordM genTable w : Mat A) p q) j, fun p q => ?_,
      fun p q j x => coeffFun_apply_eq ((wordM genTable w : Mat A) p q) j x (hK p q)⟩⟩
  exact (congrFun (congrFun (val_wordValue S w) p) q).trans
    (eval_eq_sum (subshiftHomeo S) ((wordM genTable w : Mat A) p q) E (hE p q))

end SimpleKazhdanSofic

end GroupApproximation

#audit_axioms GroupApproximation.CylinderTables.eval_eq_sum
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedWordMultipliesOutToTables
