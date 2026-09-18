import GroupApproximation.Manuscript.NonMFNotes.Full.LiteralDecidable.Reduction
import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.Computability.PolyOps

/-!
# Neutral polynomial systems as NN11b monomial-list systems (lane NN02c)

Manuscript: `thm:mf-radical-arithmetic` (non_mf_group_notes.tex), sentence
"This is decidable over the real closed field" (Tarski 1951, Seidenberg 1954).

The neutral systems `PolySystem` of this lane (signed natural coefficients, monomials as lists
of variable indices) are translated into the integer monomial-list polynomials `NN11b.MvP`
(exponent vectors) on which the decision procedure of lane NN11b operates.  The translation is
primitive recursive and preserves evaluation (`mvEval_toMv`), giving the many-one reduction of
`PolySystem.Holds` to real solvability of `List MvP × List MvP` systems, and by composition
`literalD_manyOneReducible_existsSystem`.  With NN11b's decision of such systems,
`ComputablePred.computable_of_manyOneReducible` then yields decidability of `D(P,v,n,d)`.
-/

namespace GroupApproximation.Full.NN02c

/-- The integer value of a signed natural coefficient. -/
def coefInt (c : Coef) : ℤ := bif c.1 then -(c.2 : ℤ) else (c.2 : ℤ)

theorem cast_coefInt (c : Coef) : ((coefInt c : ℤ) : ℝ) = coefVal c := by
  rcases c with ⟨b, n⟩
  cases b with
  | false =>
    show (((n : ℤ) : ℤ) : ℝ) = (n : ℝ)
    exact Int.cast_natCast n
  | true =>
    show ((-(n : ℤ) : ℤ) : ℝ) = -(n : ℝ)
    rw [Int.cast_neg, Int.cast_natCast]

/-- The exponent vector of a monomial given as a list of variable indices. -/
def expOf (l : List ℕ) : List ℕ := l.foldr (fun i e => NN11b.addExp (NN11b.varExp i) e) []

theorem monoEval_expOf (x : ℕ → ℝ) (l : List ℕ) :
    NN11b.monoEval x (expOf l) = monoVal x l := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    show NN11b.monoEval x (NN11b.addExp (NN11b.varExp i) (expOf l)) = x i * monoVal x l
    rw [NN11b.monoEval_addExp, NN11b.monoEval_varExp, ih]

/-- Translation of a neutral polynomial into an NN11b monomial list. -/
def toMv (p : Poly) : NN11b.MvP := p.map fun m => (coefInt m.1, expOf m.2)

theorem mvEval_toMv (x : ℕ → ℝ) (p : Poly) : NN11b.mvEval x (toMv p) = evalR x p := by
  induction p with
  | nil => rfl
  | cons m p ih =>
    show (coefInt m.1 : ℝ) * NN11b.monoEval x (expOf m.2) + NN11b.mvEval x (toMv p) =
      coefVal m.1 * monoVal x m.2 + evalR x p
    rw [ih, monoEval_expOf, cast_coefInt]

/-- Translation of a neutral system into a system over `NN11b.MvP`. -/
def toMvSystem (S : PolySystem) : List NN11b.MvP × List NN11b.MvP :=
  (S.1.map toMv, S.2.map toMv)

theorem holds_iff_toMvSystem (S : PolySystem) :
    PolySystem.Holds S ↔
      ∃ x : ℕ → ℝ, (∀ p ∈ (toMvSystem S).1, NN11b.mvEval x p = 0) ∧
      ∀ p ∈ (toMvSystem S).2, 0 ≤ NN11b.mvEval x p := by
  constructor
  · rintro ⟨x, h1, h2⟩
    refine ⟨x, fun q hq => ?_, fun q hq => ?_⟩
    · change q ∈ S.1.map toMv at hq
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
      rw [mvEval_toMv]
      exact h1 p hp
    · change q ∈ S.2.map toMv at hq
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
      rw [mvEval_toMv]
      exact h2 p hp
  · rintro ⟨x, h1, h2⟩
    change ∀ q ∈ S.1.map toMv, NN11b.mvEval x q = 0 at h1
    change ∀ q ∈ S.2.map toMv, 0 ≤ NN11b.mvEval x q at h2
    refine ⟨x, fun p hp => ?_, fun p hp => ?_⟩
    · rw [← mvEval_toMv]
      exact h1 (toMv p) (List.mem_map.mpr ⟨p, hp, rfl⟩)
    · rw [← mvEval_toMv]
      exact h2 (toMv p) (List.mem_map.mpr ⟨p, hp, rfl⟩)

/-! ## Primitive recursiveness of the translation -/

theorem varExp_eq (i : ℕ) : NN11b.varExp i = List.replicate i 0 ++ [1] := by
  induction i with
  | zero => rfl
  | succ i ih =>
    show 0 :: NN11b.varExp i = List.replicate (i + 1) 0 ++ [1]
    rw [ih, List.replicate_succ, List.cons_append]

theorem primrec_varExp : Primrec NN11b.varExp :=
  (Primrec.list_append.comp
    (NN11b.PR.primrec_replicate.comp Primrec.id (Primrec.const (0 : ℕ)))
    (Primrec.const ([1] : List ℕ))).of_eq fun i => (varExp_eq i).symm

theorem primrec_coefInt : Primrec coefInt :=
  Primrec.cond Primrec.fst
    (Higman.primrec_int_neg.comp (Higman.primrec_int_natCast.comp Primrec.snd))
    (Higman.primrec_int_natCast.comp Primrec.snd)

theorem primrec_expOf : Primrec expOf := by
  show Primrec fun l : List ℕ => l.foldr (fun i e => NN11b.addExp (NN11b.varExp i) e) []
  have hh : Primrec₂ fun (_ : List ℕ) (q : ℕ × List ℕ) =>
      NN11b.addExp (NN11b.varExp q.1) q.2 :=
    NN11b.PR.primrec_addExp.comp (primrec_varExp.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  exact Primrec.list_foldr (f := fun l : List ℕ => l) (g := fun _ : List ℕ => ([] : List ℕ))
    (h := fun (_ : List ℕ) (q : ℕ × List ℕ) => NN11b.addExp (NN11b.varExp q.1) q.2)
    Primrec.id (Primrec.const []) hh

theorem primrec_toMv : Primrec toMv := by
  show Primrec fun p : Poly => p.map fun m => (coefInt m.1, expOf m.2)
  have hm : Primrec₂ fun (_ : Poly) (m : Coef × List ℕ) => (coefInt m.1, expOf m.2) :=
    Primrec.pair (primrec_coefInt.comp (Primrec.fst.comp Primrec.snd))
      (primrec_expOf.comp (Primrec.snd.comp Primrec.snd))
  exact Primrec.list_map (f := fun p : Poly => p)
    (g := fun (_ : Poly) (m : Coef × List ℕ) => (coefInt m.1, expOf m.2)) Primrec.id hm

theorem primrec_toMvSystem : Primrec toMvSystem := by
  show Primrec fun S : PolySystem => (S.1.map toMv, S.2.map toMv)
  have ht : Primrec₂ fun (_ : PolySystem) (p : Poly) => toMv p := primrec_toMv.comp Primrec.snd
  exact Primrec.pair
    (Primrec.list_map (f := fun S : PolySystem => S.1)
      (g := fun (_ : PolySystem) (p : Poly) => toMv p) Primrec.fst ht)
    (Primrec.list_map (f := fun S : PolySystem => S.2)
      (g := fun (_ : PolySystem) (p : Poly) => toMv p) Primrec.snd ht)

/-! ## The reductions -/

/-- Neutral polynomial systems many-one reduce to real solvability of `NN11b.MvP` systems. -/
theorem polySystemHolds_manyOneReducible :
    PolySystem.Holds ≤₀ (fun S : List NN11b.MvP × List NN11b.MvP =>
      ∃ x : ℕ → ℝ, (∀ p ∈ S.1, NN11b.mvEval x p = 0) ∧ ∀ p ∈ S.2, 0 ≤ NN11b.mvEval x p) :=
  ⟨toMvSystem, primrec_toMvSystem.to_comp, holds_iff_toMvSystem⟩

/-- **`D(P,v,n,d)` many-one reduces to real solvability of `NN11b.MvP` systems**
(`thm:mf-radical-arithmetic`, "This is decidable over the real closed field"). -/
theorem literalD_manyOneReducible_existsSystem :
    (fun z : (PresentationCodes.PresentationCode × List (ℕ × Bool)) × ℕ × ℕ =>
      NN02b.LiteralD z.1.1 z.1.2 z.2.1 z.2.2) ≤₀
      (fun S : List NN11b.MvP × List NN11b.MvP =>
        ∃ x : ℕ → ℝ, (∀ p ∈ S.1, NN11b.mvEval x p = 0) ∧ ∀ p ∈ S.2, 0 ≤ NN11b.mvEval x p) :=
  literalD_manyOneReducible.trans polySystemHolds_manyOneReducible

end GroupApproximation.Full.NN02c
