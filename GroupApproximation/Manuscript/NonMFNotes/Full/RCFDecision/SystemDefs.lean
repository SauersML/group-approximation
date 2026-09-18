import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.Prenex

/-!
# Polynomial systems as prenex sentences

`non_mf_group_notes.tex`, `thm:mf-arithmetic`, proof step "Fixed-dimensional
feasibility is decidable over the real closed field": the feasibility of a system
`p = 0 (p ∈ S.1)`, `0 ≤ q (q ∈ S.2)` is the existential sentence `systemPrenex S`
over the variables occurring in the system.  The correctness proof lives in
`ExistsSystem`.
-/

namespace GroupApproximation.Full.NN11b

/-- The conjunction `0 ≤ q` over `q ∈ qs`, in disjunctive normal form. -/
def nonnegQF : List MvP → List (List Atom)
  | [] => [[]]
  | q :: qs => qfAnd [[(true, q)], [(false, q)]] (nonnegQF qs)

/-- A bound on the variables occurring in a list of polynomials: the maximal length of
their exponent vectors. -/
def varBound (l : List MvP) : ℕ :=
  (l.flatMap fun p => p.map fun m => m.2.length).foldr max 0

/-- The sentence `∃ x_0 … ∃ x_{N-1}, ⋀ p = 0 ∧ ⋀ 0 ≤ q`. -/
def systemPrenex (S : List MvP × List MvP) : List (Bool × ℕ) × List (List Atom) :=
  ((List.range (varBound (S.1 ++ S.2))).map fun i => (true, i),
    qfAnd [S.1.map fun p => (false, p)] (nonnegQF S.2))

end GroupApproximation.Full.NN11b
