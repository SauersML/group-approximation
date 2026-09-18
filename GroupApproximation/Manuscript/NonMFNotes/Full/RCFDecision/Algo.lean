import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.Tree
import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.UPoly
import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.Univariate.Defs

/-!
# The symbolic decision procedure

`non_mf_group_notes.tex`, `thm:mf-arithmetic`, proof step "Fixed-dimensional
feasibility is decidable over the real closed field".  This file only holds the
algorithm.  Every function is first-order recursion on lists and natural numbers,
over `ℤ`, `ℕ`, `Bool` and `Option`.  The correctness proofs live in the sibling files.

* `normUP u`: case tree over the sign of the top coefficients of `u`, returning
  `(b, bl, s)` with `u` equal to `b ++ [bl]` up to zero top coefficients, where
  `bl ≠ 0` has sign `bsgn s`;
* `premLoop`: pseudo-remainder with even multipliers `bl²`;
* `chainIter`, `taqTree`: parametric generalized Sturm chains, and their Tarski
  query values;
* `bkrTree`: the Ben-Or--Kozen--Reif sum;
* `conjTree i c`: elimination of `∃ x_i` from a conjunction of atoms;
* `elimAll`, `decidePrenex`: prenex sentences.
-/

namespace GroupApproximation.Full.NN11b

/-! ## Signs and branching -/

/-- The sign encoded by a Boolean: `true ↦ 1`, `false ↦ -1`. -/
def bsgn : Bool → ℤ
  | true => 1
  | false => -1

/-- Branching on the sign of `c`: positive, negative, zero. -/
def branch3 {α : Type} (c : MvP) (t1 t2 t3 : List (List Atom × α)) : List (List Atom × α) :=
  guardT [(true, c)] t1 ++ guardT [(true, mvNeg c)] t2 ++ guardT [(false, c)] t3

/-- Normal forms of coefficient lists: `(b, bl, s)` stands for `b ++ [bl]` with
`bl ≠ 0` of sign `bsgn s`. -/
abbrev NForm := List MvP × MvP × Bool

/-- Normalization of a coefficient list given top coefficient first. -/
def normRev : List MvP → List (List Atom × Option (List MvP × MvP × Bool))
  | [] => tpure none
  | c :: w => branch3 c (tpure (some (w.reverse, c, true))) (tpure (some (w.reverse, c, false)))
      (normRev w)

/-- Normalization of a coefficient list (lowest degree first). -/
def normUP (u : List MvP) : List (List Atom × Option (List MvP × MvP × Bool)) :=
  normRev u.reverse

/-! ## Pseudo-remainder -/

/-- One reduction step `bl²·A - bl·an·X^{n-k}·B`, where `A = a ++ [an]`,
`B = b ++ [bl]`, `n = a.length`, `k = b.length`. -/
def premStep (bl : MvP) (b : List MvP) (an : MvP) (a : List MvP) : List MvP :=
  upAdd (upSmul (mvMul bl bl) a)
    (upSmul (mvNeg (mvMul bl an)) (List.replicate (a.length - b.length) [] ++ b))

/-- The pseudo-remainder loop.  The dividend is given top coefficient first. -/
def premLoop (bl : MvP) (b : List MvP) : ℕ → List MvP → List MvP
  | 0, v => v
  | _ + 1, [] => []
  | t + 1, an :: w =>
      if w.length < b.length then an :: w else premLoop bl b t (premStep bl b an w.reverse).reverse

/-! ## Parametric Sturm chains -/

/-- Chain states `(done, A, b, bl, acc)`: `A` top coefficient first, `B = b ++ [bl]`
normalized, `acc` the signs at `+∞` and `-∞` of the chain so far. -/
abbrev St := Bool × List MvP × List MvP × MvP × List (ℤ × ℤ)

/-- The state after one remainder, given the normalized remainder. -/
def chainNext (v b : List MvP) (bl : MvP) (acc : List (ℤ × ℤ)) :
    Option (List MvP × MvP × Bool) → Bool × List MvP × List MvP × MvP × List (ℤ × ℤ)
  | none => (true, v, b, bl, acc)
  | some (d, dl, s) => (false, bl :: b.reverse, d, dl, acc ++ [(bsgn s, bsgn s * (-1) ^ d.length)])

/-- One step of the parametric chain. -/
def chainStep : Bool × List MvP × List MvP × MvP × List (ℤ × ℤ) →
    List (List Atom × (Bool × List MvP × List MvP × MvP × List (ℤ × ℤ)))
  | (true, v, b, bl, acc) => tpure (true, v, b, bl, acc)
  | (false, v, [], bl, acc) => tpure (true, v, [], bl, acc)
  | (false, v, c :: b, bl, acc) =>
      tmap (chainNext v (c :: b) bl acc) (normUP (upNeg (premLoop bl (c :: b) v.length v).reverse))

/-- `n` steps of the parametric chain. -/
def chainIter (n : ℕ) (t : List (List Atom × St)) : List (List Atom × St) :=
  (fun s : List (List Atom × St) => tbind s chainStep)^[n] t

/-- The value `changes(-∞) - changes(+∞)` of a chain state. -/
def leafVal (st : Bool × List MvP × List MvP × MvP × List (ℤ × ℤ)) : ℤ :=
  ((changes (st.2.2.2.2.map Prod.snd) : ℕ) : ℤ) - ((changes (st.2.2.2.2.map Prod.fst) : ℕ) : ℤ)

/-- The chain started at normalized `P = p ++ [pl]` and `P'Q = q ++ [ql]`. -/
def chainStart (p : List MvP) (pl : MvP) (sp : Bool) (q : List MvP) (ql : MvP) (sq : Bool) :
    List (List Atom × St) :=
  chainIter (q.length + 1)
    (tpure (false, pl :: p.reverse, q, ql,
      [(bsgn sp, bsgn sp * (-1) ^ p.length), (bsgn sq, bsgn sq * (-1) ^ q.length)]))

/-- The Tarski query `TaQ(Q, P)` as a case tree, from the coefficient lists of `P`
and of `P'Q`. -/
def taqTree (u0 u1 : List MvP) : List (List Atom × ℤ) :=
  tbind (normUP u0) fun o0 => o0.elim (tpure 0) fun n0 =>
    tbind (normUP u1) fun o1 => o1.elim (tpure 0) fun n1 =>
      tmap leafVal (chainStart n0.1 n0.2.1 n0.2.2 n1.1 n1.2.1 n1.2.2)

/-! ## Ben-Or--Kozen--Reif -/

/-- The constant coefficient list `1`. -/
def upOne : List MvP := [mvConst 1]

/-- Powers of a coefficient list. -/
def upPow (u : List MvP) : ℕ → List MvP
  | 0 => upOne
  | k + 1 => upMul u (upPow u k)

/-- The product `∏ u_j^{e_j}` of coefficient lists. -/
def prodPowUP : List (List MvP) → List ℕ → List MvP
  | u :: us, k :: e => upMul (upPow u k) (prodPowUP us e)
  | _, _ => upOne

/-- The product of coefficient lists. -/
def prodUP : List (List MvP) → List MvP
  | [] => upOne
  | u :: us => upMul u (prodUP us)

/-- Weighted sum `∑ w(σ, e) z_e`. -/
def weightedSum (σ : List ℤ) : List (List ℕ) → List ℤ → ℤ
  | e :: es, z :: zs => weight σ e * z + weightedSum σ es zs
  | _, _ => 0

/-- The Ben-Or--Kozen--Reif sum `∑_e w(σ, e) TaQ(∏ q_j^{e_j}, F)` as a case tree. -/
def bkrTree (F : List MvP) (us : List (List MvP)) (σ : List ℤ) : List (List Atom × ℤ) :=
  tmap (weightedSum σ (expVecs us.length))
    (tseq ((expVecs us.length).map fun e => taqTree F (upMul (upDeriv F) (prodPowUP us e))))

/-! ## Eliminating one existential quantifier from a conjunction -/

/-- The atom `(b, p)` viewed in `x_i`, normalized. -/
def atomTree (i : ℕ) (a : Bool × List (ℤ × List ℕ)) :
    List (List Atom × Option (List MvP × MvP × Bool)) :=
  normUP (coeffX i a.2)

/-- Collecting the nonvanishing atoms with their target signs (`1` for `>`, `0`
for `=`); `none` if a strict atom vanishes identically. -/
def collectAtoms : List Atom → List (Option (List MvP × MvP × Bool)) →
    Option (List (ℤ × (List MvP × MvP × Bool)))
  | (true, _) :: _, none :: _ => none
  | (false, _) :: c, none :: os => collectAtoms c os
  | (b, _) :: c, some n :: os => (collectAtoms c os).map (List.cons (if b then 1 else 0, n))
  | _, _ => some []

/-- The decision of `∃ x, sgn q_j(x) = σ_j` for normalized `q_j`, as a case tree:
signs at `±∞`, then the Ben-Or--Kozen--Reif sums on the roots of `F = ∏ q_j` and of `F'`. -/
def conjDecide (d : List (ℤ × (List MvP × MvP × Bool))) : List (List Atom × Bool) :=
  let σ := d.map Prod.fst
  let us := d.map fun x => x.2.1 ++ [x.2.2.1]
  if d.map (fun x => bsgn x.2.2.2) = σ ∨ d.map (fun x => bsgn x.2.2.2 * (-1) ^ x.2.1.length) = σ
  then tpure true
  else tmap (fun z : ℤ × ℤ => decide (0 < z.1) || decide (0 < z.2))
    (tbind (bkrTree (prodUP us) us σ) fun z1 =>
      tmap (Prod.mk z1) (bkrTree (upDeriv (prodUP us)) us σ))

/-- Elimination of `∃ x_i` from a conjunction of atoms, as a case tree. -/
def conjTree (i : ℕ) (c : List Atom) : List (List Atom × Bool) :=
  tbind (tseq (c.map (atomTree i))) fun os => (collectAtoms c os).elim (tpure false) conjDecide

/-! ## Prenex sentences -/

/-- Elimination of `∃ x_i` from a formula in disjunctive normal form. -/
def elimEx (i : ℕ) (f : List (List Atom)) : List (List Atom) :=
  f.flatMap fun c => toQF (conjTree i c)

/-- Elimination of a quantifier prefix (`(true, i)` is `∃ x_i`, `(false, i)` is `∀ x_i`),
innermost quantifier last. -/
def elimAll : List (Bool × ℕ) → List (List Atom) → List (List Atom)
  | [], f => f
  | (true, i) :: qs, f => elimEx i (elimAll qs f)
  | (false, i) :: qs, f => qfNot (elimEx i (qfNot (elimAll qs f)))

/-- Prenex sentences: a quantifier prefix and a quantifier-free matrix. -/
abbrev Prenex := List (Bool × ℕ) × List (List Atom)

/-- The decision procedure: eliminate all quantifiers and evaluate at `0`. -/
def decidePrenex (φ : List (Bool × ℕ) × List (List Atom)) : Bool :=
  qfZ (elimAll φ.1 φ.2)

end GroupApproximation.Full.NN11b
