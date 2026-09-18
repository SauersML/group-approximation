import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.Encoding.Semantics
import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.Encoding.WordVec
import GroupApproximation.Manuscript.MFRecognition.PrintedTarskiCertificateDerivation

/-!
# The sentence `Φ(P, n, c)` as a prenex formula over the reals

`non_mf_group_notes.tex`, `prop:mf-upper-bound`, printed sentence `9eae4d68673a`
("`Φ(P,n,c)` is a first-order sentence over the reals"), feeding
`thm:mf-arithmetic`.  With `d = certDim c`, `S = sWords P n c` and `R = P.2`, the
sentence `encodePrenex ((P, n), c)` reads

`∃ U_1 … U_k ∃ v_1 … v_{|S|} ∀ u_1 … u_{|R|}`
`  (⋀ U_g^* U_g = 1) ∧ (⋀ ‖v_t‖² = 1) ∧ d ≥ 1`
`  ∧ ⋀_t 16 ‖(S_t(U) - 1) v_t‖² ≥ 1 ∧ ⋀_t ‖u_t‖² - 4^n ‖(R_t(U) - 1) u_t‖² ≥ 0`,

the variables being the real and imaginary parts of the entries (tag `0`), of the
unit vectors witnessing the lower bounds `‖S_t(U) - 1‖ ≥ 1/4` (tag `1`), and of the
test vectors of the quadratic forms giving the upper bounds
`‖R_t(U) - 1‖ ≤ 2^{-n}` (tag `2`).
-/

namespace GroupApproximation.Full.NN11b

open GroupApproximation.PresentationCodes

/-- The entry `(p, q)` of `U_g^* U_g - 1`. -/
def encUnitEntry (d g p q : ℕ) : MvP × MvP :=
  cpAdd (cpSumRange d fun l => cpMul (cpConj (encGEntry g l p)) (encGEntry g l q))
    (if p = q then cpOfInt (-1) else cpZero)

/-- The equations `U_g^* U_g = 1` for `g < k`, in dimension `d`. -/
def encUnitEqs (k d : ℕ) : List MvP :=
  (List.range k).flatMap fun g => (List.range d).flatMap fun p =>
    (List.range d).flatMap fun q => [(encUnitEntry d g p q).1, (encUnitEntry d g p q).2]

/-- The coordinate `r` of the vector of tag `tag` and index `t`. -/
def encVecCoord (tag t d r : ℕ) : MvP × MvP := (encVecOf tag t d).getD r cpZero

/-- The polynomial `‖v_t‖² - 1`. -/
def encUnitNormPoly (d t : ℕ) : MvP :=
  encNormSq d (encVecCoord 1 t d) ++ mvConst (-1)

/-- The coordinate `r` of `(w(U) - 1) v`, for the vector `v` of tag `tag` and index `t`. -/
def encDisp (P : PresentationCode) (d : ℕ) (w : List (ℕ × Bool)) (tag t r : ℕ) : MvP × MvP :=
  cpAdd ((encWordVec P d w (encVecOf tag t d)).getD r cpZero) (cpNeg (encVecCoord tag t d r))

/-- The polynomial `16 ‖(w(U) - 1) v_t‖² - 1` (lower bound `‖w(U) - 1‖ ≥ 1/4`). -/
def encLowerPoly (P : PresentationCode) (d : ℕ) (w : List (ℕ × Bool)) (t : ℕ) : MvP :=
  mvMul (mvConst 16) (encNormSq d (encDisp P d w 1 t)) ++ mvConst (-1)

/-- The polynomial `‖u_t‖² - 4^n ‖(w(U) - 1) u_t‖²` (upper bound `‖w(U) - 1‖ ≤ 2^{-n}`). -/
def encUpperPoly (P : PresentationCode) (n d : ℕ) (w : List (ℕ × Bool)) (t : ℕ) : MvP :=
  encNormSq d (encVecCoord 2 t d) ++ mvMul (mvConst (-(4 : ℤ) ^ n)) (encNormSq d (encDisp P d w 2 t))

/-- The equations of the sentence. -/
def encEqs (P : PresentationCode) (d : ℕ) (S : List (List (ℕ × Bool))) : List MvP :=
  encUnitEqs (genCount P) d ++ (List.range S.length).map (encUnitNormPoly d)

/-- The nonnegativity conditions of the sentence. -/
def encNonnegs (P : PresentationCode) (n d : ℕ) (S : List (List (ℕ × Bool))) : List MvP :=
  mvConst ((d : ℤ) - 1) ::
    ((List.range S.length).map fun t => encLowerPoly P d (S.getD t []) t) ++
      (List.range P.2.length).map fun t => encUpperPoly P n d (P.2.getD t []) t

/-- The existentially quantified variables: entries of the unitaries and of the unit
vectors. -/
def encExVars (P : PresentationCode) (d : ℕ) (S : List (List (ℕ × Bool))) : List ℕ :=
  encBlock 0 (genCount P) d d ++ encBlock 1 S.length d 1

/-- The universally quantified variables: entries of the test vectors. -/
def encAllVars (P : PresentationCode) (d : ℕ) : List ℕ :=
  encBlock 2 P.2.length d 1

/-- The prenex sentence in the data `P`, `n`, `d`, `S`. -/
def encFormula (P : PresentationCode) (n d : ℕ) (S : List (List (ℕ × Bool))) :
    List (Bool × ℕ) × List (List Atom) :=
  ((encExVars P d S).map (fun i => (true, i)) ++ (encAllVars P d).map (fun i => (false, i)),
    qfAnd [(encEqs P d S).map fun p => (false, p)] (nonnegQF (encNonnegs P n d S)))

noncomputable section

/-- The sentence `Φ(P, n, c)` of `prop:mf-upper-bound` (printed sentence
`9eae4d68673a`), as a prenex formula with an `∃ … ∃ ∀ … ∀` prefix. -/
def encodePrenex
    (z : (PresentationCode × ℕ) × Manuscript.MFRecognition.Certificates.PrintedCertificate) :
    List (Bool × ℕ) × List (List Atom) :=
  encFormula z.1.1 z.1.2 (Manuscript.MFRecognition.Certificates.certDim z.2)
    (Manuscript.MFRecognition.Certificates.sWords z.1.1 z.1.2 z.2)

end

end GroupApproximation.Full.NN11b
