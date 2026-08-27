import GroupApproximation.Computability.SoficEnumeratedPi02
import GroupApproximation.Computability.MicrostateNormalForm

/-!
# Unitary microstates on the standard countable alphabet

`MFMicrostate.Microstate` carries one unitary per generator of a *finite*
presentation code.  A recursively enumerated presentation lives on the
countable alphabet `ℕ`, so its microstates carry one unitary per natural
number.  This file fixes that structure and the two challenge normal forms
built on it; the semantic equivalence with `IsOperatorMF` and the effective
checker live in separate modules.

A challenge is a finite list `W` of raw words, a relator-prefix length `N`,
and an accuracy index `k`.  It is answered when either some word of `W` is
trivial in the coded group (the challenge is void), or a microstate displaces
the relators at the addresses `0, …, N` by at most `1/(k+1)` and every word of
`W` by at least `1/2`.  The open variant uses strict inequalities and the
separation `1/3`; that is the shape the rational matrix certificates of
`MFRecognitionPi02` decide.

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

namespace GroupApproximation
namespace MFEnumeratedPi02

open Higman EnumeratedPresentationCodes
open SoficEnumeratedPi02 (relatorAt EnumWordProblem)

noncomputable section

/-- **A unitary microstate on the countable alphabet.**  A nonempty finite
model together with one unitary per natural number.  No finiteness clause is
imposed on the generator family: a challenge only ever reads finitely many
letters, and the effective bridge truncates at a letter bound. -/
structure NatMatrixMicrostate where
  /-- The finite model the unitaries act on. -/
  model : FiniteModel
  /-- The model is nonempty. -/
  card_pos : 0 < Fintype.card model
  /-- One unitary per letter. -/
  gen : ℕ → Matrix.unitaryGroup model ℂ

namespace NatMatrixMicrostate

/-- The homomorphism a microstate induces on the free group on `ℕ`. -/
def hom (M : NatMatrixMicrostate) :
    FreeGroup ℕ →* Matrix.unitaryGroup M.model ℂ :=
  FreeGroup.lift M.gen

@[simp] theorem hom_of (M : NatMatrixMicrostate) (i : ℕ) :
    M.hom (FreeGroup.of i) = M.gen i := by
  simp [hom]

/-- Operator-norm displacement of a free-group element. -/
def hlen (M : NatMatrixMicrostate) (x : FreeGroup ℕ) : ℝ :=
  opLength M.model (M.hom x)

/-- Operator-norm displacement of a raw word. -/
def len (M : NatMatrixMicrostate) (w : List (ℕ × Bool)) : ℝ :=
  M.hlen (freeEval w)

theorem hom_freeEval (M : NatMatrixMicrostate) (w : List (ℕ × Bool)) :
    M.hom (freeEval w) = evalRaw M.gen w := by
  have h := map_evalRaw M.hom FreeGroup.of w
  have hgen : (fun n => M.hom (FreeGroup.of n)) = M.gen :=
    funext fun n => M.hom_of n
  rw [show freeEval w = evalRaw FreeGroup.of w from rfl, h, hgen]

theorem len_def (M : NatMatrixMicrostate) (w : List (ℕ × Bool)) :
    M.len w = opLength M.model (evalRaw M.gen w) := by
  rw [len, hlen, hom_freeEval]

end NatMatrixMicrostate

/-! ## Challenges and answers -/

/-- The closed conditions a challenge asks a microstate for: the relators at
the first `N + 1` addresses are displaced by at most `1/(k+1)`, and every
listed word is displaced by at least `1/2`. -/
def PassesM (c : PresentationCode) (W : List (List (ℕ × Bool))) (N k : ℕ)
    (M : NatMatrixMicrostate) : Prop :=
  (∀ j, j ≤ N → M.hlen (relatorAt c j) ≤ 1 / ((k : ℝ) + 1)) ∧
    (∀ w ∈ W, 1 / 2 ≤ M.len w)

/-- **One closed challenge, answered.**  Either the challenge is void because
one of its words is trivial in the coded group, or a microstate meets it. -/
def AnswersM (c : PresentationCode) (W : List (List (ℕ × Bool))) (N k : ℕ) :
    Prop :=
  (∃ w ∈ W, EnumWordProblem c w) ∨ ∃ M : NatMatrixMicrostate, PassesM c W N k M

/-- The strict-open packet: relators displaced by less than `1/(k+1)`, listed
words displaced by more than `1/3`. -/
def PassesOpenM (c : PresentationCode) (W : List (List (ℕ × Bool))) (N k : ℕ)
    (M : NatMatrixMicrostate) : Prop :=
  (∀ j, j ≤ N → M.hlen (relatorAt c j) < 1 / ((k : ℝ) + 1)) ∧
    (∀ w ∈ W, 1 / 3 < M.len w)

/-- **One open challenge, answered.** -/
def AnswersOpenM (c : PresentationCode) (W : List (List (ℕ × Bool)))
    (N k : ℕ) : Prop :=
  (∃ w ∈ W, EnumWordProblem c w) ∨
    ∃ M : NatMatrixMicrostate, PassesOpenM c W N k M

end

end MFEnumeratedPi02
end GroupApproximation
