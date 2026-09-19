import GroupApproximation.Higman.HigmanPrimitiveRecursiveRunSemantics

/-!
# Reified primitive-recursive programs

`Nat.Primrec'` is a proposition indexed by a function.  It is ideal for
proving closure, but it cannot itself be the input of an executable compiler:
eliminating a proof in `Prop` cannot produce finite-presentation data.

This file introduces the corresponding syntax in `Type`.  Arity is part of
the type, so projection, composition, and primitive recursion cannot be
assembled with mismatched interfaces.  `Program.eval_primrec` proves that the
syntax has exactly the intended primitive-recursive semantics.  Subsequent
compiler files can recurse on `Program` while the semantic proof follows for
free from this theorem.
-/

namespace GroupApproximation
namespace Higman
namespace ReifiedPrimrec

/- A finite, arity-indexed syntax tree for primitive-recursive functions.

The composition constructor stores its finitely many inner programs in the
strictly-positive mutual vector below.  Unlike a function-valued field, this
is directly finite syntax and admits numerical serialization without choosing
any proof object.
-/
mutual
  /-- A finite, arity-indexed syntax tree for primitive-recursive functions. -/
  inductive Program : ℕ → Type
    | zero (n : ℕ) : Program n
    | succ : Program 1
    | get {n : ℕ} (i : Fin n) : Program n
    | comp {m n : ℕ} (outer : Program m)
        (inner : ProgramVec n m) : Program n
    | prec {n : ℕ} (base : Program n) (step : Program (n + 2)) : Program (n + 1)

  /-- A strictly-positive, length-indexed family of inner programs.  Using a
  mutual vector rather than nesting `Program` under `List.Vector` keeps the
  syntax accepted by Lean's positivity checker. -/
  inductive ProgramVec : ℕ → ℕ → Type
    | nil (n : ℕ) : ProgramVec n 0
    | cons {n m : ℕ} (head : Program n) (tail : ProgramVec n m) : ProgramVec n (m + 1)
end

mutual
  /-- Interpret a reified program as an ordinary function on vectors. -/
  def Program.eval : {n : ℕ} → Program n → List.Vector ℕ n → ℕ
    | _, .zero _, _ => 0
    | _, .succ, v => v.head + 1
    | _, .get i, v => v.get i
    | _, .comp outer inner, v =>
        outer.eval (List.Vector.ofFn fun i => (inner.evalAll v).get i)
    | _, .prec base step, v =>
        v.head.rec (base.eval v.tail)
          fun k old => step.eval (k ::ᵥ old ::ᵥ v.tail)

  /-- Evaluate all inner programs of a composition on the same input. -/
  def ProgramVec.evalAll {m n : ℕ} :
      ProgramVec n m → List.Vector ℕ n → List.Vector ℕ m
    | .nil _, _ => ⟨[], rfl⟩
    | .cons head tail, v => head.eval v ::ᵥ tail.evalAll v
end

@[simp] theorem Program.eval_zero (n : ℕ) (v : List.Vector ℕ n) :
    (Program.zero n).eval v = 0 := rfl

@[simp] theorem Program.eval_succ (v : List.Vector ℕ 1) :
    Program.succ.eval v = v.head + 1 := rfl

@[simp] theorem Program.eval_get {n : ℕ} (i : Fin n)
    (v : List.Vector ℕ n) :
    (Program.get i).eval v = v.get i := rfl

@[simp] theorem Program.eval_comp {m n : ℕ} (outer : Program m)
    (inner : ProgramVec n m) (v : List.Vector ℕ n) :
    (Program.comp outer inner).eval v =
      outer.eval (List.Vector.ofFn fun i => (inner.evalAll v).get i) := rfl

@[simp] theorem Program.eval_prec {n : ℕ} (base : Program n)
    (step : Program (n + 2)) (v : List.Vector ℕ (n + 1)) :
    (Program.prec base step).eval v =
      v.head.rec (base.eval v.tail)
        fun k old => step.eval (k ::ᵥ old ::ᵥ v.tail) := rfl

/- Every reified program denotes a primitive-recursive function.

This is the exact bridge into the already validated structural theorem
`Seq.higmanGenerated_natGraph_of_primrec'`.
-/
/-- Every reified program denotes a primitive-recursive function.  The mutual
induction motive for `ProgramVec` says that every evaluated coordinate is
primitive recursive, exactly the family demanded by composition. -/
theorem Program.eval_primrec {n : ℕ} (p : Program n) :
    Nat.Primrec' p.eval := by
  refine @Program.rec
    (fun n p => Nat.Primrec' p.eval)
    (fun n m p => ∀ i, Nat.Primrec' (fun v => (p.evalAll v).get i))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ _ p
  · intro n
    have hz : Nat.Primrec' (fun _ : List.Vector ℕ n => 0) := by
      simpa using Nat.Primrec'.comp
        (fun i : Fin 0 => Fin.elim0 i) Nat.Primrec'.zero
        (fun i : Fin 0 => Fin.elim0 i)
    simpa only [Program.eval] using hz
  · exact Nat.Primrec'.succ
  · intro n i
    exact Nat.Primrec'.get i
  · intro m n outer inner hOuter hInner
    exact Nat.Primrec'.comp
      (fun i v => (inner.evalAll v).get i) hOuter hInner
  · intro n base step hBase hStep
    exact Nat.Primrec'.prec hBase hStep
  · intro n i
    exact Fin.elim0 i
  · intro n m head tail hHead hTail i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [ProgramVec.evalAll] using hHead
    · simpa [ProgramVec.evalAll] using hTail j

/-- The natural graph computed by any reified program belongs to Higman's
generated family.  Unlike the earlier theorem on `Nat.Primrec'`, this theorem
has a syntax tree on which a finite-presentation compiler can recurse. -/
theorem Program.higmanGenerated_natGraph {n : ℕ} (p : Program n) :
    Seq.HigmanGenerated (Seq.natGraph p.eval) :=
  Seq.higmanGenerated_natGraph_of_primrec' p.eval_primrec

end ReifiedPrimrec
end Higman
end GroupApproximation
