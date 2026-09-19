import GroupApproximation.Higman.ReifiedPrimitiveRecursiveProgram

/-!
# Numerical codes for reified primitive-recursive programs

The semantic syntax in `ReifiedPrimitiveRecursiveProgram` is dependent.  The
compiler input, by contrast, must live in a fixed `Primcodable` type.  Here a
program is serialized as a list of natural numbers.  Every recursive child is
length-framed, so composition and primitive-recursion nodes can be decoded
without inspecting proofs or guessing a delimiter.

This first tranche includes the complete serialization format and executable,
primitive-recursive constructors for every program node.  Composition uses
the same primitive-recursive list-map/list-flatten combination as the existing
finite-relator compilers.
-/

namespace GroupApproximation
namespace Higman
namespace ReifiedPrimrecCode

open ReifiedPrimrec

/-- A numerical program word.  Lists of naturals are already `Primcodable`. -/
abbrev Code := List ℕ

/-- Prefix a child syntax tree by its length. -/
def frame (w : Code) : Code := w.length :: w

/-- The arity-`n` zero program. -/
def zeroCode (n : ℕ) : Code := [0, n]

/-- Unary successor. -/
def succCode : Code := [1]

/-- Projection `i` from an `n`-tuple. -/
def getCode (n i : ℕ) : Code := [2, n, i]

/-- Composition.  The header records the result arity and number of inner
programs; every child carries its own frame. -/
def compCode (n : ℕ) (outer : Code) (inner : List Code) : Code :=
  [3, n, inner.length] ++ frame outer ++ (inner.map frame).flatten

/-- Primitive recursion from an `n`-ary base and `(n+2)`-ary step. -/
def precCode (n : ℕ) (base step : Code) : Code :=
  [4, n] ++ frame base ++ frame step

mutual
  /-- Serialize a well-typed reified program. -/
  def encodeProgram : {n : ℕ} → Program n → Code
    | _, .zero n => zeroCode n
    | _, .succ => succCode
    | n, .get i => getCode n i
    | n, .comp outer inner => compCode n (encodeProgram outer) (encodePrograms inner)
    | _, @Program.prec n base step =>
        precCode n (encodeProgram base) (encodeProgram step)

  /-- Serialize the finite inner family of a composition. -/
  def encodePrograms : {m n : ℕ} → ProgramVec n m → List Code
    | _, _, .nil _ => []
    | _, _, .cons head tail => encodeProgram head :: encodePrograms tail
end

@[simp] theorem encodeProgram_zero (n : ℕ) :
    encodeProgram (Program.zero n) = zeroCode n := rfl

@[simp] theorem encodeProgram_succ :
    encodeProgram Program.succ = succCode := rfl

@[simp] theorem encodeProgram_get {n : ℕ} (i : Fin n) :
    encodeProgram (Program.get i) = getCode n i := rfl

@[simp] theorem encodeProgram_comp {m n : ℕ} (outer : Program m)
    (inner : ProgramVec n m) :
    encodeProgram (Program.comp outer inner) =
      compCode n (encodeProgram outer) (encodePrograms inner) := rfl

@[simp] theorem encodeProgram_prec {n : ℕ} (base : Program n)
    (step : Program (n + 2)) :
    encodeProgram (Program.prec base step) =
      precCode n (encodeProgram base) (encodeProgram step) := rfl

/-- Length framing is primitive recursive. -/
theorem primrec_frame : Primrec frame :=
  Primrec.list_cons.comp Primrec.list_length Primrec.id

/-- The zero-node constructor is primitive recursive. -/
theorem primrec_zeroCode : Primrec zeroCode :=
  Primrec.list_cons.comp (Primrec.const 0)
    (Primrec.list_cons.comp Primrec.id (Primrec.const []))

/-- The successor-node constructor is primitive recursive. -/
theorem primrec_succCode : Primrec (fun _ : Unit => succCode) :=
  Primrec.const _

/-- The projection-node constructor is primitive recursive in `(arity,index)`. -/
theorem primrec_getCode : Primrec (fun x : ℕ × ℕ => getCode x.1 x.2) :=
  Primrec.list_cons.comp (Primrec.const 2)
    (Primrec.list_cons.comp Primrec.fst
      (Primrec.list_cons.comp Primrec.snd (Primrec.const [])))

/-- The composition-node constructor is primitive recursive in its packed
arity, outer code, and finite inner-code list. -/
theorem primrec_compCode :
    Primrec (fun x : (ℕ × Code) × List Code =>
      compCode x.1.1 x.1.2 x.2) := by
  have hheader : Primrec (fun x : (ℕ × Code) × List Code =>
      ([3, x.1.1, x.2.length] : Code)) :=
    Primrec.list_cons.comp (Primrec.const 3)
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.list_cons.comp (Primrec.list_length.comp Primrec.snd)
          (Primrec.const [])))
  have houter : Primrec (fun x : (ℕ × Code) × List Code =>
      frame x.1.2) :=
    primrec_frame.comp (Primrec.snd.comp Primrec.fst)
  have hframeEntry : Primrec₂
      (fun (_ : (ℕ × Code) × List Code) (w : Code) => frame w) :=
    (primrec_frame.comp Primrec.snd).to₂
  have hinners : Primrec (fun x : (ℕ × Code) × List Code =>
      (x.2.map frame).flatten) :=
    Primrec.list_flatten.comp (Primrec.list_map Primrec.snd hframeEntry)
  have hfirst : Primrec (fun x : (ℕ × Code) × List Code =>
      ([3, x.1.1, x.2.length] : Code) ++ frame x.1.2) :=
    Primrec.list_append.comp hheader houter
  exact Primrec.list_append.comp hfirst hinners

/-- The primitive-recursion-node constructor is primitive recursive in its
packed arity, base code, and step code. -/
theorem primrec_precCode :
    Primrec (fun x : (ℕ × Code) × Code =>
      precCode x.1.1 x.1.2 x.2) := by
  have hheader : Primrec (fun x : (ℕ × Code) × Code =>
      ([4, x.1.1] : Code)) :=
    Primrec.list_cons.comp (Primrec.const 4)
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.const []))
  have hbase : Primrec (fun x : (ℕ × Code) × Code => frame x.1.2) :=
    primrec_frame.comp (Primrec.snd.comp Primrec.fst)
  have hstep : Primrec (fun x : (ℕ × Code) × Code => frame x.2) :=
    primrec_frame.comp Primrec.snd
  have hfirst : Primrec (fun x : (ℕ × Code) × Code =>
      ([4, x.1.1] : Code) ++ frame x.1.2) :=
    Primrec.list_append.comp hheader hbase
  exact Primrec.list_append.comp hfirst hstep

theorem computable_zeroCode : Computable zeroCode := primrec_zeroCode.to_comp

theorem computable_getCode : Computable (fun x : ℕ × ℕ => getCode x.1 x.2) :=
  primrec_getCode.to_comp

theorem computable_compCode :
    Computable (fun x : (ℕ × Code) × List Code =>
      compCode x.1.1 x.1.2 x.2) :=
  primrec_compCode.to_comp

theorem computable_precCode :
    Computable (fun x : (ℕ × Code) × Code =>
      precCode x.1.1 x.1.2 x.2) :=
  primrec_precCode.to_comp

end ReifiedPrimrecCode
end Higman
end GroupApproximation
