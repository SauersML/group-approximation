import GroupApproximation
import GroupApproximation.Endpoint.Audit
import Audit.DeclFilter
import Lean.Elab.Command

/-!
# How much of this development a reader has to read

`scripts/Audit.lean` answers "what does the proof rest on".  This script
answers the other question, the one a referee actually asks first: **to know
what the theorem says, how much of our own vocabulary must be understood?**

For each declaration named by a manuscript margin note -- the rosters
`metadata/CLAIM_DECLS.txt` and `metadata/NON_MF_CLAIM_DECLS.txt`, the same ones
`scripts/Signatures.lean` elaborates -- this walks the transitive closure of
**repository-local** constants reachable from its *statement*, and reports how
many there are and how many source lines they occupy.  Mathlib and core
constants are not counted: they are the shared vocabulary the reader is assumed
to have, and the whole point of the number is what is left over.

Definitions are unfolded and theorems are not: a definition appearing in a
statement changes what the statement means, whereas the proof of a lemma
appearing in it does not.  That is the difference between this closure and the
one `scripts/Audit.lean` computes, which traverses proofs precisely because it
is asking the other question.

Run after a build:

    lake env lean scripts/StatementClosure.lean

then commit the regenerated `metadata/AUDIT_SURFACE.md`.

## Why the number is worth having

The `leanprover/comparator` protocol -- as used by every Lean entry in the
Palomar registry (`palomar-registry.org`) -- reduces a formalization's trust
surface to a single `Challenge.lean` that imports only Mathlib, states the
theorem, and is the *entire* human audit surface; a mechanical check then
certifies that the library proves exactly that statement from the standard
axioms.  The registry grades a submission partly on how small that file is: the
Jordan curve theorem needs 8 lines, and an 805-line challenge is flagged as
exceeding the preferred audit surface.

This development cannot state its endpoints in Mathlib alone -- soficity, the
MF radical and the compression defect are its own definitions -- so a
`Challenge.lean` here would be exactly the closure computed below.  Measuring
it is the first half of that protocol and is worth having on its own: it turns
"the statement is readable" from an assertion into a number that moves when a
statement quietly acquires a new dependency.

The extraction design is prior art from `LionSR/MIPStarRE`'s
`scripts/comparator/extract_closure.lean`, which generates the challenge file
for the MIP* = RE low-degree-test entry.  That repository carries no licence,
so nothing is copied from it; the traversal below is written here, and answers
a deliberately different question (statement meaning, not kernel closure).
-/

open Lean Elab Command

namespace GroupApproximation.StatementClosure

/-- The module root of this development.  Constants outside it are Mathlib,
Batteries or core: shared vocabulary, not audit surface. -/
def libRoot : Name := `GroupApproximation

/-- The module a constant was declared in, if it came from an import. -/
def moduleOf? (env : Environment) (n : Name) : Option Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]?
  | none => none

/-- Was `n` declared in this development? -/
def isLocal (env : Environment) (n : Name) : Bool :=
  match moduleOf? env n with
  | some m => m.getRoot == libRoot
  | none => false

/-- The local constants that a declaration's *meaning* depends on.

The type always.  The value only for things that are not theorems or axioms:
unfolding a definition is part of understanding a statement that mentions it,
whereas a lemma's proof is not.  Constructors are followed so that a structure
in a statement drags in its fields. -/
def meaningRefs (env : Environment) (n : Name) : Array Name :=
  match env.find? n with
  | none => #[]
  | some ci =>
    let fromValue :=
      match ci with
      | .thmInfo _ => #[]
      | .axiomInfo _ => #[]
      | _ => match ci.value? with
             | some v => v.getUsedConstants
             | none => #[]
    let structural :=
      match ci with
      | .inductInfo v => v.ctors.toArray
      | .ctorInfo v => #[v.induct]
      | _ => #[]
    (ci.type.getUsedConstants ++ fromValue ++ structural).filter (isLocal env)

/-- Attribute a Lean-generated companion (`Foo.rec`, `Foo.proof_1`, a
projection) to the declaration a person actually wrote, so the report counts
declarations rather than elaboration artefacts.  `Audit.userWritten` is the
repository's single answer to "did a person write this"; the fuel is a
belt-and-braces bound, since the name always shortens. -/
partial def canonical (env : Environment) : Nat → Name → Name
  | 0, n => n
  | fuel + 1, n =>
    if Audit.userWritten env n then n
    else
      let p := n.getPrefix
      if p.isAnonymous || !env.contains p then n else canonical env fuel p

/-- Breadth-first transitive closure of `meaningRefs`, canonicalised. -/
partial def closureOf (env : Environment) : List Name → NameSet → NameSet
  | [], seen => seen
  | n :: rest, seen =>
    let c := canonical env 32 n
    if seen.contains c || !isLocal env c then closureOf env rest seen
    else closureOf env ((meaningRefs env n).toList ++ rest) (seen.insert c)

/-- Source lines occupied by `n`, or `0` when Lean recorded no range (which
happens for a compiler-generated declaration that survived canonicalisation). -/
def sourceLines (n : Name) : CommandElabM Nat := do
  match ← liftCoreM <| findDeclarationRanges? n with
  | some r => return r.range.endPos.line + 1 - r.range.pos.line
  | none => return 0

/-- The surface of one declaration: its statement closure and that closure's
total source size. -/
structure Surface where
  name : Name
  constants : Nat
  lines : Nat
  closure : NameSet

def surfaceOf (env : Environment) (n : Name) : CommandElabM Surface := do
  let cl := closureOf env (meaningRefs env n).toList {}
  let mut lines := 0
  for c in cl.toArray do
    lines := lines + (← sourceLines c)
  return { name := n, constants := cl.size, lines := lines, closure := cl }

def readRoster (path : System.FilePath) : CommandElabM (List Name) := do
  let input ← IO.FS.readFile path
  let names := input.splitOn "\n" |>.map (fun s => s.trimAscii.toString)
    |>.filter (· ≠ "") |>.map String.toName
  if names.isEmpty then
    throwError "{path}: no declarations listed; \
run `python3 scripts/claim_map.py --write` first"
  return names

/-- Pad a string on the right so the generated table stays column-aligned
without depending on a Markdown renderer. -/
def padRight (s : String) (width : Nat) : String :=
  s ++ String.ofList (List.replicate (width - s.length) ' ')

def section_ (env : Environment) (title : String) (path : System.FilePath) :
    CommandElabM (String × NameSet) := do
  let names ← readRoster path
  let mut rows : Array (Surface) := #[]
  for n in names do
    unless env.contains n do
      throwError "mapped declaration `{n}` is not in the environment; \
the lexical index and the elaborated library disagree"
    rows := rows.push (← surfaceOf env n)
  let mut union : NameSet := {}
  for r in rows do
    for c in r.closure.toArray do
      union := union.insert c
  let mut unionLines := 0
  for c in union.toArray do
    unionLines := unionLines + (← sourceLines c)
  let widest := rows.foldl (fun acc r => max acc (toString r.name).length) 0
  let mut out :=
    s!"\n## {title}\n\nRoster: `{path}` ({rows.size} declarations).  \
Union of all statement closures: **{union.size} local constants, \
{unionLines} source lines**.\n\n```\n\
{padRight "declaration" widest}  constants  lines\n"
  for r in rows do
    out := out ++ s!"{padRight (toString r.name) widest}  \
{padRight (toString r.constants) 9}  {r.lines}\n"
  out := out ++ "```\n"
  return (out, union)

run_cmd do
  let env ← getEnv
  let (mainSec, mainUnion) ← section_ env "Soficity manuscript"
    ("metadata" / "CLAIM_DECLS.txt")
  let (nonMFSec, nonMFUnion) ← section_ env "Non-MF manuscript"
    ("metadata" / "NON_MF_CLAIM_DECLS.txt")
  let mut union := mainUnion
  for c in nonMFUnion.toArray do
    union := union.insert c
  let mut lines := 0
  for c in union.toArray do
    lines := lines + (← sourceLines c)
  let header :=
    "<!-- generated by `lake env lean scripts/StatementClosure.lean`; \
do not edit by hand -->\n\n\
# Audit surface of the mapped declarations\n\n\
For every declaration a manuscript margin note names, the number of \
**repository-local** constants its statement transitively depends on, and the \
number of source lines those constants occupy.  Mathlib and core constants are \
not counted; definitions are unfolded and theorem proofs are not.  See \
`scripts/StatementClosure.lean` for what the number is for and why it is the \
first half of the `leanprover/comparator` protocol.\n\n\
Whole development: **" ++ toString union.size ++ " local constants, " ++
    toString lines ++ " source lines** in the union of every mapped \
statement's closure.\n"
  IO.FS.writeFile ("metadata" / "AUDIT_SURFACE.md")
    (header ++ mainSec ++ nonMFSec)
  logInfo m!"wrote metadata/AUDIT_SURFACE.md ({union.size} local constants, \
{lines} source lines)"

end GroupApproximation.StatementClosure
