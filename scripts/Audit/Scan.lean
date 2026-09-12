import Lean
import Audit.DeclFilter

/-!
# Detectors that read the elaborated environment

Adapted from gnomon's `proofs/validation/code/Check.lean` and the budget list
at the head of its `check.py`.  The scans here are the ones that transfer to a
pure proof corpus; gnomon's genetics-specific budgets (conventions, regimes,
equilibria, domain-named arithmetic) do not, and its differential and
metamorphic tiers compare Lean against a shipped Rust implementation, which
this repository does not have.

WHY THIS IS A LEAN METAPROGRAM AND NOT A GREP.  Every question below is about
what a proof TERM is, or about what the kernel actually accepted, and neither
exists in the source text.  gnomon records that three separate text scans of
one such question returned 2, 16 and 3 hits with no overlap in names, and that
one of them reported a word out of a docstring as a theorem.  Lean is
whitespace-insensitive and its proofs are not a regular language; the
environment is the only authority.

## The scans

  AXIOM            transitive axiom closure outside classical Lean's three.
  LITERATURE_INPUT a premise, alias, embedded conclusion, or structure field
                   carrying a tagged transcription of an external theorem.
                   This is the laundering check: it follows definitional and
                   constructor closure instead of guessing from whether an
                   ordinary relation happens to have a closed example.
  TAUTOLOGY        the conclusion is syntactically one of the premises.
                   `theorem P_of_P (h : P) : P := h` has a clean axiom report.
  UNCONDITIONAL    a name promising an unconditional result on a type that
                   still carries Prop premises.
  INSTANCE_PREMISE a Prop-valued instance or implicit binder: an assumption
                   written in a syntax that hides it from the signature's
                   reader.
  EMPTY_PREMISE    a premise of an empty type; the theorem is vacuous.
  TRIVIAL          the conclusion is `True`.
  UNUSED           a binder occurring in neither the rest of the type nor the
                   accepted proof term.  KNOWN LOWER BOUND: `omega`, `linarith`
                   and `simp_all` splice every hypothesis in scope into the
                   certificate they emit, so a hypothesis they did not need
                   still occurs in the term and is invisible here.  There is no
                   false-positive direction: occurrence-freedom in a term the
                   kernel accepted proves the binder is deletable.
  DUPLICATE        one proposition proved twice under two names.
  RFL              the proof term is literally `Eq.refl`.
  STALE_DISCLAIMER a docstring describing the result as conditional, on a
                   statement that carries no Prop premise to be conditional
                   ON.  See `mentionsConditionality` for why this scan is
                   here and not in `check.py`.
-/

open Lean Meta Elab Command

namespace Audit

/-- One finding.  There is no severity field: the driver fails on any finding
under any tag, so a policy knob here would be a budget nobody is meant to
have.  (An earlier `fatal` flag documented a distinction the driver never
implemented; it is gone rather than misleading.) -/
structure Finding where
  tag : String
  decl : Name
  detail : String
  deriving Inhabited

/-- Was `n` compiled in a module of the corpus source tree?

Membership is deliberately by module, not namespace.  A project file may
open `Algebra`, `Ring`, or any other namespace; that must not let its
declarations escape the audit. -/
def inCorpusModule (env : Environment) (moduleRoot : Name) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx =>
      match env.header.moduleNames[idx.toNat]? with
      | some m => m.getRoot == moduleRoot
      | none => false
  | none => false

/-- Every hand-written declaration of the corpus, taken from the environment
rather than from a list, so a new module cannot escape the audit by not being
mentioned anywhere. -/
def corpusNames (env : Environment) (root : Name) : Array Name :=
  env.constants.fold (init := #[]) fun acc n _ =>
    if inCorpusModule env root n && userWritten env n then acc.push n else acc

/-- Strip leading binders, returning the body.

A theorem with binders stores its proof as `fun a b c ↦ Eq.refl _`, so testing
the head of the whole value asks whether a LAMBDA is `Eq.refl`, which is never
true.  gnomon records that the first version of its rfl scan did exactly this
and reported a clean-looking 0 of 0. -/
partial def stripLams : Expr → Expr
  | .lam _ _ b _ => stripLams b
  | .mdata _ b => stripLams b
  | e => e

/-- The value of a declaration.

NOT `ConstantInfo.value?`, which returns `none` for THEOREMS on this toolchain
even though the proof term is present and reachable by matching `.thmInfo`
directly.  Every scan that reads a proof term went silent when it trusted
`value?` -- including the axiom traversal, which stopped descending through
proofs entirely and would therefore have reported a clean closure for a corpus
with an admitted proof.  `scripts/Calibrate.lean` caught this, and it now
asserts the descent explicitly. -/
def valueOf? : ConstantInfo → Option Expr
  | .thmInfo v => some v.value
  | .defnInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

/-! ## AXIOM -/

/-- Axiom-closure traversal state. -/
structure AxiomState where
  visited : NameSet := {}
  axioms : Array Name := #[]

/-- Walk the transitive closure of `c` through the environment, accumulating
axioms.

Written out rather than calling `Lean.CollectAxioms.collect`, which this
toolchain's module system does not export to downstream code -- the public
`Lean.collectAxioms` wrapper is exported, but it allocates a fresh visited set
per call, and the whole point here is to sweep thousands of roots against ONE
shared set.  Per-root closures over a corpus this size are quadratic and do not
finish. -/
partial def collectFrom (env : Environment) (c : Name) : StateM AxiomState Unit := do
  unless (← get).visited.contains c do
    modify fun s => { s with visited := s.visited.insert c }
    match env.find? c with
    | some (.axiomInfo v) =>
        modify fun s => { s with axioms := s.axioms.push c }
        v.type.getUsedConstants.forM (collectFrom env)
    | some ci =>
        ci.type.getUsedConstants.forM (collectFrom env)
        if let some val := valueOf? ci then
          val.getUsedConstants.forM (collectFrom env)
        if let .inductInfo v := ci then
          v.ctors.forM (collectFrom env)
    | none => pure ()

/-- Axioms reachable from `roots`, sharing one visited set so the sweep over
the whole corpus stays a single traversal. -/
def axiomClosure (env : Environment) (roots : Array Name) : Array Name :=
  (((roots.forM (collectFrom env)).run {}).2).axioms

/-- Corpus declarations that reach `target`, capped: the point is to name a
place to start reading, not to enumerate every debtor. -/
def debtorsOf (env : Environment) (names : Array Name) (target : Name)
    (cap : Nat := 5) : Array Name := Id.run do
  let mut out := #[]
  for n in names do
    if out.size ≥ cap then break
    if (axiomClosure env #[n]).contains target then out := out.push n
  return out

def axiomScan (env : Environment) (names : Array Name) (allowed : List Name) :
    Array Finding := Id.run do
  let bad := (axiomClosure env names).filter fun a => !allowed.contains a
  let mut out := #[]
  for a in bad do
    out := out.push
      { tag := "AXIOM", decl := a,
        detail := s!"reached from {(debtorsOf env names a).toList}" }
  return out

/-! ## Shared expression classifiers -/

/-- Head constant of a type, if it has one. -/
def headConst? (e : Expr) : Option Name := e.getAppFn.constName?

/-- Prop-valued classes that are smuggled ASSUMPTIONS rather than ordinary
mathematical structure.

The distinction matters and getting it wrong cost this scan its first real
verdict.  `Finite` is `class Finite (α : Sort*) : Prop`, so a positive control
stated as `theorem isLEF_of_finite (G) [Group G] [Finite G] : IsLEF G` has a
Prop argument in its telescope -- and a rule that says "any Prop argument means
this is conditional" therefore reports `IsLEF` as never established, which is
precisely backwards: that theorem is the thing that establishes it.  A theorem
about a finite group is not assuming finite groups exist, it is naming the
category it is stated in.

A theorem carrying `[Fact (p < 1)]`, by contrast, IS assuming `p < 1`.  So an
instance binder counts as an obligation only when its class is one of these.
Written as unresolved name literals because this module must not import the
corpus or Mathlib. -/
def assumptionClasses : List Name := [`Fact, `Nonempty, `Inhabited]

/-- Prose describing a result as not yet established.

WHY THIS SCAN MOVED OUT OF `check.py`.  The source-text version asked only
whether a comment contains one of these words, and on this corpus that is a
question with four answers and no way to grade them: `glTwo_eq_elementary`
says "conditional on the rose-graph `K₁` input" and takes
`(hscalar : ScalarReduction _)` as a hypothesis, so the prose is exactly
right.  A text scan cannot see that hypothesis, so its only green state was
one where a true sentence had been deleted -- a gate that pays for silence
with documentation is worse than no gate.

The environment can see both halves, so the question becomes decidable and
sharper than the original: prose claiming conditionality on a statement with
NO Prop premise to be conditional on.  That is the disclaimer that is
genuinely stale, and it is the one worth failing a run over.

COVERAGE DROPPED IN THE MOVE, stated rather than left to be discovered:
module docstrings (`/-! ... -/`) belong to no declaration and are invisible
here, and so is prose on a `def`.  `BinaryLeavittDiagonal.lean`'s module
docstring was one of the four original hits, and is no longer checked by
anything. -/
def disclaimerPhrases : List String :=
  ["conditional", "proposed", "not proved", "unproved",
   "not yet proved", "assumed rather than", "remains an assumption"]

/-- Case-insensitive substring test against `disclaimerPhrases`.  `splitOn`
rather than a regex because Lean has no regex and this needs none. -/
def occurrenceCount (text needle : String) : Nat :=
  (text.splitOn needle).length - 1

def mentionsConditionality (s : String) : Bool :=
  let lower := s.toLower
  disclaimerPhrases.any fun p =>
    let hits := occurrenceCount lower p
    -- "unconditional(ly)" contains "conditional"; a substring hit inside a
    -- word that asserts the opposite is not a disclaimer.
    let shielded := occurrenceCount lower ("un" ++ p)
    -- "Conditional expectation" is a standard operator-algebraic noun, not
    -- a disclaimer about proof status.  Count it precisely instead of deleting
    -- the word "conditional" from otherwise useful documentation.
    let technical := if p == "conditional" then
      occurrenceCount lower "conditional expectation"
    else 0
    hits > shielded + technical

/-! ## Per-declaration shape scans -/

/-- Words that promise the HEADLINE result, not merely an existence statement.

`exists` and `_not_` were here and produced 1195 findings on a 5269-declaration
corpus, which is not a gate, it is a mailing list.  Lean's naming convention is
`exists_foo_of_bar` for conditional lemmas, so "exists" in a name carries no
claim at all; `_not_` fares the same.  What the root docstring actually
promises is that no CONDITIONAL result is advertised as THE existence theorem,
so these are the words that only a headline claim would use. -/
def claimWords : List String :=
  ["unconditional", "nonsofic", "theorema", "theoremb"]

/-- Declared directly in the corpus root namespace, i.e. `Corpus.foo` and not
`Corpus.Sub.foo`.  Headline results live at the root; the deep namespaces are
machinery, where a claim word is describing the subject matter rather than
making a claim. -/
def isHeadlineName : Name → Bool
  | .str (.str .anonymous _) _ => true
  | _ => false

/-- Does this name promise the headline result?

Matched against the LAST COMPONENT, never the full name.  Matching
`n.toString` tests the NAMESPACE too, and this corpus is called
`GroupApproximation` -- so the claim word "nonsofic" matched every single
declaration at the root and the scan reported 99 of them, `mul_mem_tableDomain`
first.  A corpus named after its own headline claim makes that mistake
invisible in the count and obvious in the first example. -/
def promisesClaim (n : Name) : Bool :=
  isHeadlineName n &&
    (match n with
     | .str _ f => claimWords.any fun w ↦ (f.toLower.splitOn w).length > 1
     | _ => false)

/-- Empty types: a premise of one makes the theorem vacuous. -/
def emptyTypes : List Name := [``False, ``Empty, ``PEmpty]

/-- Positions of `forallE` binders whose variable does not occur in the rest of
the TYPE.  Index 0 is outermost. -/
partial def typeUnused : Expr → Nat → Array (Nat × Name) → Array (Nat × Name)
  | .forallE nm _ b _, i, acc =>
      typeUnused b (i + 1) (if b.hasLooseBVar 0 then acc else acc.push (i, nm))
  | _, _, acc => acc

/-- Positions of `lam` binders unused in the proof TERM, and how many binders
the term abstracts.

The count matters.  A term may be eta-short of its type's telescope, and a
binder the term never abstracts is passed on to whatever the term reduces to
rather than discarded, so positions at or beyond the count are not reported.
That is the conservative direction. -/
partial def valUnused : Expr → Nat → Array Nat → (Array Nat × Nat)
  | .lam _ _ b _, i, acc =>
      valUnused b (i + 1) (if b.hasLooseBVar 0 then acc else acc.push i)
  | _, i, acc => (acc, i)

/-- Deliberate, by Lean's own convention for an intentionally unused binder --
the leading underscore its `unusedVariables` linter respects.  That keeps the
scan silent with no allow-list, and makes the underscore an admission a
reader can grep for rather than a way around the check. -/
def deliberate (n : Name) : Bool := n.toString.startsWith "_"

def declScan (env : Environment) (names : Array Name) : MetaM (Array Finding) := do
  let mut out := #[]
  let mut byType : Std.HashMap String Name := {}
  for n in names do
    let some ci := env.find? n | continue
    unless (match ci with | .thmInfo _ => true | _ => false) do continue

    -- TAUTOLOGY / UNCONDITIONAL / INSTANCE_PREMISE / EMPTY_PREMISE / TRIVIAL
    let shape ← forallTelescope ci.type fun args body ↦ do
      let mut taut := false
      let mut propPremise := false
      let mut hidden : Array Name := #[]
      let mut empty : Array Name := #[]
      for a in args do
        let t ← inferType a
        unless ← isProp t do continue
        propPremise := true
        if t == body then taut := true
        if let some h := headConst? t then
          if emptyTypes.contains h then empty := empty.push h
        -- Only instance-syntax ASSUMPTIONS.  Flagging every implicit Prop
        -- binder reported 256 declarations, nearly all of them ordinary
        -- side conditions written `{h : a ≠ b}` so they can be inferred from
        -- later arguments -- normal Lean, not smuggled content.
        let fv := a.fvarId!
        let bi := (← fv.getDecl).binderInfo
        if bi == .instImplicit &&
            (headConst? t |>.map assumptionClasses.contains |>.getD false) then
          hidden := hidden.push (← fv.getUserName)
      return (taut, propPremise, hidden, empty, body.isConstOf ``True)
    let (taut, propPremise, hidden, empty, trivialConcl) := shape

    if taut then
      out := out.push
        { tag := "TAUTOLOGY", decl := n,
          detail := "the conclusion is syntactically one of the premises" }
    let promisesUnconditional := promisesClaim n
    if propPremise && promisesUnconditional then
      out := out.push
        { tag := "UNCONDITIONAL", decl := n,
          detail := "the name promises an unconditional result; the type carries \
Prop premises" }
    unless hidden.isEmpty do
      out := out.push
        { tag := "ASSUMPTION_INSTANCE", decl := n,
          detail := s!"assumptions in instance syntax: {hidden.toList}" }
    unless empty.isEmpty do
      out := out.push
        { tag := "EMPTY_PREMISE", decl := n,
          detail := s!"premise of an empty type {empty.toList}: vacuously true" }
    if trivialConcl then
      out := out.push
        { tag := "TRIVIAL", decl := n, detail := "concludes `True`" }

    -- STALE_DISCLAIMER.  `propPremise` is the whole test: a docstring may call
    -- a result conditional exactly when the type says what it is conditional
    -- on.  Without that guard this is the text scan again, and it fires on
    -- four accurate sentences.
    if let some doc ← findDocString? env n then
      if mentionsConditionality doc && !propPremise then
        out := out.push
          { tag := "STALE_DISCLAIMER", decl := n,
            detail := "the docstring describes the result as conditional or \
unproved; the statement carries no Prop premise to be conditional on" }

    -- UNUSED
    let some val := valueOf? ci | continue
    let deadType := typeUnused ci.type 0 #[]
    let (deadVal, lams) := valUnused val 0 #[]
    let dead := deadType.filter fun (i, nm) ↦
      i < lams && deadVal.contains i && !deliberate nm
    unless dead.isEmpty do
      out := out.push
        { tag := "UNUSED", decl := n,
          detail := s!"binders occurring in neither the rest of the type nor the \
proof term: {(dead.map Prod.snd).toList}" }

    -- DUPLICATE
    let key := toString ci.type
    if let some other := byType[key]? then
      out := out.push
        { tag := "DUPLICATE", decl := n,
          detail := s!"same proposition already proved as {other}" }
    else
      byType := byType.insert key n

    -- RFL
    -- Both spellings.  `rfl` is its own constant (`theorem rfl := Eq.refl a`),
    -- and which one survives elaboration depends on how the proof was written;
    -- testing only `Eq.refl` reports a clean-looking 0 of 0 on a corpus full of
    -- `:= rfl`.
    let head := (stripLams val).getAppFn
    if head.isConstOf ``Eq.refl || head.isConstOf ``rfl then
      -- A `@[simp]` lemma proved by `rfl` is a deliberate API lemma -- it makes
      -- a definitional fact available to `simp`, which is the whole reason to
      -- state it.  96 of the corpus's hits were exactly that (`_apply`,
      -- `_val`, `_coe`).  The interesting case is an ordinary theorem, stated
      -- as though it had content, that holds by definition.
      unless (← getSimpTheorems).isLemma (.decl n) do
        out := out.push
          { tag := "RFL", decl := n,
            detail := "non-simp theorem whose proof term is `Eq.refl`" }
  return out

/-! ## LITERATURE_INPUT

Whether a premise is ordinary
mathematics or a transcription of someone's Theorem 4.1 is not a property of
the expression.  So the roster of transcriptions is CONFIG, owned by the
driver under the same custody as `allowedAxioms`, and this scan enforces a
ban: no user-written corpus declaration may take a tagged proposition as a
premise, and none may embed one in its conclusion except to prove it outright
(a conclusion whose head constant is itself tagged-reaching -- proving the
proposition, or an alias of it, is mathematics, not assumption).

Laundering is defeated by closure, not spelling: the ban extends to every
corpus constant from whose type, body, or constructor types a tagged name is
reachable, so an `abbrev` alias, a wrapper structure carrying the
transcription as a field, and a definition mentioning it in its body are all
exactly as banned as the name itself.

Population is by MODULE, not namespace: a corpus file can open any namespace
it likes, so membership is decided by where the declaration was compiled,
which the author of a corpus file cannot spoof. -/

/-- Corpus constants from which some tagged name is reachable through types,
bodies, and constructor types.  Always contains the tagged names themselves.
Propagation stays inside the corpus modules: nothing compiled before the
corpus can mention a corpus name, so the restriction loses nothing. -/
def taggedClosure (env : Environment) (moduleRoot : Name) (tagged : List Name) :
    NameSet := Id.run do
  let entries : Array (Name × Array Name) :=
    env.constants.fold (init := #[]) fun acc n ci =>
      if inCorpusModule env moduleRoot n then
        let m := ci.type.getUsedConstants
        let m := match valueOf? ci with
          | some v => m ++ v.getUsedConstants
          | none => m
        -- An inductive does not mention its constructors; add them, so a
        -- structure is contaminated when a field type is.
        let m := match ci with
          | .inductInfo v => m ++ v.ctors.toArray
          | _ => m
        acc.push (n, m)
      else acc
  let mut contaminated : NameSet := {}
  for t in tagged do contaminated := contaminated.insert t
  let mut changed := true
  while changed do
    changed := false
    for (n, ms) in entries do
      unless contaminated.contains n do
        if ms.any contaminated.contains then
          contaminated := contaminated.insert n
          changed := true
  return contaminated

/-- The types of the leading-`∀` premises.  Structural, not `MetaM`: the scan
must run on the Mathlib-free plants. -/
partial def premiseTypes : Expr → Array Expr
  | .forallE _ t b _ => #[t] ++ premiseTypes b
  | .mdata _ b => premiseTypes b
  | _ => #[]

/-- The body after the leading-`∀` telescope. -/
partial def conclusionOf : Expr → Expr
  | .forallE _ _ b _ => conclusionOf b
  | .mdata _ b => conclusionOf b
  | e => e

def literatureScan (env : Environment) (moduleRoot : Name)
    (tagged : List Name) : Array Finding := Id.run do
  if tagged.isEmpty then return #[]
  let contaminated := taggedClosure env moduleRoot tagged
  let corpus : Array (Name × ConstantInfo) :=
    env.constants.fold (init := #[]) fun acc n ci =>
      if inCorpusModule env moduleRoot n && userWritten env n then
        acc.push (n, ci)
      else acc
  let mut out := #[]
  for (n, ci) in corpus do
    let hit? := (premiseTypes ci.type).findSome? fun t =>
      t.getUsedConstants.find? contaminated.contains
    if let some bad := hit? then
      out := out.push
        { tag := "LITERATURE_INPUT", decl := n,
          detail := s!"premise mentions `{bad}`, which is or unfolds to a \
tagged literature transcription: the result is conditional on a theorem this \
corpus does not prove" }
    else
      let concl := conclusionOf ci.type
      let headTagged := match headConst? concl with
        | some h => contaminated.contains h
        | none => false
      if !headTagged then
        if let some bad := concl.getUsedConstants.find? contaminated.contains then
          out := out.push
            { tag := "LITERATURE_INPUT", decl := n,
              detail := s!"conclusion embeds `{bad}`, which is or unfolds to a \
tagged literature transcription, under a connective rather than proving it \
outright" }
  return out

/-! ## Driver -/

def allScans (env : Environment) (root : Name) (allowed : List Name) :
    MetaM (Array Finding) := do
  let names := corpusNames env root
  let mut out := axiomScan env names allowed
  out := out ++ (← declScan env names)
  return out

end Audit
