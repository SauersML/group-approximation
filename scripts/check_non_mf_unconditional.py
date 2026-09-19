#!/usr/bin/env python3
"""Require every Lean declaration cited by the non-MF paper to be *mathematically*
unconditional.

`check_non_mf_zero_input.py` answers a different, much narrower question: does
the declaration *header* end at the colon?  That is a statement about where the
binders are printed, not about what the theorem assumes.  Both of these pass it:

    theorem closed_and_unconditional :
        ∀ (G : Type) [Group G], P G := ...

    theorem closed_and_conditional :
        ∀ (semantics : FinitePresentationSemantics Code)
          (_reduction : AdianRabinReduction sourceProperty (mfProperty semantics))
          (_undecidable : ¬ComputablePred sourceProperty),
          ¬ComputablePred (mfProperty semantics) := ...

The second is a closed Lean declaration whose mathematics is entirely
conditional: it imports Adian--Rabin as quantified reduction data.  Moving a
literature theorem from the header to the proposition changes nothing about
what has been proved, so a gate that only looks at the header certifies
nothing.  This script looks at the proposition.

## What counts as conditional

A *premise* is anything the caller must supply before the conclusion can be
used: a header binder, an in-scope `variable` the statement mentions, a binder
in the statement's leading `∀`-telescope, or a top-level `→` antecedent.

A premise is *conditional* when its type is a **corpus-defined** name that the
corpus never discharges.  Two halves, both necessary:

* **Corpus-defined.**  Mathlib and core names are not literature assumptions --
  they have Lean proofs behind them -- so `(n : ℕ)`, `[Group G]` and
  `(f : G →* H)` are never findings.  Only names this repository itself
  introduces with `structure`, `class`, `inductive`, or `def ... : Prop` are
  candidates.
* **Never discharged.**  A corpus-defined premise type is fine when the corpus
  can actually produce one: `[Group G]`-style data, `IsSofic G`,
  `HasKazhdanPropertyT G` and `KazhdanCompressionCore Γ E` are all inhabited by
  in-repository constructions, so assuming one assumes nothing unprovable.
  `AdianRabinReduction`, `DefectRoutingData` and `IsPointNormMatriciallyStable`
  are not: nothing in the corpus ever builds or concludes one, and nothing can
  without formalizing the cited theorem.

Discharge is a least fixed point, not a one-step lookup.  `DefectRoutingData`
*is* produced -- by `RoutingLemmaData.toDefectRoutingData`, which consumes a
`RoutingLemmaData`, which nothing produces.  A producer discharges its result
only when its own premises are discharged, so the whole chain is correctly
reported as open.

### Discharged, and discharged honestly

Being produced and being produced *honestly* are different facts, and the gate
reports both.  A datum whose only inhabitant rests on a `sorry` looks
discharged and is not, which is worse than an undischarged premise rather than
better: an undischarged premise is visibly a citation, and this one reads as
settled.  So the fixed point runs twice, once over every producer and once with
the `sorry`-tainted producers removed, and the difference is its own detector:

* `conditional-data` / `open-predicate` -- nothing in the corpus produces the
  premise's type.  The honest citation shape.
* `conditional-debt` -- the corpus produces it, but every producer rests on a
  `sorry`.

The case this was written for: `TheoremC.LiteratureInputs` is inhabited by
`TheoremCAssembly.literatureInputs`, which is assembled from three unfinished
literature theorems.  Before the split, every theorem taking `LiteratureInputs`
read as unconditional, because the gate asked whether a producer existed and
not whether it was honest.  `HullInputsCorrected`, by contrast, has an
untainted producer and stays clean, which is the test the detector has to pass:
it must discriminate, not condemn a whole surface.

Taint is transitive, and one refinement in its reference scan matters.  An
identifier whose first component is one of the declaration's own binder names
is NOT a reference: `exists_configuration (I : LiteratureInputs)` writes
`I.kotowskiOllivier`, a field of its hypothesis whose last component collides
with the name of a `sorry`-backed theorem elsewhere.  Reading that as a
reference tainted four Theorem C declarations that rest on no `sorry` at all.

This is a lexical scan, not a kernel fact.  The authoritative version is the
axiom set: `#audit_closed_axioms` and `scripts/Audit.lean` walk the transitive
closure and refuse anything past `propext`, `Classical.choice` and `Quot.sound`.
That needs a build, and this gate has to run in a checkout without one, so the
lexical scan is the cheap always-on ratchet and the kernel audit is what
settles it.  If the two ever disagree, the kernel wins.

Names may additionally be declared conditional by hand in the literature
roster (`--literature-roster`), which mirrors `Audit.literatureInputNames` in
`scripts/Audit.lean` on the Python side.  That roster is for transcriptions the
structural rule cannot see; it is not the primary mechanism, and it is empty in
both places today.

## The baseline, and why it is not a budget

The gate reports real findings today, and the mathematics that discharges them
does not exist yet.  Wiring it into CI as an unqualified gate would therefore
have exactly one effect: the step would be disabled again.  `--baseline`
records the findings that are *already known and already written up*, one line
each, so that the interesting event -- a **new** finding -- fails the run from
the day the step lands.

This is an itemized register, not a tolerance:

* every accepted finding is named by `(detector, declaration)`, so a finding of
  a different shape on the same declaration is new and fails;
* every entry must carry a written justification after `--`, so an unexplained
  line is a malformed baseline, not a quiet exemption;
* an entry matching nothing in this run is **stale and fatal**.  A discharged
  item cannot be left on the register to pre-authorize its own regression, and
  the register cannot outlive the problems it records -- the same discipline
  `KNOWN_CONDITIONAL_DECLARATIONS` is under, for the same reason.

There is no count anywhere in the mechanism, so there is no number a reviewer
can raise instead of fixing the corpus, and `--strict` ignores the register
entirely: that is the end state, once the register is empty.

The register does *not* record how many ways a declaration is conditional under
one detector.  Two undischarged packages in one telescope are one entry, and
discharging one of them leaves the entry live.  Finer keying would have to
quote premise text, which drifts on every rewording; the inventory carries the
per-premise account instead.

## Scope

The gate is lexical, like every other checker in this directory: it reads Lean
source, it does not elaborate it.  It therefore *under*-reports rather than
over-reports.  Known blind spots, all of which can only hide a finding:

* premise walking stops at a `let`/`letI`/`haveI` in the statement spine, so
  premises printed after one are not seen;
* a premise whose type is a bare logical formula (`∀ x, f x = 1`) is judged
  by the head symbols it mentions, not by whether that formula is provable;
* `variable` tracking is textual, so a `variable` that the elaborator includes
  through a dependency the statement does not name by hand is missed.

`--explain` prints the full classification, premise by premise, for review.
"""

from __future__ import annotations

import argparse
import re
import sys
import tempfile
from dataclasses import dataclass, field
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from lean_decls import MODIFIERS, _strip_block_comments


REPO = Path(__file__).resolve().parent.parent
DEFAULT_TEX = REPO / "non_mf_groups_exist.tex"
DEFAULT_ROSTER = REPO / "metadata" / "NON_MF_LITERATURE_INPUTS.txt"
DEFAULT_INVENTORY = REPO / "notes" / "NON_MF_CONDITIONAL_INVENTORY.md"
DEFAULT_BASELINE = REPO / "metadata" / "NON_MF_UNCONDITIONAL_BASELINE.txt"

LEAN_REF = re.compile(r"\\leanverified\{([^}]+)\}\{([^}]+)\}")

# Lean identifiers, including the subscripted and primed names this corpus uses.
IDENT = r"[^\W\d][\w'!?]*(?:\.[^\W\d][\w'!?]*)*"

DECL_KEYWORDS = ("theorem", "lemma", "def", "abbrev", "instance", "structure",
                 "class", "inductive", "opaque", "axiom")
# The keywords a badge may cite.  A cited `structure` or `class` is a category
# error rather than a conditionality finding, and is reported as such.
CITABLE = ("theorem", "lemma", "def", "abbrev", "instance")

OPENERS, CLOSERS = "([{⟨⦃", ")]}⟩⦄"

# Spine tokens that end premise walking.  `let`-style binders introduce a
# definition rather than a premise, and everything after one is out of scope
# for this lexical pass.
SPINE_STOPPERS = ("let ", "letI ", "let_fun ", "haveI ", "have ", "show ",
                  "if ", "match ", "fun ", "‹")

# Conditional endpoints the structural rule cannot see, because their premise
# is a plain sentence in Mathlib vocabulary rather than a corpus-defined
# package.  This roster lives in the gate, not in a data file, for the reason
# `Audit.literatureInputNames` does: the corpus must not be able to untag its
# own citations.  An entry that is no longer cited is reported as stale, so the
# roster cannot quietly outlive the problem it records.
#
# The roster is empty.  Two entries lived here until 2026-08-16 and were
# removed because the corpus discharged them, not because anyone tired of
# them; both removals are recorded here so that re-adding either without
# re-establishing its premise is a visible regression.
#
# * `ContinuumMultiplicity.manuscriptContinuumMultiplicity` was listed on the
#   grounds that "the corpus never exhibits one".  It now does:
#   `Monsters/NeumannContinuum.neumann_continuum_of_finitely_generated_groups`
#   builds a continuum of pairwise nonisomorphic finitely generated groups
#   outright, as a lamplighter over coset spaces of the free group, and the
#   badged declaration exhibits it as a conjunct rather than quantifying over
#   it.
# * `ClosedEnvelopeCompression.manuscriptEnvelopeCompressionBlind` was listed
#   on the grounds that "the corpus exhibits no `Closed` for which the
#   instance holds".  It now does:
#   `Algebra/ZariskiDescendingChain.wellFoundedLT_isZClosedSubgroup` is an
#   `instance`, proved from the Hilbert basis theorem through the
#   ideal--variety pair, and `Algebra/ZariskiEnvelopeEndpoint` packages the
#   whole premise tuple at it.  That entry additionally quoted the manuscript
#   as saying the chain condition "is the input the badge quantifies over
#   rather than proves"; that sentence does not occur in
#   `non_mf_groups_exist.tex` and appears to have been transcribed from an
#   early draft.
#
KNOWN_CONDITIONAL_DECLARATIONS: dict[str, str] = {}


# ---------------------------------------------------------------------------
# Lexical scanning primitives
# ---------------------------------------------------------------------------


def _depths(text: str) -> list[int]:
    """Bracket depth *before* each character of `text`."""
    depth = 0
    out = []
    for char in text:
        out.append(depth)
        if char in OPENERS:
            depth += 1
        elif char in CLOSERS:
            depth -= 1
    return out


def _find_top_level(text: str, needles: tuple[str, ...], start: int = 0) -> tuple[int, str]:
    """First occurrence of any needle at bracket depth zero, or `(-1, "")`."""
    depths = _depths(text)
    index = start
    while index < len(text):
        if depths[index] == 0:
            for needle in needles:
                if text.startswith(needle, index):
                    return index, needle
        index += 1
    return -1, ""


@dataclass
class Binder:
    """One `(a b : T)` / `{a : T}` / `[T]` group, or a bare `→` antecedent."""

    names: tuple[str, ...]
    type_text: str
    kind: str  # "explicit" | "implicit" | "instance" | "strict" | "arrow" | "variable"

    @property
    def head(self) -> str:
        return type_head(self.type_text)


def type_head(text: str) -> str:
    """The head symbol a premise type is *about*.

    `Nonempty (DefectRoutingData D)` is about `DefectRoutingData`; a negation
    or a nested quantifier is skipped through to what it constrains.
    """
    text = text.strip()
    for _ in range(8):
        stripped = text.lstrip("¬ ").strip()
        if stripped.startswith("∀") or stripped.startswith("∃"):
            comma, _ = _find_top_level(stripped, (",",))
            if comma == -1:
                break
            stripped = stripped[comma + 1:].strip()
        while stripped.startswith("(") and _matching(stripped, 0) == len(stripped) - 1:
            stripped = stripped[1:-1].strip()
        if stripped == text:
            break
        text = stripped
    match = re.match(IDENT, text)
    if match is None:
        return ""
    head = match.group(0)
    if head in ("Nonempty", "Inhabited", "Subsingleton", "IsEmpty"):
        rest = text[match.end():].strip()
        return type_head(rest) if rest else head
    return head


#: A premise that quantifies over a `Type` or `Sort` is not a fact about the
#: objects at hand; it is a general statement, which is to say a theorem.
QUANTIFIES_OVER_SORT = re.compile(r"(∀|\{|\()\s*[^:()]*:\s*(Type|Sort)\b")
SORTS = ("Prop", "Type", "Sort", "Type*")


def laundered_premises(declaration: "Declaration") -> list["Binder"]:
    """Premises whose head this gate reads from an ARROW ANTECEDENT.

    `type_head` skips through `∀`-binders and then reads the head of what it
    finds, so for

        (h : ∀ {G : Type u} [Group G] …, Suitable A N → ∃ p ms, …)

    it answers `Suitable` -- a name the corpus discharges -- when what the
    caller must supply is the whole implication, which nothing produces.  A
    theorem resting on such a premise REDUCES its conclusion to an unnamed
    statement; it does not construct one, and it must not discharge anything,
    or `HullRelatorStatement₂` and `ExistsHypEmbeddedConeOff₂` read as
    available while their literature input sits unproved inside a binder.

    The test is the one the separation lanes were given: an inline hypothesis
    is honest when the head read is the head of the premise's OWN conclusion,
    and launders when an antecedent's head is read instead.  Two exemptions
    keep it from swallowing ordinary mathematics.  A premise whose conclusion
    is a sort is DATA the caller picks freely --- `(P : (H : Type) → Prop)` is
    five predicates, not five theorems --- and a premise that quantifies over
    no sort at all is a hypothesis about the objects in hand, which is what
    most `→` premises are: 12096 declarations carry one, and treating those as
    reductions would cost 171 names their discharge for nothing.  With both
    exemptions the rule touches 65 declarations and moves exactly four names.
    """
    return [binder for binder in declaration.build_premises
            if is_laundered(binder)]


def is_laundered(binder: "Binder") -> bool:
    """Does `type_head` read this binder's head from an arrow antecedent?

    See `laundered_premises` for what the two exemptions are for."""
    if binder.kind == "instance":
        return False
    text = binder.type_text or ""
    conclusion = type_head(_strip_premises(text))
    if conclusion in SORTS:
        return False
    return bool(QUANTIFIES_OVER_SORT.search(text)) and type_head(text) != conclusion


def _matching(text: str, index: int) -> int:
    """Index of the bracket closing the opener at `index`, or `-1`."""
    depth = 0
    for position in range(index, len(text)):
        if text[position] in OPENERS:
            depth += 1
        elif text[position] in CLOSERS:
            depth -= 1
            if depth == 0:
                return position
    return -1


def parse_binder_group(text: str, index: int) -> tuple[Binder | None, int]:
    """Read one bracketed binder group starting at `text[index]`."""
    kinds = {"(": "explicit", "{": "implicit", "[": "instance", "⦃": "strict"}
    kind = kinds.get(text[index])
    if kind is None:
        return None, index
    close = _matching(text, index)
    if close == -1:
        return None, len(text)
    body = text[index + 1:close]
    colon, _ = _find_top_level(body, (":",))
    if colon == -1:
        # `[Group G]` and friends: the type is the whole body, unnamed.
        return Binder((), body.strip(), kind), close + 1
    names = tuple(body[:colon].split())
    return Binder(names, body[colon + 1:].strip(), kind), close + 1


def split_header(block: str, name_end: int) -> tuple[list[Binder], int]:
    """Binders printed *before* the colon, and the index just past that colon."""
    binders: list[Binder] = []
    index = name_end
    while index < len(block):
        while index < len(block) and block[index].isspace():
            index += 1
        if index >= len(block):
            break
        char = block[index]
        if char in "({[⦃":
            binder, index = parse_binder_group(block, index)
            if binder is None:
                break
            binders.append(binder)
            continue
        if char == ":" and not block.startswith(":=", index):
            return binders, index + 1
        break
    return binders, -1


def walk_premises(statement: str) -> list[Binder]:
    """Premises on the spine of a proposition: `∀`-telescopes and `→` antecedents."""
    premises: list[Binder] = []
    text = statement
    for _ in range(64):
        text = text.lstrip()
        if not text:
            break
        if any(text.startswith(stopper) for stopper in SPINE_STOPPERS):
            break
        if text[0] in "∀Π":
            index = 1
            while index < len(text):
                while index < len(text) and text[index].isspace():
                    index += 1
                if index >= len(text):
                    break
                if text[index] == ",":
                    index += 1
                    break
                if text[index] in "({[⦃":
                    binder, index = parse_binder_group(text, index)
                    if binder is None:
                        return premises
                    premises.append(binder)
                    continue
                # `∀ x y, ...`: untyped binders carry no premise content.
                match = re.match(rf"(?:{IDENT}|_)", text[index:])
                if match is None:
                    return premises
                index += match.end()
            text = text[index:]
            continue
        # Not a quantifier: look along the implication spine.  A depth-zero
        # connective reached before any arrow means the conclusion has started.
        position, token = _find_top_level(text, ("→", "∧", "↔", "∨", "∃", ":="))
        if position == -1 or token != "→":
            break
        premises.append(Binder((), text[:position].strip(), "arrow"))
        text = text[position + 1:]
    return premises


# ---------------------------------------------------------------------------
# Corpus index
# ---------------------------------------------------------------------------


@dataclass
class Declaration:
    keyword: str
    short_name: str
    path: Path
    line: int
    header: list[Binder]
    statement: str
    value: str = ""
    premises: list[Binder] = field(default_factory=list)
    variables: list[Binder] = field(default_factory=list)
    body_variables: list[Binder] = field(default_factory=list)

    @property
    def conclusion_head(self) -> str:
        return type_head(_strip_premises(self.statement))

    @property
    def cited_premises(self) -> list[Binder]:
        """What a caller of this declaration must supply."""
        return list(self.header) + list(self.variables) + list(self.premises)

    @property
    def build_premises(self) -> list[Binder]:
        """What *constructing* this declaration needed, proof body included."""
        return list(self.header) + list(self.body_variables) + list(self.premises)


def _strip_premises(statement: str) -> str:
    """The conclusion: the statement with its spine premises removed."""
    text = statement
    for _ in range(64):
        text = text.lstrip()
        if not text:
            return text
        if any(text.startswith(stopper) for stopper in SPINE_STOPPERS):
            return text
        if text[0] in "∀Π":
            comma, _ = _find_top_level(text, (",",))
            if comma == -1:
                return text
            text = text[comma + 1:]
            continue
        position, token = _find_top_level(text, ("→", "∧", "↔", "∨", "∃", ":="))
        if position == -1 or token != "→":
            return text
        text = text[position + 1:]
    return text


EXISTS_BINDER = re.compile(rf"∃[^,∃]*?:\s*({IDENT})")
NONEMPTY_ARG = re.compile(rf"Nonempty\s*\(?\s*({IDENT})")
REFUTATION = re.compile(r"¬\s*∃|IsEmpty|¬\s*Nonempty")


def is_refutation(conclusion: str) -> bool:
    """Does this conclusion deny its head rather than exhibit one?

    `¬ ∃`, `IsEmpty` and `¬ Nonempty` are the shapes a refuted *structure*
    takes.  A refuted `def … : Prop` is written `¬ P`, which matches none of
    them and which `type_head` reads as `P`, so the proof that a citation is
    **false** used to register as a producer of it and every consumer of the
    refuted name read as discharged.  That is backwards, and this repository
    refutes citations on purpose: `OsinTheorem24`, `DGOTheorem611`,
    `HullInputs`, `RelatorSeparation` and `ZpowersConeOffEmbedding` are all
    refuted here, and all of them used to count as available.
    """
    return conclusion.lstrip().startswith("¬") or bool(REFUTATION.search(conclusion))


def produced_heads(declaration: Declaration) -> set[str]:
    """Every name this declaration exhibits an inhabitant of.

    The head of the conclusion is the obvious one.  A theorem concluding
    `∃ M : NormModel …, P M` or `Nonempty (StrictKazhdanCompression …)` also
    produces one, and missing those would report an inhabited structure as
    open.  Refutations exhibit nothing, so they produce nothing at all --- the
    head included, which is the whole of `is_refutation`'s reason to exist.
    """
    conclusion = _strip_premises(declaration.statement)
    if is_refutation(conclusion):
        return set()
    heads = {type_head(conclusion)}
    heads |= {m.group(1).rsplit(".", 1)[-1]
              for m in EXISTS_BINDER.finditer(conclusion)}
    heads |= {m.group(1).rsplit(".", 1)[-1]
              for m in NONEMPTY_ARG.finditer(conclusion)}
    return {head for head in heads if head}


DECL_START = re.compile(
    rf"(?m)^{MODIFIERS}(?P<kw>{'|'.join(DECL_KEYWORDS)})\s+(?P<name>{IDENT})")
VARIABLE_START = re.compile(r"(?m)^variable\b")
SCOPE_LINE = re.compile(
    rf"(?m)^(?P<kind>namespace|section|end)\b(?:\s+(?P<name>{IDENT}))?")


def scan_module(path: Path) -> dict[str, Declaration]:
    """Every declaration in `path`, with its header, statement, and open variables."""
    source = _strip_block_comments(path.read_text(encoding="utf-8"))
    # `variable` blocks open a scope level; `end` closes one and everything the
    # levels above it introduced.
    scopes: list[list[Binder]] = [[]]
    events: list[tuple[int, str, object]] = []
    for match in DECL_START.finditer(source):
        events.append((match.start(), "decl", match))
    for match in SCOPE_LINE.finditer(source):
        events.append((match.start(), "scope", match))
    for match in VARIABLE_START.finditer(source):
        events.append((match.start(), "variable", match))
    events.sort(key=lambda event: event[0])

    declarations: dict[str, Declaration] = {}
    for position, kind, match in events:
        if kind == "scope":
            if match.group("kind") == "end":
                if len(scopes) > 1:
                    scopes.pop()
            else:
                scopes.append([])
            continue
        if kind == "variable":
            line_end = source.find("\n", position)
            body = source[position + len("variable"):
                          line_end if line_end != -1 else len(source)]
            # A `variable` command may wrap; keep reading indented continuations.
            cursor = line_end
            while cursor != -1:
                nxt = source.find("\n", cursor + 1)
                chunk = source[cursor + 1: nxt if nxt != -1 else len(source)]
                if not chunk[:1].isspace() or not chunk.strip():
                    break
                body += " " + chunk
                cursor = nxt
            index = 0
            while index < len(body):
                while index < len(body) and body[index].isspace():
                    index += 1
                if index >= len(body) or body[index] not in "({[⦃":
                    break
                binder, index = parse_binder_group(body, index)
                if binder is None:
                    break
                scopes[-1].append(Binder(binder.names, binder.type_text, "variable"))
            continue

        # A declaration.  Its block runs to the next column-zero command.
        next_start = len(source)
        for other_position, other_kind, _other in events:
            if other_position > position:
                next_start = other_position
                break
        block = source[position:next_start]
        name_end = match.end() - position
        header, colon = split_header(block, name_end)
        body = block[colon:] if colon != -1 else ""
        # The signature is the type; everything past the first depth-zero `:=`
        # or `where` is the proof.  A `letI ... :=` inside the type truncates
        # early, which can only hide a premise, never invent one.
        cut, token = _find_top_level(body, (":=", " where\n", " where "))
        statement = body if cut == -1 else body[:cut]
        value = body[cut + len(token):] if cut != -1 and token == ":=" else ""
        declaration = Declaration(
            keyword=match.group("kw"),
            short_name=match.group("name").rsplit(".", 1)[-1],
            path=path,
            line=source.count("\n", 0, position) + 1,
            header=header,
            statement=statement,
            value=value,
        )
        declaration.premises = walk_premises(statement)
        # A section `variable` is an input only when the declaration does not
        # rebind that name itself; a shadowed variable is never included.
        bound = {name for binder in header + declaration.premises
                 for name in binder.names}
        open_variables = [binder for scope in scopes for binder in scope]

        def mentioned(binder: Binder, text: str) -> bool:
            if not binder.names or bound & set(binder.names):
                return False
            return any(re.search(rf"(?<![\w'.]){re.escape(name)}(?![\w'])", text)
                       for name in binder.names)

        declaration.variables = [b for b in open_variables if mentioned(b, statement)]
        declaration.body_variables = [b for b in open_variables if mentioned(b, body)]
        declarations[declaration.short_name] = declaration
    return declarations


@dataclass
class Corpus:
    declarations: dict[Path, dict[str, Declaration]]
    corpus_types: set[str]
    corpus_props: set[str]
    discharged: set[str]
    by_name: dict[str, Declaration] = field(default_factory=dict)
    corpus_namespaces: set[str] = field(default_factory=set)
    #: Discharged by at least one producer that does not rest on a `sorry`.
    #: A subset of `discharged`; the difference is the `conditional-debt`
    #: surface.
    discharged_honestly: set[str] = field(default_factory=set)
    #: Short names whose proof rests on a `sorry`, directly or transitively.
    sorry_tainted: set[str] = field(default_factory=set)

    def resolve(self, head: str) -> str:
        """`Ns.Foo` written from outside `Ns` is the same name as `Foo`.

        `type_head` reports a premise or conclusion head exactly as written, so
        one corpus name has two spellings depending on whether the writer was
        inside its namespace.  Both sides of the discharge fixpoint compare
        against short names, so the qualified spelling silently dropped out of
        *both*: a theorem concluding `HNNTorsionFree.ExistsCyclicConjugate`
        produced nothing, and a premise requiring it needed nothing.  The
        second half is the dangerous one -- it is a conditional the gate did
        not report.

        Only a prefix that is really a corpus namespace is stripped.  Matching
        on the last component alone would collide with Mathlib: the corpus
        defines `IsComplete`, and so does Mathlib.
        """
        prefix, _, last = head.rpartition(".")
        if prefix and prefix in self.corpus_namespaces and self.is_corpus_name(last):
            return last
        return head

    def is_corpus_name(self, head: str) -> bool:
        return head in self.corpus_types or head in self.corpus_props

    def unfolded_premises(
        self, declaration: Declaration, depth: int = 3
    ) -> list[tuple[Binder, str]]:
        """Premises of `declaration`, plus those hidden inside named `Prop`s.

        `theorem endpoint : ManuscriptCentralSignCriterion` is closed, has no
        spine premises, and can still assume anything at all -- the hypotheses
        live one indirection away, in the definition of that `Prop`.  Following
        the chain is the difference between reading a type and reading a claim.
        """
        return self._unfold(declaration, depth)[0]

    def unfolded_conclusion(self, declaration: Declaration, depth: int = 3) -> str:
        """The conclusion text, named `Prop`s followed through."""
        return self._unfold(declaration, depth)[1]

    def _unfold(
        self, declaration: Declaration, depth: int
    ) -> tuple[list[tuple[Binder, str]], str]:
        collected = [(binder, "") for binder in declaration.cited_premises]
        conclusions = [_strip_premises(declaration.statement)]
        current = declaration
        seen: set[str] = set()
        for _ in range(depth):
            head = current.conclusion_head
            if head in seen or head not in self.corpus_props:
                break
            target = self.by_name.get(head)
            if target is None or target.keyword not in ("def", "abbrev"):
                break
            seen.add(head)
            # A named `Prop` carries its content in its *value*, not its type:
            # `def S : Prop := ∀ (h : Literature), …` has type `Prop` and
            # assumes `Literature`.  The parameters of the definition itself
            # are instantiated by the caller and are not premises.
            body_premises = walk_premises(target.value)
            collected += [(binder, f"through `{head}`, ")
                          for binder in body_premises + target.variables]
            conclusions.append(_strip_premises(target.value))
            current = Declaration(
                keyword=target.keyword, short_name=target.short_name,
                path=target.path, line=target.line, header=[],
                statement=target.value, premises=body_premises,
            )
        return collected, "\n".join(conclusions)


# A `sorry`-family token, on a word boundary and not after a dot, so that a
# field or namespace component spelled `sorry` is not mistaken for the tactic.
SORRY_TOKEN = re.compile(r"(?<![\w.])(?:sorry|sorryAx|admit)(?![\w'])")

# `--strict` is the completion gate for the whole non-MF manuscript, not only
# for the declarations carrying a `\leanverified` badge.  Some central results
# (most importantly Theorem C) are assembled in this tree and are discussed in
# the paper without a badge on every intervening sentence.  A badge-only scan
# therefore used to print "unconditional" while `TheoremCAssembly.lean` still
# contained six `sorry`s.  Scan the authoritative manuscript source tree as a
# separate invariant so that cannot happen again.
NON_MF_MANUSCRIPT_ROOT = Path("GroupApproximation/Manuscript/NonMF")
AXIOM_DECL = re.compile(rf"^\s*{MODIFIERS}axiom\s+", re.UNICODE)


def manuscript_source_integrity_problems(root: Path) -> list[str]:
    """Direct placeholders or axiom declarations in the non-MF manuscript.

    This deliberately complements, rather than replaces, the transitive
    declaration analysis below.  The latter starts from badges; this source
    invariant covers every manuscript declaration, including unbadged
    assembly modules.  Block and line comments are ignored, so prose about a
    remaining `sorry` does not itself fail the gate.
    """
    source_root = root / NON_MF_MANUSCRIPT_ROOT
    if not source_root.is_dir():
        return [f"missing non-MF manuscript source tree {source_root}"]
    problems: list[str] = []
    for path in sorted(source_root.rglob("*.lean")):
        source = _strip_block_comments(path.read_text(encoding="utf-8"))
        for line_number, raw in enumerate(source.splitlines(), start=1):
            code = raw.split("--", 1)[0]
            if SORRY_TOKEN.search(code):
                problems.append(
                    f"{path.relative_to(root)}:{line_number}: "
                    "placeholder in non-MF manuscript source"
                )
            if AXIOM_DECL.match(code):
                problems.append(
                    f"{path.relative_to(root)}:{line_number}: "
                    "axiom declaration in non-MF manuscript source"
                )
    return problems

IDENTIFIER_PATH = re.compile(IDENT)


def sorry_tainted(
    modules: dict[Path, dict[str, Declaration]],
) -> set[str]:
    """Short names whose proof rests on a `sorry`, directly or transitively.

    A declaration is tainted when its own body carries a `sorry`-family token,
    or when it references a tainted declaration.

    An identifier whose first component is one of the declaration's own binder
    names is NOT a reference.  `exists_configuration (I : LiteratureInputs)`
    writes `I.chiodo` and `I.kotowskiOllivier`: those are fields of its
    hypothesis, and their last components collide with the names of the
    `sorry`-backed theorems that inhabit `LiteratureInputs` elsewhere.  Reading
    them as references tainted `exists_configuration`, and through it
    `Configuration`, `manuscriptTorsionFreeFullMFRadical` and both printed forms
    of Theorem C -- four declarations that rest on no `sorry` at all.  Dropping
    projections off a declaration's own binders is what keeps the detector from
    condemning honest work.

    This is a lexical scan, not a kernel fact.  The authoritative version is the
    axiom set: `#audit_closed_axioms` and `scripts/Audit.lean` walk the
    transitive closure and refuse anything past `propext`, `Classical.choice`
    and `Quot.sound`.  That needs a build, and this gate has to run in a
    checkout without one, so the lexical scan is the cheap always-on ratchet
    and the kernel audit is what settles it.  If the two ever disagree, the
    kernel wins.
    """
    declarations: dict[str, Declaration] = {}
    for module in modules.values():
        declarations.update(module)

    references: dict[str, set[str]] = {}
    for name, declaration in declarations.items():
        own = {
            binder_name
            for group in (declaration.header, declaration.premises,
                          declaration.variables, declaration.body_variables)
            for binder in (group or ())
            for binder_name in binder.names
        }
        seen: set[str] = set()
        for token in IDENTIFIER_PATH.findall(declaration.value or ""):
            root, _, _ = token.partition(".")
            if root in own:
                continue
            seen.add(token.rsplit(".", 1)[-1])
        references[name] = seen

    tainted = {
        name for name, declaration in declarations.items()
        if SORRY_TOKEN.search(declaration.value or "")
    }
    changed = True
    while changed:
        changed = False
        for name, refs in references.items():
            if name in tainted:
                continue
            if refs & tainted:
                tainted.add(name)
                changed = True
    return tainted


def build_corpus(root: Path) -> Corpus:
    """Index the Lean corpus and compute which corpus-defined names it discharges."""
    modules: dict[Path, dict[str, Declaration]] = {}
    corpus_namespaces: set[str] = set()
    for path in sorted((root / "GroupApproximation").rglob("*.lean")):
        if path.name.startswith("._"):
            continue
        modules[path] = scan_module(path)
        # Namespaces the corpus actually opens, so `resolve` can tell a corpus
        # name wearing its namespace from a Mathlib name that merely ends the
        # same way.  Both the bare token and the enclosing path are recorded:
        # `A.B.Foo` may be written against `namespace A.B` or against a
        # `namespace B` nested inside a `namespace A`.
        stack: list[str] = []
        source = _strip_block_comments(path.read_text(encoding="utf-8"))
        for match in SCOPE_LINE.finditer(source):
            kind, name = match.group("kind"), match.group("name")
            if kind == "namespace" and name:
                stack.append(name)
                corpus_namespaces.add(name)
                corpus_namespaces.add(".".join(stack))
            elif kind == "end" and stack and name == stack[-1]:
                stack.pop()

    corpus_types: set[str] = set()
    corpus_props: set[str] = set()
    for declarations in modules.values():
        for declaration in declarations.values():
            if declaration.keyword in ("structure", "class", "inductive"):
                corpus_types.add(declaration.short_name)
            elif declaration.keyword in ("def", "abbrev"):
                if type_head(_strip_premises(declaration.statement)) == "Prop":
                    corpus_props.add(declaration.short_name)

    corpus_names = corpus_types | corpus_props

    def resolve(head: str) -> str:
        """`Corpus.resolve`, before the `Corpus` exists to carry it."""
        prefix, _, last = head.rpartition(".")
        if prefix and prefix in corpus_namespaces and last in corpus_names:
            return last
        return head

    # producers[head] = (producing declaration, its premise heads), one entry
    # per declaration producing `head`.  The name is kept because whether the
    # producer rests on a `sorry` is what separates the two conditional
    # detectors below.
    producers: dict[str, list[tuple[str, set[str]]]] = {}
    for declarations in modules.values():
        for declaration in declarations.values():
            if declaration.keyword in ("structure", "class", "inductive", "axiom",
                                       "opaque"):
                continue
            if laundered_premises(declaration):
                # A reduction to a statement written inside a binder, not a
                # construction: see `laundered_premises`.  It proves its
                # conclusion only to a caller who already has the literature.
                continue
            heads = {resolve(head) for head in produced_heads(declaration)} & corpus_names
            # A self-requirement is kept, not dropped: a transport
            # `ProperProjectionCompression A → ProperProjectionCompression B`
            # produces nothing until something produces its input.
            needs = {
                resolve(binder.head) for binder in declaration.build_premises
                if resolve(binder.head) in corpus_names
            }
            for head in heads:
                if declaration.short_name == head:
                    continue  # the definition of a name is not a proof of it
                producers.setdefault(head, []).append(
                    (declaration.short_name, needs))

    by_name: dict[str, Declaration] = {}
    for declarations in modules.values():
        by_name.update(declarations)

    # Being produced and being produced *honestly* are different facts, and the
    # gate needs both: a datum whose only inhabitant rests on a `sorry` looks
    # discharged and is not.  Run the same fixed point twice, once over every
    # producer and once with the tainted producers removed.
    tainted = sorry_tainted(modules)
    honest_producers = {
        head: [needs for name, needs in entries if name not in tainted]
        for head, entries in producers.items()
    }
    all_producers = {
        head: [needs for _name, needs in entries]
        for head, entries in producers.items()
    }

    def fixed_point(sources: dict[str, list[set[str]]]) -> set[str]:
        """Least fixed point: a name is discharged once some producer's own
        requirements are all discharged."""
        out: set[str] = set()
        changed = True
        while changed:
            changed = False
            for head, requirement_sets in sources.items():
                if head in out:
                    continue
                if any(needs <= out for needs in requirement_sets):
                    out.add(head)
                    changed = True
        return out

    return Corpus(modules, corpus_types, corpus_props,
                  fixed_point(all_producers), by_name, corpus_namespaces,
                  fixed_point(honest_producers), tainted)


# ---------------------------------------------------------------------------
# The gate
# ---------------------------------------------------------------------------


@dataclass
class Finding:
    anchor: str
    declaration: str
    detector: str
    detail: str

    @property
    def key(self) -> tuple[str, str]:
        """What the baseline records: the shape of the defect, and where.

        Not the anchor (the manuscript is edited concurrently and anchors
        move) and not the detail (it quotes premise text, which rewords).
        """
        return (self.detector, self.declaration)


# Every detector `classify` can emit.  A baseline entry naming anything else is
# a typo, and a typo that silently matches nothing would look exactly like a
# discharged item.
DETECTORS = (
    "buried-conditional",
    "conditional-data",
    "conditional-debt",
    "carrier-data",
    "carrier-debt",
    "definition-only",
    "header-binder",
    "inlined-statement",
    "known-conditional",
    "literature-input",
    "open-predicate",
    "open-variable",
)


@dataclass(frozen=True)
class BaselineEntry:
    detector: str
    declaration: str
    note: str
    line: int

    @property
    def key(self) -> tuple[str, str]:
        return (self.detector, self.declaration)


# `<detector> <declaration>  -- why this is on the register`.  The note is
# mandatory: an entry nobody could explain is not a decision, it is a leak.
BASELINE_LINE = re.compile(
    r"^(?P<detector>[a-z][a-z-]*)\s+(?P<declaration>\S+)\s+--\s*(?P<note>\S.*)$")


def read_baseline(path: Path) -> tuple[dict[tuple[str, str], BaselineEntry], list[str]]:
    """Parse the accepted-findings register.  A missing file is an empty one."""
    problems: list[str] = []
    if not path.is_file():
        return {}, problems
    try:
        text = path.read_text(encoding="utf-8")
    except OSError as error:
        return {}, [f"cannot read baseline {path}: {error}"]
    entries: dict[tuple[str, str], BaselineEntry] = {}
    for number, raw in enumerate(text.splitlines(), start=1):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        match = BASELINE_LINE.match(line)
        if match is None:
            problems.append(
                f"{path.name}:{number}: malformed entry; the form is "
                "`<detector> <declaration>  -- why it is accepted`"
            )
            continue
        entry = BaselineEntry(match.group("detector"),
                              match.group("declaration"),
                              match.group("note").strip(), number)
        if entry.detector not in DETECTORS:
            problems.append(
                f"{path.name}:{number}: unknown detector `{entry.detector}`; "
                f"expected one of {', '.join(DETECTORS)}"
            )
            continue
        if entry.key in entries:
            problems.append(
                f"{path.name}:{number}: duplicate entry for "
                f"{entry.detector} {entry.declaration}"
            )
            continue
        entries[entry.key] = entry
    return entries, problems


def apply_baseline(
    findings: list[Finding], baseline: dict[tuple[str, str], BaselineEntry]
) -> tuple[list[Finding], list[Finding], list[BaselineEntry]]:
    """Split findings into accepted and new, and report entries that expired.

    A stale entry is a finding that has been discharged while its exemption was
    left behind.  Reporting it is what makes the register one-way: it cannot
    accumulate permissions for defects that no longer exist, and therefore
    cannot pre-authorize their return.
    """
    accepted: list[Finding] = []
    new: list[Finding] = []
    matched: set[tuple[str, str]] = set()
    for finding in findings:
        if finding.key in baseline:
            matched.add(finding.key)
            accepted.append(finding)
        else:
            new.append(finding)
    stale = [entry for key, entry in baseline.items() if key not in matched]
    return accepted, new, sorted(stale, key=lambda e: e.line)


def render_baseline(
    findings: list[Finding], baseline: dict[tuple[str, str], BaselineEntry]
) -> str:
    """The register text for `--write-baseline`, keeping hand-written notes."""
    header = (
        "# Findings of `scripts/check_non_mf_unconditional.py` that are known,\n"
        "# written up, and not yet discharged.  One line per accepted finding:\n"
        "#\n"
        "#     <detector> <declaration>  -- why it is accepted\n"
        "#\n"
        "# This register is not a budget.  A finding not listed here fails the\n"
        "# gate, and a line here that matches nothing fails it too -- so a\n"
        "# discharged item cannot be left behind to license its own return.\n"
        "# Every line must correspond to a row of notes/NON_MF_CONDITIONAL_INVENTORY.md.\n"
        "# Regenerate with:\n"
        "#\n"
        "#     python3 scripts/check_non_mf_unconditional.py --write-baseline\n"
        "#\n"
        "# and delete a line the moment its mathematics lands.\n"
    )
    lines = []
    for key in sorted({finding.key for finding in findings}):
        detector, declaration = key
        existing = baseline.get(key)
        if existing is not None:
            note = existing.note
        else:
            note = next(_one_line(f.detail, 140) for f in findings
                        if f.key == key)
        lines.append(f"{detector} {declaration}  -- {note}")
    return header + "\n" + "\n".join(lines) + "\n"


def read_roster(path: Path) -> tuple[set[str], list[str]]:
    problems: list[str] = []
    if not path.is_file():
        return set(), problems
    try:
        text = path.read_text(encoding="utf-8")
    except OSError as error:
        return set(), [f"cannot read literature roster {path}: {error}"]
    names = {line.split("--", 1)[0].strip() for line in text.splitlines()}
    return {name for name in names if name and not name.startswith("#")}, problems


LABEL_RE = re.compile(r"\\label\{([^}]+)\}")
SECTION_RE = re.compile(
    r"\\(?:sub)*section\*?\{([^}]+)\}|\\paragraph\*?\{([^}]+)\}")
# Closing one of these ends the scope of its `\label`, so a badge in the free
# prose after a corollary is not misreported as belonging to the corollary.
END_ENV_RE = re.compile(
    r"\\end\{(?:mainthm|theorem|proposition|lemma|corollary|definition|remark"
    r"|example|conjecture|question)\}")


def references(tex: str) -> list[tuple[str, str, str]]:
    """`(anchor, module, declaration)` for every `\\leanverified` badge.

    The anchor, not the line number, is the citable location: this manuscript
    is edited concurrently and line numbers drift between runs of this script.
    The nearest preceding `\\label` is used when there is one, the nearest
    sectioning command otherwise, and the line number only as a last resort.
    """
    lines = tex.split("\n")
    found: list[tuple[str, str, str]] = []
    label: str | None = None
    heading: str | None = None
    for number, line in enumerate(lines, start=1):
        match = LABEL_RE.search(line)
        if match:
            label = match.group(1)
        match = SECTION_RE.search(line)
        if match:
            heading = match.group(1) or match.group(2)
            label = None  # a new section invalidates the previous label
        for module, declaration in LEAN_REF.findall(line):
            # A badge on the `\end` line itself still belongs to the
            # environment; only later lines fall back to the heading.
            if label:
                anchor = f"\\label{{{label}}}"
            elif heading:
                anchor = f'section "{heading}"'
            else:
                anchor = f"line {number}"
            found.append((f"{anchor} (line {number} at scan time)",
                          module, declaration))
        if END_ENV_RE.search(line):
            label = None
    return found


def classify(
    corpus: Corpus, declaration: Declaration, roster: set[str],
    full_name: str = "", known: dict[str, str] | None = None,
) -> list[tuple[str, str]]:
    """`(detector, detail)` for each way `declaration` is conditional."""
    known = KNOWN_CONDITIONAL_DECLARATIONS if known is None else known
    findings: list[tuple[str, str]] = []

    if full_name in known:
        findings.append(("known-conditional", known[full_name]))

    # A cited declaration can be conditional by BEING an undischarged datum,
    # not only by taking one as a premise.  `classify` reads premises, and a
    # `structure` has none, so a row naming `HullQuotientNG` as its carrier was
    # invisible: the row says the sentence is proved, and names an object whose
    # only inhabitant rests on a `sorry`.  Reported with the same two-status
    # split as a premise, since the distinction is the same one.
    #
    # Whether this is an overreach depends on what the citing row CLAIMS, which
    # `classify` cannot see: a row that merely fixes notation is right to name
    # an uninhabited datum, because naming the object is its whole claim.  So
    # the finding is emitted here and filtered by row status in
    # `sentence_census.verify_unconditional`.
    datum = declaration.keyword in ("structure", "class", "inductive")
    notion = (declaration.keyword in ("def", "abbrev")
              and declaration.conclusion_head in ("Prop", "Type", "Sort", "Type*"))
    if datum or notion:
        head = corpus.resolve(declaration.short_name)
        if corpus.is_corpus_name(head) and head not in corpus.discharged_honestly:
            if head in corpus.discharged:
                findings.append((
                    "carrier-debt",
                    f"`{declaration.short_name}` is a cited {declaration.keyword} "
                    "that the corpus produces only through declarations resting "
                    "on `sorry`, so a row claiming the sentence is proved by it "
                    "claims more than the kernel holds",
                ))
            else:
                findings.append((
                    "carrier-data",
                    f"`{declaration.short_name}` is a cited {declaration.keyword} "
                    "that nothing in the corpus ever produces, so a row claiming "
                    "the sentence is proved by it claims more than the kernel "
                    "holds",
                ))

    if (declaration.keyword in ("def", "abbrev")
            and declaration.conclusion_head in ("Prop", "Type", "Sort", "Type*")):
        findings.append((
            "definition-only",
            f"`{declaration.short_name}` is a `{declaration.keyword}` producing a "
            f"`{declaration.conclusion_head}`: it introduces a notion and asserts "
            "nothing, so a \\leanverified badge over it certifies no claim",
        ))

    if declaration.header:
        printed = ", ".join(
            f"{' '.join(b.names) or b.type_text}" for b in declaration.header)
        findings.append((
            "header-binder",
            f"the declaration header takes {len(declaration.header)} binder(s) "
            f"({printed}); move every binder after the colon",
        ))

    for binder in declaration.variables:
        findings.append((
            "open-variable",
            f"the statement mentions the in-scope `variable` "
            f"({' '.join(binder.names)} : {_one_line(binder.type_text)}), so the "
            "elaborated type has a leading input the header does not print",
        ))

    conclusion = corpus.unfolded_conclusion(declaration)
    for binder, origin in corpus.unfolded_premises(declaration):
        head = corpus.resolve(binder.head)
        if not head:
            continue
        if head in roster:
            findings.append((
                "literature-input",
                f"{origin}premise `{_one_line(binder.type_text)}` is a "
                "transcription on the literature roster",
            ))
            continue
        if not corpus.is_corpus_name(head):
            continue
        if is_laundered(binder) and head in corpus.discharged:
            # The head is an antecedent's, not the premise's: the caller must
            # supply the whole implication, and reading it as `head` -- which
            # the corpus discharges -- reports a citation as settled.
            findings.append((
                "inlined-statement",
                f"{origin}premise `{_one_line(binder.type_text)}` is a "
                f"statement written inline; its head reads as `{head}`, which "
                "the corpus discharges, but what a caller must supply is the "
                "whole implication, which nothing produces",
            ))
            continue
        if head in corpus.discharged_honestly:
            continue
        # A premise the conclusion is *about* is the theorem's subject matter,
        # not an imported theorem: "if `x` is an asymptotic commutant then so
        # is `uxu*`" says something whether or not commutants exist.  A premise
        # the conclusion never mentions is doing a different job -- it is
        # buying the conclusion with data the corpus cannot supply.
        # `head` is resolved, so the conclusion may spell it either way; the
        # optional prefix keeps the dot-excluding lookbehind from rejecting the
        # qualified spelling it was written to guard against.
        if re.search(rf"(?<![\w'.])(?:[^\W\d][\w'!?]*\.)*{re.escape(head)}(?![\w'])",
                     conclusion):
            continue
        kind = "structure" if head in corpus.corpus_types else "predicate"
        if head in corpus.discharged:
            # Produced, but every producer rests on a `sorry`.  This is worse
            # than an undischarged premise, not better: an undischarged one is
            # visibly a citation, and this one reads as settled.
            findings.append((
                "conditional-debt",
                f"{origin}premise `{_one_line(binder.type_text)}` requires the "
                f"corpus-defined {kind} `{head}`, which the corpus produces only "
                "through declarations that rest on `sorry`; the premise reads as "
                "discharged and is not",
            ))
            continue
        findings.append((
            "conditional-data" if head in corpus.corpus_types else "open-predicate",
            f"{origin}premise `{_one_line(binder.type_text)}` requires the "
            f"corpus-defined {kind} `{head}`, which nothing in the corpus ever "
            "produces; the conclusion is available only to a caller who supplies it",
        ))

    findings += buried_findings(corpus, declaration, conclusion)
    return findings


def buried_names(text: str) -> list[str]:
    """Every identifier occurring anywhere in a type, head or not.

    Deduplicated, in order of first appearance, with each dotted name also
    contributing its final component, because the corpus index is keyed on
    short names.
    """
    seen: dict[str, None] = {}
    for match in re.finditer(IDENT, text):
        name = match.group(0)
        seen.setdefault(name, None)
        seen.setdefault(name.rsplit(".", 1)[-1], None)
    return list(seen)


def buried_findings(
    corpus: Corpus, declaration: Declaration, conclusion: str
) -> list[tuple[str, str]]:
    """Undischarged corpus names below the head of a premise.

    `type_head` walks through `¬`, `∀`/`∃` telescopes, parentheses and
    `Nonempty` and then stops at the leading identifier.  That is the right
    place to look for `(_h : Nonempty (DefectRoutingData D))`, and the wrong
    place for

        (ambient : ∀ ω : Ultrafilter ℕ, (ω : Filter ℕ) ≤ Filter.cofinite →
          UltraproductAdjointModel iota s d U ω)

    whose head is `Ultrafilter` -- a harmless quantifier -- while the premise
    actually demands an `UltraproductAdjointModel`, a bundling structure
    nothing in the repository constructs.  A head-position test reads that as
    unconditional; the theorem is vacuous.  Wrapping the real premise in one
    more quantifier is the cheapest possible evasion of a head-position gate,
    so the scan reads the whole type.

    The same two exemptions as the head test apply, and they are what keep the
    cost of scanning everything low: a discharged name is not a finding, and
    neither is a name the conclusion also mentions.
    """
    findings: list[tuple[str, str]] = []
    reported: set[str] = set()
    for binder, origin in corpus.unfolded_premises(declaration):
        head = binder.head
        for name in buried_names(binder.type_text):
            if name == head or name in reported:
                continue
            if not corpus.is_corpus_name(name) or name in corpus.discharged:
                continue
            if re.search(rf"(?<![\w'.]){re.escape(name)}(?![\w'])", conclusion):
                continue
            reported.add(name)
            kind = "structure" if name in corpus.corpus_types else "predicate"
            findings.append((
                "buried-conditional",
                f"{origin}premise `{_one_line(binder.type_text)}` has head "
                f"`{head}`, but buried below it requires the corpus-defined "
                f"{kind} `{name}` (buried:{name}), which nothing in the corpus "
                "ever produces; a head-position test reads this premise as "
                "harmless",
            ))
    return findings


def _one_line(text: str, width: int = 90) -> str:
    collapsed = " ".join(text.split())
    return collapsed if len(collapsed) <= width else collapsed[: width - 1] + "…"


def validate(
    root: Path, tex_path: Path, roster_path: Path,
    known: dict[str, str] | None = None,
) -> tuple[list[Finding], list[str], int]:
    known = KNOWN_CONDITIONAL_DECLARATIONS if known is None else known
    problems: list[str] = []
    roster, roster_problems = read_roster(roster_path)
    problems.extend(roster_problems)

    try:
        tex = tex_path.read_text(encoding="utf-8")
    except OSError as error:
        return [], [f"cannot read {tex_path}: {error}"], 0

    corpus = build_corpus(root)
    findings: list[Finding] = []
    seen: set[str] = set()

    for anchor, module, name in references(tex):
        path = root / "GroupApproximation" / f"{module}.lean"
        if path not in corpus.declarations:
            problems.append(f"{anchor}: missing GroupApproximation/{module}.lean")
            continue
        short = name.rsplit(".", 1)[-1]
        declaration = corpus.declarations[path].get(short)
        if declaration is None:
            problems.append(f"{anchor}: declaration {name} not found in {module}")
            continue
        if declaration.keyword not in CITABLE:
            problems.append(
                f"{anchor}: {name} is a `{declaration.keyword}`, which asserts "
                "nothing; a \\leanverified badge must cite a proof"
            )
            continue
        if name in seen:
            continue
        seen.add(name)
        for detector, detail in classify(corpus, declaration, roster, name, known):
            findings.append(Finding(anchor, name, detector, detail))

    for name in sorted(known):
        if name not in seen:
            problems.append(
                f"stale entry in KNOWN_CONDITIONAL_DECLARATIONS: {name} is no "
                "longer cited by a \\leanverified badge; delete the entry"
            )

    return findings, problems, len(seen)


def explain(root: Path, tex_path: Path, roster_path: Path) -> int:
    roster, _ = read_roster(roster_path)
    corpus = build_corpus(root)
    tex = tex_path.read_text(encoding="utf-8")
    seen: set[str] = set()
    for anchor, module, name in references(tex):
        if name in seen:
            continue
        seen.add(name)
        path = root / "GroupApproximation" / f"{module}.lean"
        declaration = corpus.declarations.get(path, {}).get(name.rsplit(".", 1)[-1])
        if declaration is None:
            print(f"{name}\n  MISSING")
            continue
        results = classify(corpus, declaration, roster, name)
        status = "CONDITIONAL" if results else "unconditional"
        print(f"{status:13s} {name}")
        print(f"              {module}.lean:{declaration.line}  --  {anchor}")
        for detector, detail in results:
            print(f"    [{detector}] {detail}")
    print(f"\n{len(seen)} cited declarations")
    return 0


def audit_corpus(root: Path) -> int:
    """List every undischarged corpus name and who assumes it.

    The badge roster is the manuscript's trust surface, but a conditional
    result one import away is still a conditional result the moment a badged
    theorem starts using it.  This is the watchlist.
    """
    corpus = build_corpus(root)
    assumers: dict[str, list[tuple[str, Path, int]]] = {}
    for path, declarations in corpus.declarations.items():
        for declaration in declarations.values():
            if declaration.keyword in ("structure", "class", "inductive"):
                continue
            for binder in declaration.cited_premises:
                # Head *and* buried, for the same reason `classify` looks at
                # both: an assumption one quantifier down is still an
                # assumption, and this listing is what tells the lead which
                # names to watch as new lanes land.
                for name in [binder.head] + buried_names(binder.type_text):
                    if (corpus.is_corpus_name(name)
                            and name not in corpus.discharged
                            and name != declaration.short_name):
                        entry = (declaration.short_name, path, declaration.line)
                        bucket = assumers.setdefault(name, [])
                        if entry not in bucket:
                            bucket.append(entry)
    for head in sorted(assumers, key=lambda h: (-len(assumers[h]), h)):
        kind = "structure" if head in corpus.corpus_types else "predicate"
        print(f"{head}  ({kind}, assumed by {len(assumers[head])} declaration(s))")
        for name, path, line in sorted(assumers[head])[:12]:
            print(f"    {name}  ({path.relative_to(root)}:{line})")
        if len(assumers[head]) > 12:
            print(f"    … {len(assumers[head]) - 12} more")
    print(f"\n{len(assumers)} undischarged corpus names are assumed somewhere")
    return 0


def self_test() -> int:
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        integrity_root = root / "integrity"
        integrity_tree = integrity_root / NON_MF_MANUSCRIPT_ROOT
        integrity_tree.mkdir(parents=True)
        (integrity_tree / "Clean.lean").write_text(
            "/- sorry and axiom in prose are ignored -/\n"
            "theorem clean : True := by trivial\n",
            encoding="utf-8",
        )
        if manuscript_source_integrity_problems(integrity_root):
            print("self-test: clean manuscript source failed integrity scan",
                  file=sys.stderr)
            return 1
        (integrity_tree / "Debt.lean").write_text(
            "theorem debt : True := by sorry\n"
            "axiom assumed : True\n",
            encoding="utf-8",
        )
        integrity_findings = manuscript_source_integrity_problems(integrity_root)
        if len(integrity_findings) != 2:
            print("self-test: manuscript source integrity scan missed a "
                  f"placeholder/axiom: {integrity_findings}", file=sys.stderr)
            return 1
        module = root / "GroupApproximation" / "Fake"
        module.mkdir(parents=True)
        (module / "Inputs.lean").write_text(
            "namespace GroupApproximation\n"
            "structure ReductionData where\n"
            "  transform : Nat\n"
            "structure BuildableData where\n"
            "  value : Nat\n"
            "def buildable : BuildableData := ⟨0⟩\n"
            "def IsNeverProved (n : Nat) : Prop := n = n\n"
            "def IsSometimesProved (n : Nat) : Prop := n = n\n"
            "theorem sometimes : IsSometimesProved 0 := rfl\n"
            # the laundering shape: the premise quantifies over a Type and its
            # head reads as `IsSometimesProved`, which IS discharged, while the
            # caller must supply the whole implication.  `LaunderedTarget` must
            # NOT come out discharged.  The other three are the exemptions:
            # head-is-citation inline, a predicate parameter, and an ordinary
            # arrow premise that quantifies over nothing.
            "def LaunderedTarget : Prop := True\n"
            "theorem launderedTarget_of_inline\n"
            "    (h : ∀ (G : Type) [Group G], IsSometimesProved 0 → Nonempty G) :\n"
            "    LaunderedTarget := trivial\n"
            "def HonestTarget : Prop := True\n"
            "theorem honestTarget_of_inline\n"
            "    (h : ∀ (_G : Type), IsSometimesProved 0) : HonestTarget := trivial\n"
            "def PredicateTarget : Prop := True\n"
            "theorem predicateTarget_of_predicates\n"
            "    (P : (H : Type) → Prop) : PredicateTarget := trivial\n"
            "def PlainTarget : Prop := True\n"
            "theorem plainTarget_of_arrow\n"
            "    (h : IsSometimesProved 0 → Nonempty Nat) :\n"
            "    PlainTarget := trivial\n"
            # a refuted citation: its ONLY inhabitant-shaped declaration proves
            # it false, so nothing produces it and every consumer is citing a
            # statement this corpus has disproved
            "def IsRefuted : Prop := 0 = 1\n"
            "theorem not_isRefuted : ¬ IsRefuted := by decide\n"
            # negative control: refuting one instance must not take away the
            # discharge `sometimes` gives the name
            "theorem not_sometimes_at_three : ¬ IsSometimesProved 3 := by decide\n"
            # produced, but only by a declaration that rests on a `sorry`
            "structure DebtData where\n"
            "  mark : Nat\n"
            "def debtData : DebtData := sorry\n"
            # the binder-projection regression: `debtWitness` is a tainted
            # top-level name AND a field of `Package`, and `cleanFromPackage`
            # only ever writes the field.  Reading `p.debtWitness` as a
            # reference would taint it and make `CleanData` a false debt.
            "theorem debtWitness : IsSometimesProved 2 := by sorry\n"
            "structure Package where\n"
            "  debtWitness : Nat\n"
            "def package : Package := ⟨0⟩\n"
            "structure CleanData where\n"
            "  seed : Nat\n"
            "def cleanFromPackage (p : Package) : CleanData := ⟨p.debtWitness⟩\n"
            "end GroupApproximation\n",
            encoding="utf-8",
        )
        (module / "Claims.lean").write_text(
            "import GroupApproximation.Fake.Inputs\n"
            "namespace GroupApproximation\n"
            "section\n"
            "variable (G : Type) [Group G]\n"
            "theorem uses_variable : G = G := rfl\n"
            "end\n"
            "theorem honest :\n"
            "    ∀ (n : Nat) (_h : IsSometimesProved n), n = n := fun _ _ => rfl\n"
            "theorem via_buildable :\n"
            "    ∀ (_d : BuildableData), True := fun _ => trivial\n"
            "theorem closed_but_conditional :\n"
            "    ∀ (_r : ReductionData), True := fun _ => trivial\n"
            "theorem open_predicate :\n"
            "    ∀ (n : Nat), IsNeverProved n → True := fun _ _ => trivial\n"
            "theorem header_binder (n : Nat) : n = n := rfl\n"
            "theorem shadows_variable :\n"
            "    ∀ (G : Type), G = G := fun _ => rfl\n"
            "def IsNotion (n : Nat) : Prop := n = n\n"
            "def HiddenStatement : Prop :=\n"
            "    ∀ (_r : ReductionData), True\n"
            "theorem hides_in_named_prop : HiddenStatement := fun _ => trivial\n"
            "theorem via_debt :\n"
            "    ∀ (_d : DebtData), True := fun _ => trivial\n"
            "theorem via_clean :\n"
            "    ∀ (_c : CleanData), True := fun _ => trivial\n"
            "theorem via_refuted :\n"
            "    ∀ (_h : IsRefuted), True := fun _ => trivial\n"
            "theorem via_sometimes :\n"
            "    ∀ (_h : IsSometimesProved 0), True := fun _ => trivial\n"
            "theorem via_inlined_statement\n"
            "    (h : ∀ (G : Type) [Group G], IsSometimesProved 0 → Nonempty G) :\n"
            "    True := trivial\n"
            # cited AS the datum rather than as a premise: the blind spot a
            # `structure`/`def : Prop` carrier used to fall through.  CarrierOk
            # is honestly produced and must NOT fire.
            "def CarrierNever : Prop := ∀ n : Nat, IsNeverProved n\n"
            "def CarrierDebt : Prop := True\n"
            "theorem carrierDebtProved : CarrierDebt := by sorry\n"
            "def CarrierOk : Prop := True\n"
            "theorem carrierOkProved : CarrierOk := trivial\n"
            # the same blind spot in its `datum` shape --- a cited STRUCTURE
            # nothing produces, which is how `HullQuotientNG` reaches a row.
            # `CarrierStructOk` is produced and must NOT fire.
            "structure CarrierStruct where\n"
            "  seed : Nat\n"
            "structure CarrierStructOk where\n"
            "  seed : Nat\n"
            "def carrierStructOk : CarrierStructOk := ⟨0⟩\n"
            # the refutation of a STRUCTURE, in the shape the corpus uses for
            # `HullInputs`: nothing produces `RefutedData` either
            "structure RefutedData where\n"
            "  seed : Nat\n"
            "theorem not_nonempty_refutedData : ¬ Nonempty RefutedData :=\n"
            "  fun _ => by decide\n"
            "theorem via_refuted_struct :\n"
            "    ∀ (_d : RefutedData), True := fun _ => trivial\n"
            # planted positive: the real premise is one quantifier below the head
            "theorem buries_premise :\n"
            "    ∀ (_a : ∀ k : Nat, 0 < k → ReductionData), True :=\n"
            "  fun _ => trivial\n"
            # planted negative: same buried shape, but the buried name is
            # discharged, so scanning the whole type must NOT report it
            "theorem buries_discharged :\n"
            "    ∀ (_a : ∀ k : Nat, 0 < k → BuildableData), True :=\n"
            "  fun _ => trivial\n"
            # planted negative: buried name the conclusion is also about
            "theorem buries_subject_matter :\n"
            "    ∀ (_a : ∀ k : Nat, IsNeverProved k), IsNeverProved 0 :=\n"
            "  fun h => h 0\n"
            "end GroupApproximation\n",
            encoding="utf-8",
        )
        roster = root / "roster.txt"
        roster.write_text("# empty\n", encoding="utf-8")
        tex = root / "paper.tex"

        def badge(name: str) -> str:
            return (r"\leanverified{Fake/Claims}{GroupApproximation." + name + "}\n")

        cited = ("honest", "via_buildable", "closed_but_conditional",
                 "open_predicate", "header_binder", "uses_variable",
                 "shadows_variable", "IsNotion", "hides_in_named_prop",
                 "via_debt", "via_clean", "via_refuted", "via_sometimes",
                 "via_inlined_statement",
                 "CarrierNever", "CarrierDebt", "CarrierOk",
)
        tex.write_text("".join(badge(name) for name in cited), encoding="utf-8")
        known = {"GroupApproximation.honest": "pinned by hand"}
        findings, problems, checked = validate(root, tex, roster, known)
        if problems or checked != len(cited):
            print(f"self-test: unexpected setup failure: {problems}", file=sys.stderr)
            return 1
        by_declaration: dict[str, set[str]] = {}
        for finding in findings:
            by_declaration.setdefault(finding.declaration, set()).add(finding.detector)

        for clean in ("GroupApproximation.via_buildable",
                      "GroupApproximation.shadows_variable",
                      "GroupApproximation.via_clean",
                      "GroupApproximation.via_sometimes"):
            if clean in by_declaration:
                print(f"self-test: false positive on {clean}: "
                      f"{by_declaration[clean]}", file=sys.stderr)
                return 1

        expected = {
            "GroupApproximation.closed_but_conditional": "conditional-data",
            "GroupApproximation.open_predicate": "open-predicate",
            "GroupApproximation.header_binder": "header-binder",
            "GroupApproximation.uses_variable": "open-variable",
            "GroupApproximation.honest": "known-conditional",
            "GroupApproximation.IsNotion": "definition-only",
            "GroupApproximation.hides_in_named_prop": "conditional-data",
            "GroupApproximation.via_debt": "conditional-debt",
            # a premise whose only inhabitant-shaped declaration REFUTES it
            # reads as a never-proved predicate, which is what it is
            "GroupApproximation.via_refuted": "open-predicate",
            "GroupApproximation.via_inlined_statement": "inlined-statement",
            "GroupApproximation.CarrierNever": "carrier-data",
            "GroupApproximation.CarrierDebt": "carrier-debt",
        }
        for carrier_clean in ("GroupApproximation.CarrierOk",):
            got = by_declaration.get(carrier_clean, set())
            if got & {"carrier-data", "carrier-debt"}:
                print(f"self-test: false carrier finding on {carrier_clean}: "
                      f"{got}", file=sys.stderr)
                return 1

        for name, detector in expected.items():
            if detector not in by_declaration.get(name, set()):
                print(f"self-test: missed {detector} on {name}; got "
                      f"{by_declaration.get(name, set())}", file=sys.stderr)
                return 1

        # The `datum` half of the carrier rule cannot be reached through a
        # badge -- a `\leanverified` badge may not cite a `structure` at all,
        # and the setup check above says so -- but a census ROW can cite one,
        # which is how `HullQuotientNG` reaches the manuscript.  So it is
        # pinned directly, both directions.
        corpus = build_corpus(root)
        carrier_struct = {detector for detector, _detail in classify(
            corpus, corpus.by_name["CarrierStruct"], set(),
            "GroupApproximation.CarrierStruct")}
        if "carrier-data" not in carrier_struct:
            print("self-test: missed carrier-data on the cited structure "
                  f"CarrierStruct; got {carrier_struct}", file=sys.stderr)
            return 1
        carrier_struct_ok = {detector for detector, _detail in classify(
            corpus, corpus.by_name["CarrierStructOk"], set(),
            "GroupApproximation.CarrierStructOk")}
        if carrier_struct_ok & {"carrier-data", "carrier-debt"}:
            print("self-test: false carrier finding on the produced structure "
                  f"CarrierStructOk; got {carrier_struct_ok}", file=sys.stderr)
            return 1

        # A theorem that REDUCES its conclusion to a statement written inside a
        # binder discharges nothing; the three exemptions beside it keep the
        # rule from swallowing ordinary hypotheses.  Without this,
        # `HullRelatorStatement₂OfBaseLetter` reads as available while its
        # literature input sits unproved in a binder.
        for name, want in (("LaunderedTarget", False), ("HonestTarget", True),
                           ("PredicateTarget", True), ("PlainTarget", True)):
            if (name in corpus.discharged) is not want:
                print(f"self-test: {name} discharged="
                      f"{name in corpus.discharged}, expected {want}",
                      file=sys.stderr)
                return 1

        # A refutation must not read as a producer even when the refuted name
        # is a `structure`: `¬ Nonempty HullInputs` is how that arrives.
        refuted_struct = {detector for detector, _detail in classify(
            corpus, corpus.by_name["via_refuted_struct"], set(),
            "GroupApproximation.via_refuted_struct")}
        if "conditional-data" not in refuted_struct:
            print("self-test: a refuted structure read as discharged; "
                  f"got {refuted_struct}", file=sys.stderr)
            return 1

        # A pinned name that is no longer cited must be reported, so the roster
        # cannot outlive the problem it records.
        _findings, problems, _checked = validate(
            root, tex, roster, {"GroupApproximation.gone": "pinned by hand"})
        if not any("stale entry" in problem for problem in problems):
            print("self-test: stale roster entry was not reported", file=sys.stderr)
            return 1

        # The roster must be able to condemn a name the structural rule clears.
        roster.write_text("IsSometimesProved\n", encoding="utf-8")
        findings, _problems, _checked = validate(root, tex, roster, {})
        if not any(finding.detector == "literature-input" for finding in findings):
            print("self-test: literature roster did not fire", file=sys.stderr)
            return 1

        # A badge citing a `structure` proves nothing and must be rejected.
        tex.write_text(
            r"\leanverified{Fake/Inputs}{GroupApproximation.ReductionData}",
            encoding="utf-8")
        _findings, problems, _checked = validate(root, tex, roster, {})
        if not any("asserts nothing" in problem for problem in problems):
            print("self-test: badge on a structure was accepted", file=sys.stderr)
            return 1

        # Transitive discharge: a producer that itself needs an open package
        # must not discharge its result.
        (module / "Inputs.lean").write_text(
            (module / "Inputs.lean").read_text(encoding="utf-8").replace(
                "def buildable : BuildableData := ⟨0⟩",
                "def buildable (_r : ReductionData) : BuildableData := ⟨0⟩"),
            encoding="utf-8")
        tex.write_text(badge("via_buildable"), encoding="utf-8")
        findings, _problems, _checked = validate(root, tex, roster, {})
        if not any(finding.detector == "conditional-data" for finding in findings):
            print("self-test: transitive discharge closure is too generous",
                  file=sys.stderr)
            return 1

        # The baseline has three behaviours, and each of them is a separate way
        # for an armed gate to go quiet.  Plant one of each: a finding the
        # register accepts, a finding nobody accepted, and an exemption whose
        # defect is gone.
        register = root / "baseline.txt"
        register.write_text(
            "# planted by the self-test\n"
            "conditional-data GroupApproximation.via_buildable  -- planted\n",
            encoding="utf-8")
        entries, entry_problems = read_baseline(register)
        if entry_problems or len(entries) != 1:
            print(f"self-test: baseline parse failed: {entry_problems}",
                  file=sys.stderr)
            return 1
        accepted, new, stale = apply_baseline(findings, entries)
        if not accepted or new or stale:
            print("self-test: a listed finding was not accepted", file=sys.stderr)
            return 1
        unlisted = Finding("anchor", "GroupApproximation.elsewhere",
                           "open-variable", "planted")
        _accepted, new, _stale = apply_baseline(findings + [unlisted], entries)
        if [finding.declaration for finding in new] != [unlisted.declaration]:
            print("self-test: the baseline swallowed an unlisted finding",
                  file=sys.stderr)
            return 1
        # Same declaration, different detector: a new *shape* of defect on an
        # accepted declaration is a new finding, not a covered one.
        reshaped = Finding("anchor", "GroupApproximation.via_buildable",
                           "open-variable", "planted")
        _accepted, new, _stale = apply_baseline(findings + [reshaped], entries)
        if not new:
            print("self-test: a new detector on a listed declaration was "
                  "accepted", file=sys.stderr)
            return 1
        _accepted, _new, stale = apply_baseline([], entries)
        if not stale:
            print("self-test: a stale baseline entry was not reported",
                  file=sys.stderr)
            return 1

        rendered = root / "rendered.txt"
        rendered.write_text(render_baseline(findings, entries), encoding="utf-8")
        again, render_problems = read_baseline(rendered)
        if render_problems or set(again) != {finding.key for finding in findings}:
            print(f"self-test: rendered baseline does not round-trip: "
                  f"{render_problems}", file=sys.stderr)
            return 1
        if again[("conditional-data", "GroupApproximation.via_buildable")
                 ].note != "planted":
            print("self-test: rewriting the baseline dropped a justification",
                  file=sys.stderr)
            return 1

        register.write_text(
            "conditional-data GroupApproximation.via_buildable\n"
            "not-a-detector GroupApproximation.via_buildable  -- typo\n"
            "conditional-data GroupApproximation.via_buildable  -- once\n"
            "conditional-data GroupApproximation.via_buildable  -- twice\n",
            encoding="utf-8")
        _entries, entry_problems = read_baseline(register)
        for expected in ("malformed entry", "unknown detector", "duplicate entry"):
            if not any(expected in problem for problem in entry_problems):
                print(f"self-test: baseline did not report a {expected}",
                      file=sys.stderr)
                return 1

    print("check-non-mf-unconditional: self-test passed")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=REPO)
    parser.add_argument("--tex", type=Path, default=DEFAULT_TEX)
    parser.add_argument(
        "--literature-roster", type=Path, default=DEFAULT_ROSTER,
        help=("names that are transcriptions of unproved literature theorems; "
              "the Python mirror of `Audit.literatureInputNames`"),
    )
    parser.add_argument(
        "--explain", action="store_true",
        help="print the classification of every cited declaration and exit 0",
    )
    parser.add_argument(
        "--audit-corpus", action="store_true",
        help=("list every undischarged corpus name and the declarations that "
              "assume it, badged or not, and exit 0"),
    )
    parser.add_argument(
        "--baseline", type=Path, default=DEFAULT_BASELINE,
        help=("the register of known, written-up findings; anything not on it "
              "fails, and an entry that matches nothing fails too"),
    )
    parser.add_argument(
        "--write-baseline", action="store_true",
        help=("rewrite the baseline from this run, keeping the existing "
              "justification of every entry that survives"),
    )
    parser.add_argument(
        "--strict", action="store_true",
        help="ignore the baseline entirely; the end state, once it is empty",
    )
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()

    if args.self_test:
        return self_test()

    root = args.root if args.root.is_absolute() else REPO / args.root
    tex = args.tex if args.tex.is_absolute() else root / args.tex
    roster = (args.literature_roster if args.literature_roster.is_absolute()
              else root / args.literature_roster)
    baseline_path = (args.baseline if args.baseline.is_absolute()
                     else root / args.baseline)

    if args.audit_corpus:
        return audit_corpus(root)

    if args.explain:
        return explain(root, tex, roster)

    findings, problems, checked = validate(root, tex, roster)
    baseline, baseline_problems = read_baseline(baseline_path)

    if args.write_baseline:
        baseline_path.parent.mkdir(parents=True, exist_ok=True)
        baseline_path.write_text(render_baseline(findings, baseline),
                                 encoding="utf-8")
        accepted_keys = {finding.key for finding in findings}
        print(f"wrote {baseline_path} ({len(accepted_keys)} accepted "
              f"finding(s) over {len(findings)} report(s))")
        return 0

    if args.strict:
        baseline = {}
        problems.extend(manuscript_source_integrity_problems(root))
    else:
        problems.extend(baseline_problems)
    accepted, new, stale = apply_baseline(findings, baseline)
    for entry in stale:
        problems.append(
            f"stale baseline entry {baseline_path.name}:{entry.line}: "
            f"[{entry.detector}] {entry.declaration} is no longer reported; "
            "delete the line"
        )

    if new or problems:
        total = len(new) + len(problems)
        print(f"check-non-mf-unconditional: {total} problem(s):", file=sys.stderr)
        for problem in problems:
            print(f"  {problem}", file=sys.stderr)
        for finding in sorted(new, key=lambda f: (f.declaration, f.detector)):
            print(f"  {finding.anchor}: [{finding.detector}] "
                  f"{finding.declaration}: {finding.detail}", file=sys.stderr)
        counts: dict[str, int] = {}
        for finding in new:
            counts[finding.detector] = counts.get(finding.detector, 0) + 1
        if counts:
            summary = ", ".join(f"{counts[k]} {k}" for k in sorted(counts))
            print(f"  ({summary}; see notes/NON_MF_CONDITIONAL_INVENTORY.md. "
                  "A finding that is genuinely known and written up belongs on "
                  f"{baseline_path.name}, with its justification.)",
                  file=sys.stderr)
        return 1

    if accepted:
        print(f"check-non-mf-unconditional: {checked} cited declarations, no "
              f"new findings; {len(accepted)} report(s) over "
              f"{len({f.key for f in accepted})} entries accepted by "
              f"{baseline_path.name}")
        for finding in sorted(accepted, key=lambda f: (f.declaration, f.detector)):
            print(f"  known [{finding.detector}] {finding.declaration}")
        return 0

    print(f"check-non-mf-unconditional: {checked} cited declarations are "
          "unconditional")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
