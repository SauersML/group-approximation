#!/usr/bin/env python3
r"""Walk the transitive proof-dependency closure of every non-MF manuscript badge.

`check_non_mf_refs.py` asks whether the declaration a `\leanverified` badge
names exists.  `check_non_mf_zero_input.py` asks whether its header is closed.
`check_non_mf_unconditional.py` asks whether *its own* premises are dischargeable.
None of the three looks past the badged declaration itself, and the standard the
manuscript is held to reaches further than that:

> It is not enough for a manuscript-facing theorem's top-level proof to resemble
> the TeX.  Every helper it invokes must be checked against the corresponding
> TeX step.  If a helper contains a mathematically different proof of something
> whose proof is specified in the manuscript, that helper must be replaced on
> the manuscript path.

A badged theorem can therefore have a perfectly faithful three-line top-level
proof and still be a MISMATCH, because four levels down it discharges a
manuscript-specified step by a route the manuscript does not take.  This script
produces the object those judgements need: for each badge, the set of
repository declarations its proof transitively depends on, with the edges that
connect them.

## What this is, and what it is not

This is a **source-level** analyser.  It never invokes `lake`, `lean`, or
`#print axioms`; it parses `.lean` text, tracks the `namespace`/`section`/`open`
stack, resolves `import` graphs, and extracts the identifiers each declaration
mentions.  A real dependency trace would come from the elaborated environment,
and would be exact.  This one is approximate, and it is deliberately tuned to
**OVER-report rather than miss**:

* every scope prefix that could resolve a token contributes an edge, not just
  the one Lean would pick;
* a token that resolves nowhere in scope falls back to a suffix match on its
  last component (this is how dot-notation such as `hσ.toSofic` and names
  reached through an `export` are recovered), reported at lower confidence;
* the statement of a declaration is scanned as well as its proof, so the
  objects a claim is *about* appear in the closure alongside the lemmas that
  prove it;
* a token whose only matches lie outside the module's import closure is kept
  anyway rather than discarded as impossible.

The cost is false edges.  A local hypothesis named like a repository lemma, a
`simp` set member, or a projection that happens to share a short name will all
show up.  Over-reporting is the right failure mode here: a spurious helper in
the trace costs a reviewer one glance, while a missing one defeats the point of
the trace.  Mathlib and core names are absent from the index by construction and
so never appear -- Mathlib is the permitted base, not a dependency to audit.

## Flags

Four properties are computed for each node of a closure, matching the four
questions the manuscript audit asks of a helper:

`conditional`
    the helper's premises include a corpus-defined package the corpus never
    discharges.  Computed by delegating to `check_non_mf_unconditional`, so the
    two agree by construction; that gate applies the test to badged
    declarations only, and this script applies it to everything they reach.
`literature`
    the helper's short name is on the literature roster
    (`metadata/NON_MF_LITERATURE_INPUTS.txt`, the mirror of
    `Audit.literatureInputNames`).
`abstraction`
    the helper's name matches one of `--abstraction`'s patterns.  These name
    the general-purpose residual/radical layers -- `normMFResidual`,
    `weakMF`, and friends -- whose appearance on a manuscript path is the
    signal that a printed concrete argument has been replaced by a detour
    through an abstraction the manuscript does not use.
`badged`
    the helper is itself cited by a badge, so the manuscript specifies a proof
    for it and that proof has its own correspondence obligation.

## Usage

    scripts/trace_manuscript_deps.py                    # tree per badge
    scripts/trace_manuscript_deps.py --flagged-only     # just the findings
    scripts/trace_manuscript_deps.py --summary          # one line per badge
    scripts/trace_manuscript_deps.py --decl NAME        # one badge, in full
    scripts/trace_manuscript_deps.py --format json      # nodes and edges
    scripts/trace_manuscript_deps.py --format dot       # graphviz
    scripts/trace_manuscript_deps.py --shared 4         # helpers on >= 4 paths
    scripts/trace_manuscript_deps.py --check            # gate: flags are errors
    scripts/trace_manuscript_deps.py --self-test

Reporting modes exit 0.  `--check` exits 1 when any badge closure contains a
conditional or literature-tagged helper, in the format the other
`check_non_mf_*.py` gates use.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
import tempfile
from collections import defaultdict, deque
from dataclasses import dataclass, field
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from lean_decls import MODIFIERS, _strip_block_comments
from check_non_mf_unconditional import (
    IDENT,
    Corpus,
    _find_top_level,
    build_corpus,
    read_roster,
)

REPO = Path(__file__).resolve().parent.parent
DEFAULT_TEX = REPO / "non_mf_groups_exist.tex"
DEFAULT_ROSTER = REPO / "metadata" / "NON_MF_LITERATURE_INPUTS.txt"

LEAN_REF = re.compile(r"\\leanverified\{([^}]+)\}\{([^}]+)\}")

DECL_KEYWORDS = (
    "theorem", "lemma", "def", "abbrev", "structure", "inductive", "class",
    "instance", "opaque", "axiom", "example",
)

# A column-zero line that ends the previous declaration's block.  `where`,
# `termination_by`, `decreasing_by` and the `|` of an inductive alternative are
# deliberately absent: they continue the declaration they follow.
BOUNDARY_WORDS = DECL_KEYWORDS + (
    "private", "protected", "noncomputable", "partial", "unsafe", "scoped",
    "local", "namespace", "section", "end", "open", "export", "variable",
    "universe", "import", "attribute", "set_option", "notation", "macro",
    "macro_rules", "syntax", "initialize", "mutual",
)
BOUNDARY_RE = re.compile(
    r"^(?:@\[|#|(?:" + "|".join(BOUNDARY_WORDS) + r")\b)")

DECL_RE = re.compile(
    rf"^{MODIFIERS}(?P<kw>{'|'.join(DECL_KEYWORDS)})\s+(?P<name>{IDENT})")
NAMESPACE_RE = re.compile(rf"^namespace\s+(?P<name>{IDENT})")
SECTION_RE = re.compile(rf"^(?:noncomputable\s+)?section(?:\s+(?P<name>{IDENT}))?\s*$")
END_RE = re.compile(rf"^end(?:\s+(?P<name>{IDENT}))?\s*$")
IMPORT_RE = re.compile(rf"^import\s+(?P<name>{IDENT})")
OPEN_RE = re.compile(r"^(?:open|export)\s+(?P<rest>.*)$")
TOKEN_RE = re.compile(IDENT)

# Vocabulary that exists only in Lean.  A manuscript step the paper proves by an
# explicit corona-image computation, discharged in Lean by a lemma whose name is
# in this vocabulary, is the (c) finding this trace exists to surface --
# `normalKazhdan_le_normMFResidual` is the known instance.
#
# The list is deliberately narrow.  `IsOperatorMF` is the manuscript's own
# definition of MF; `actualCoronaMFResidual`, `manuscriptCoronaMFResidual`,
# `cdeMFResidual`, `coronaMFResidual` and `fdUnitaryResidual` are presentations
# of its `Rad_MF` and `Rad_fd`.  Those are not abstractions standing in for a
# printed argument, they *are* the printed objects, and flagging them would bury
# the real findings.  What is left is the universal-ultraproduct layer: the
# `WeakMF` family and the `normMFResidual` built on it.  The manuscript does say
# "weakly MF" and "the norm-MF radical" once, in the appendix proof of
# `prop:mf-equivalences`, but it identifies that radical with `def:radical` --
# a single sequential cofinite corona -- whereas the Lean `normMFResidual`
# quantifies over every index type and every ultrafilter, and its own docstring
# records that it "is not a definitional identification with the paper's
# cofinite-corona radical".  It is a different object with a comparison theorem
# attached, which is exactly what (c) asks to be surfaced.
DEFAULT_ABSTRACTIONS = (
    "normMFResidual",
    "NormMFInvisible",
    "WeakMF",
    "weakMF",
)

# Identifiers that are tactics, keywords, or structure fields rather than
# references.  Only names that also exist in the corpus index would survive the
# resolution step anyway; this list keeps the obvious collisions out.
STOPWORDS = frozenset("""
by exact apply intro intros refine have show let fun if then else match with do
calc this at using from obtain rcases rintro cases constructor use ext and or
not true false rfl trivial id congr subst omega ring linarith nlinarith
positivity gcongr norm_num push_cast field_simp aesop simp simpa rw rwa
exact_mod_cast assumption contradiction specialize induction set clear change
convert all_goals any_goals first try repeat skip done swap left right exists
forall in where deriving protected private noncomputable instance theorem lemma
def abbrev open namespace end section variable universe import return fin cases'
push_neg by_cases by_contra nlinarith interval_cases decide norm_cast
""".split())


# ---------------------------------------------------------------------------
# Source scan
# ---------------------------------------------------------------------------


def _blank_strings(text: str) -> str:
    """Blank the contents of string literals, keeping length and line structure."""
    out: list[str] = []
    inside = False
    index = 0
    while index < len(text):
        char = text[index]
        if inside:
            if char == "\\" and index + 1 < len(text):
                out.append("  ")
                index += 2
                continue
            if char == '"':
                inside = False
                out.append('"')
            else:
                out.append("\n" if char == "\n" else " ")
            index += 1
            continue
        if char == '"':
            inside = True
        out.append(char)
        index += 1
    return "".join(out)


def clean_source(text: str) -> str:
    """Comment-free, string-free source with line numbers preserved."""
    stripped = _blank_strings(_strip_block_comments(text))
    return "\n".join(line.split("--", 1)[0] for line in stripped.splitlines())


@dataclass
class LeanDecl:
    """One column-zero declaration, with everything needed to resolve its body."""

    full_name: str
    short_name: str
    keyword: str
    module: str
    path: Path
    line: int
    scope_prefixes: tuple[str, ...]
    statement: str
    value: str

    @property
    def body(self) -> str:
        return self.statement + "\n" + self.value


@dataclass
class LeanModule:
    name: str
    path: Path
    imports: tuple[str, ...]
    decls: list[LeanDecl] = field(default_factory=list)


def _open_names(rest: str) -> list[str]:
    """Namespace names an `open`/`export` line brings into scope.

    `open scoped A B`, `open A (x y)`, and `open A in` all contribute `A`; the
    selective and `scoped` forms are treated as full opens, which can only add
    resolution candidates.
    """
    rest = re.sub(r"\([^)]*\)", " ", rest)
    names: list[str] = []
    for word in rest.replace(" in", " ").split():
        if word in ("scoped", "in", "renaming", "hiding"):
            continue
        if re.fullmatch(IDENT, word):
            names.append(word)
    return names


def scan_module(path: Path, module: str) -> LeanModule:
    """Every column-zero declaration in `path`, with its scope and body text."""
    source = clean_source(path.read_text(encoding="utf-8"))
    lines = source.splitlines()

    imports: list[str] = []
    # Each scope level carries a namespace component (or None) and its opens.
    stack: list[tuple[str | None, list[str]]] = []
    file_opens: list[str] = []
    decls: list[LeanDecl] = []

    # Pass one: the column-zero command lines, so a declaration's block can be
    # cut at the next one.
    starts: list[int] = [
        number for number, line in enumerate(lines)
        if line and not line[0].isspace() and BOUNDARY_RE.match(line)
    ]
    boundary_after = {}
    for position, number in enumerate(starts):
        boundary_after[number] = (starts[position + 1] if position + 1 < len(starts)
                                  else len(lines))

    for number, line in enumerate(lines):
        if not line or line[0].isspace():
            continue
        if match := IMPORT_RE.match(line):
            imports.append(match.group("name"))
            continue
        if match := NAMESPACE_RE.match(line):
            stack.append((match.group("name"), []))
            continue
        if SECTION_RE.match(line):
            stack.append((None, []))
            continue
        if END_RE.match(line):
            if stack:
                stack.pop()
            continue
        if match := OPEN_RE.match(line):
            names = _open_names(match.group("rest"))
            if stack:
                stack[-1][1].extend(names)
            else:
                file_opens.extend(names)
            continue
        match = DECL_RE.match(line)
        if match is None:
            continue

        namespace = ".".join(part for part, _ in stack if part)
        name = match.group("name")
        full = f"{namespace}.{name}" if namespace else name

        block = "\n".join(lines[number:boundary_after.get(number, len(lines))])
        after_name = block.find(name, len(match.group(0)) - len(name)) + len(name)
        cut, token = _find_top_level(block, (":=", " where\n", " where "), after_name)
        statement = block if cut == -1 else block[:cut]
        value = block[cut + len(token):] if cut != -1 and token == ":=" else ""

        # Resolution scopes, most specific first: every prefix of the enclosing
        # namespace, then every namespace opened at any enclosing level, then
        # the root.
        components = [part for part, _ in stack if part]
        prefixes: list[str] = []
        for depth in range(len(components), 0, -1):
            prefixes.append(".".join(components[:depth]))
        for _part, opens in reversed(stack):
            prefixes.extend(opens)
        prefixes.extend(file_opens)
        prefixes.append("")

        decls.append(LeanDecl(
            full_name=full,
            short_name=name.rsplit(".", 1)[-1],
            keyword=match.group("kw"),
            module=module,
            path=path,
            line=number + 1,
            scope_prefixes=tuple(dict.fromkeys(prefixes)),
            statement=statement,
            value=value,
        ))

    return LeanModule(module, path, tuple(imports), decls)


# ---------------------------------------------------------------------------
# Development index
# ---------------------------------------------------------------------------


@dataclass
class Development:
    modules: dict[str, LeanModule]
    by_full_name: dict[str, LeanDecl]
    by_short_name: dict[str, list[LeanDecl]]
    _closure: dict[str, frozenset[str]] = field(default_factory=dict)

    def import_closure(self, module: str) -> frozenset[str]:
        """Every repository module reachable from `module` through imports."""
        if module in self._closure:
            return self._closure[module]
        seen: set[str] = set()
        pending = [module]
        while pending:
            current = pending.pop()
            if current in seen or current not in self.modules:
                continue
            seen.add(current)
            pending.extend(self.modules[current].imports)
        frozen = frozenset(seen)
        self._closure[module] = frozen
        return frozen


def build_development(root: Path) -> Development:
    """Index every `.lean` file under `root/GroupApproximation`, plus the root file."""
    modules: dict[str, LeanModule] = {}
    base = root / "GroupApproximation"
    paths = sorted(base.rglob("*.lean")) if base.is_dir() else []
    for path in paths:
        name = "GroupApproximation." + ".".join(
            path.relative_to(base).with_suffix("").parts)
        modules[name] = scan_module(path, name)

    by_full_name: dict[str, LeanDecl] = {}
    by_short_name: dict[str, list[LeanDecl]] = defaultdict(list)
    for module in modules.values():
        for decl in module.decls:
            by_full_name.setdefault(decl.full_name, decl)
            by_short_name[decl.short_name].append(decl)
    return Development(modules, by_full_name, dict(by_short_name))


# ---------------------------------------------------------------------------
# Reference resolution
# ---------------------------------------------------------------------------

SUFFIX_FALLBACK_LIMIT = 6


def tokens(text: str) -> list[str]:
    return [token for token in TOKEN_RE.findall(text)
            if token not in STOPWORDS and len(token) > 1]


@dataclass(frozen=True)
class Edge:
    source: str
    target: str
    site: str          # "statement" or "proof"
    confidence: str    # "scoped" or "heuristic"


def resolve_token(
    token: str, decl: LeanDecl, dev: Development, *, suffix_fallback: bool = True
) -> list[tuple[str, str]]:
    """Every corpus declaration `token` could name inside `decl`, with confidence.

    Over-reports by design: all scope prefixes that produce a hit contribute,
    not only the one Lean's resolution order would select.
    """
    reachable = dev.import_closure(decl.module)
    scoped: list[str] = []
    for prefix in decl.scope_prefixes:
        candidate = f"{prefix}.{token}" if prefix else token
        target = dev.by_full_name.get(candidate)
        if target is not None and target.full_name != decl.full_name:
            scoped.append(target.full_name)
    if scoped:
        inside = [name for name in scoped
                  if dev.by_full_name[name].module in reachable]
        chosen = inside or scoped
        return [(name, "scoped") for name in dict.fromkeys(chosen)]

    if not suffix_fallback:
        return []
    # Nothing resolved in scope.  The identifier may still be a reference: dot
    # notation (`hσ.toSofic`), a name reached through `export`, or an `open`
    # form this scanner did not parse.  Match the final component against the
    # index, restricted to modules this one can actually see.
    short = token.rsplit(".", 1)[-1]
    if short in STOPWORDS or len(short) <= 3:
        return []
    matches = [other.full_name for other in dev.by_short_name.get(short, [])
               if other.module in reachable and other.full_name != decl.full_name]
    if not matches or len(matches) > SUFFIX_FALLBACK_LIMIT:
        return []
    return [(name, "heuristic") for name in dict.fromkeys(matches)]


def references(
    decl: LeanDecl, dev: Development, *, suffix_fallback: bool = True
) -> list[Edge]:
    """Every edge out of `decl`, tagged by whether it sits in the type or the proof."""
    edges: dict[Edge, None] = {}
    for site, text in (("statement", decl.statement), ("proof", decl.value)):
        if not text:
            continue
        for token in dict.fromkeys(tokens(text)):
            if token == decl.short_name or token == decl.full_name:
                continue
            for target, confidence in resolve_token(
                    token, decl, dev, suffix_fallback=suffix_fallback):
                edges[Edge(decl.full_name, target, site, confidence)] = None
    return list(edges)


# ---------------------------------------------------------------------------
# Flags
# ---------------------------------------------------------------------------


@dataclass
class Flags:
    conditional: tuple[str, ...] = ()
    buried: tuple[str, ...] = ()
    literature: tuple[str, ...] = ()
    abstraction: tuple[str, ...] = ()
    badged: bool = False

    def __bool__(self) -> bool:
        return bool(self.conditional or self.buried or self.literature
                    or self.abstraction)

    def render(self) -> str:
        parts = []
        if self.conditional:
            parts.append("conditional:" + ",".join(self.conditional))
        if self.buried:
            parts.append("buried:" + ",".join(self.buried))
        if self.literature:
            parts.append("literature:" + ",".join(self.literature))
        if self.abstraction:
            parts.append("abstraction:" + ",".join(self.abstraction))
        if self.badged:
            parts.append("badged")
        return " ".join(parts)


def compute_flags(
    decl: LeanDecl,
    corpus: Corpus,
    roster: set[str],
    abstractions: tuple[str, ...],
    badged: frozenset[str],
) -> Flags:
    """Classify one node of a closure against the four audit questions.

    `conditional` is the head-position test, and agrees with
    `check_non_mf_unconditional.py` by construction.  `buried` is strictly more
    sensitive: it reports a corpus-defined, never-discharged package mentioned
    *anywhere* inside a premise type, not only at its head.  That extra
    sensitivity is what catches the bundling-structure class, e.g.

        (ambient : ∀ ω : Ultrafilter ℕ, (ω : Filter ℕ) ≤ Filter.cofinite →
           UltraproductAdjointModel iota s d U ω)

    whose head is `Ultrafilter`, not the unconstructed package.  A premise
    package hidden behind a `∀ … → …` is exactly as unconstructible as one in
    head position, so missing it would defeat the point; the price is that a
    package merely *named* in a premise -- in a hypothesis about one, say --
    is reported too.  Read `buried` as a lead and `conditional` as a verdict.
    """
    conditional: list[str] = []
    buried: list[str] = []

    target = corpus.by_name.get(decl.short_name)
    if target is not None and target.path == decl.path:
        conclusion = corpus.unfolded_conclusion(target)

        def open_package(name: str) -> bool:
            """Undischarged, and not the theorem's own subject matter.

            The second half is `check_non_mf_unconditional.classify`'s
            exemption, reproduced so the two agree: a premise the conclusion is
            *about* -- "if `x` is an asymptotic commutant then so is `uxu*`" --
            says something whether or not commutants exist, while a premise the
            conclusion never mentions is buying the conclusion with data the
            corpus cannot supply.  Without it this flag reports 58 helpers
            across the badge closures where that gate reports 45.
            """
            if not name or not corpus.is_corpus_name(name):
                return False
            if name in corpus.discharged:
                return False
            return not re.search(
                rf"(?<![\w'.]){re.escape(name)}(?![\w'])", conclusion)

        premises = [binder for binder, _via in corpus.unfolded_premises(target)]
        premises += list(target.build_premises)
        for binder in premises:
            if open_package(binder.head):
                conditional.append(binder.head)
            for token in TOKEN_RE.findall(binder.type_text or ""):
                short = token.rsplit(".", 1)[-1]
                if short != binder.head and open_package(short):
                    buried.append(short)
    literature = [name for name in roster
                  if name == decl.short_name or name in decl.statement]
    abstraction = [pattern for pattern in abstractions if pattern in decl.full_name]
    seen_conditional = set(conditional)
    return Flags(
        conditional=tuple(dict.fromkeys(conditional)),
        buried=tuple(name for name in dict.fromkeys(buried)
                     if name not in seen_conditional),
        literature=tuple(dict.fromkeys(literature)),
        abstraction=tuple(abstraction),
        badged=decl.full_name in badged,
    )


# ---------------------------------------------------------------------------
# Closures
# ---------------------------------------------------------------------------


@dataclass
class Closure:
    root: str
    depth_of: dict[str, int]
    edges: list[Edge]
    truncated: bool = False

    @property
    def nodes(self) -> list[str]:
        return sorted(self.depth_of, key=lambda name: (self.depth_of[name], name))

    def children(self, name: str) -> list[Edge]:
        return sorted((edge for edge in self.edges if edge.source == name),
                      key=lambda edge: (edge.site != "statement", edge.target))


def closure_of(
    root_name: str,
    dev: Development,
    *,
    max_depth: int,
    max_nodes: int,
    suffix_fallback: bool = True,
    cache: dict[str, list[Edge]] | None = None,
) -> Closure:
    """Breadth-first transitive closure of the references out of `root_name`."""
    cache = {} if cache is None else cache
    depth_of = {root_name: 0}
    edges: list[Edge] = []
    queue: deque[str] = deque([root_name])
    truncated = False
    while queue:
        current = queue.popleft()
        depth = depth_of[current]
        if depth >= max_depth:
            truncated = True
            continue
        decl = dev.by_full_name.get(current)
        if decl is None:
            continue
        if current not in cache:
            cache[current] = references(decl, dev, suffix_fallback=suffix_fallback)
        for edge in cache[current]:
            edges.append(edge)
            if edge.target not in depth_of:
                if len(depth_of) >= max_nodes:
                    truncated = True
                    continue
                depth_of[edge.target] = depth + 1
                queue.append(edge.target)
    return Closure(root_name, depth_of, edges, truncated)


# ---------------------------------------------------------------------------
# Reporting
# ---------------------------------------------------------------------------


@dataclass
class Badge:
    tex_line: int
    module: str
    declaration: str


def badges(tex: str) -> list[Badge]:
    found: list[Badge] = []
    for number, line in enumerate(tex.splitlines(), start=1):
        for module, declaration in LEAN_REF.findall(line):
            found.append(Badge(number, module, declaration))
    return found


def _location(decl: LeanDecl, root: Path) -> str:
    try:
        return f"{decl.path.relative_to(root)}:{decl.line}"
    except ValueError:
        return f"{decl.path}:{decl.line}"


def shortest_path(closure: Closure, target: str) -> list[str]:
    """One shortest chain of references from the badge down to `target`."""
    parent: dict[str, str] = {}
    seen = {closure.root}
    queue: deque[str] = deque([closure.root])
    outgoing: dict[str, list[str]] = defaultdict(list)
    for edge in closure.edges:
        outgoing[edge.source].append(edge.target)
    while queue:
        current = queue.popleft()
        if current == target:
            break
        for nxt in outgoing.get(current, ()):
            if nxt not in seen:
                seen.add(nxt)
                parent[nxt] = current
                queue.append(nxt)
    if target != closure.root and target not in parent:
        return [target]
    chain = [target]
    while chain[-1] != closure.root:
        chain.append(parent[chain[-1]])
    return list(reversed(chain))


def render_tree(
    closure: Closure,
    dev: Development,
    flags: dict[str, Flags],
    root: Path,
    *,
    max_depth: int,
) -> list[str]:
    """A spanning tree of the closure: every helper printed once, where first met."""
    lines: list[str] = []
    seen: set[str] = {closure.root}

    def walk(name: str, depth: int) -> None:
        if depth > max_depth:
            return
        for edge in closure.children(name):
            if edge.target in seen:
                continue
            decl = dev.by_full_name.get(edge.target)
            if decl is None:
                continue
            seen.add(edge.target)
            node_flags = flags.get(edge.target, Flags())
            mark = "" if edge.confidence == "scoped" else " ~"
            tail = f"  [{node_flags.render()}]" if node_flags.render() else ""
            lines.append(
                f"  {'  ' * depth}- {edge.target}{mark}"
                f"  <{edge.site}>  {_location(decl, root)}{tail}")
            walk(edge.target, depth + 1)

    walk(closure.root, 0)
    return lines


def render_flagged(
    closure: Closure,
    dev: Development,
    flags: dict[str, Flags],
    root: Path,
) -> list[str]:
    """Every flagged helper, with a shortest chain of references reaching it."""
    lines: list[str] = []
    for name in closure.nodes:
        if name == closure.root:
            continue
        node_flags = flags.get(name)
        if not node_flags:
            continue
        decl = dev.by_full_name.get(name)
        location = _location(decl, root) if decl is not None else "?"
        lines.append(f"  * {name}  {location}")
        lines.append(f"      {node_flags.render()}")
        chain = shortest_path(closure, name)
        lines.append("      via " + " -> ".join(
            part.rsplit(".", 1)[-1] for part in chain))
    return lines


def report(
    root: Path,
    tex_path: Path,
    roster_path: Path,
    args: argparse.Namespace,
) -> int:
    tex = tex_path.read_text(encoding="utf-8")
    found = badges(tex)
    dev = build_development(root)
    corpus = build_corpus(root)
    roster: set[str] = set()
    if roster_path.is_file():
        roster, _stale = read_roster(roster_path)

    badged = frozenset(badge.declaration for badge in found)
    abstractions = tuple(args.abstraction)

    selected = [badge for badge in found
                if args.decl is None or args.decl in badge.declaration]
    if args.decl is not None and not selected:
        print(f"trace-manuscript-deps: no badge matches {args.decl!r}",
              file=sys.stderr)
        return 1

    cache: dict[str, list[Edge]] = {}
    flag_cache: dict[str, Flags] = {}

    def flags_for(name: str) -> Flags:
        if name not in flag_cache:
            decl = dev.by_full_name.get(name)
            flag_cache[name] = (
                Flags() if decl is None
                else compute_flags(decl, corpus, roster, abstractions, badged))
        return flag_cache[name]

    closures: list[tuple[Badge, Closure | None]] = []
    for badge in selected:
        if badge.declaration not in dev.by_full_name:
            closures.append((badge, None))
            continue
        closures.append((badge, closure_of(
            badge.declaration, dev,
            max_depth=args.max_depth, max_nodes=args.max_nodes,
            suffix_fallback=not args.no_suffix_fallback, cache=cache)))

    if args.format == "json":
        payload = {
            "badges": [
                {
                    "tex_line": badge.tex_line,
                    "module": badge.module,
                    "declaration": badge.declaration,
                    "missing": closure is None,
                    "nodes": [] if closure is None else [
                        {
                            "name": name,
                            "depth": closure.depth_of[name],
                            "location": _location(dev.by_full_name[name], root)
                            if name in dev.by_full_name else None,
                            "flags": {
                                "conditional": list(flags_for(name).conditional),
                                "buried": list(flags_for(name).buried),
                                "literature": list(flags_for(name).literature),
                                "abstraction": list(flags_for(name).abstraction),
                                "badged": flags_for(name).badged,
                            },
                        }
                        for name in closure.nodes
                    ],
                    "edges": [] if closure is None else [
                        {"source": e.source, "target": e.target,
                         "site": e.site, "confidence": e.confidence}
                        for e in closure.edges
                    ],
                    "truncated": bool(closure and closure.truncated),
                }
                for badge, closure in closures
            ]
        }
        print(json.dumps(payload, indent=2, sort_keys=True))
        return 0

    if args.format == "dot":
        print("digraph manuscript_deps {")
        print('  rankdir=LR; node [shape=box, fontname="monospace", fontsize=9];')
        emitted: set[tuple[str, str]] = set()
        for badge, closure in closures:
            if closure is None:
                continue
            print(f'  "{badge.declaration}" [style=bold];')
            for edge in closure.edges:
                if (edge.source, edge.target) in emitted:
                    continue
                emitted.add((edge.source, edge.target))
                style = "solid" if edge.confidence == "scoped" else "dashed"
                colour = "black" if edge.site == "proof" else "gray50"
                print(f'  "{edge.source}" -> "{edge.target}" '
                      f'[style={style}, color={colour}];')
        print("}")
        return 0

    # Forward-reference mode: badges whose proofs reach a result the manuscript
    # prints later.  The manuscript does this openly (Theorem A cites the
    # construction section), so a hit is a cross-check, not automatically a
    # defect; a hit the manuscript does *not* announce is a real finding.
    if args.forward_refs:
        tex_line = {badge.declaration: badge.tex_line for badge in found}
        hits = 0
        for badge, closure in closures:
            if closure is None:
                continue
            later = [(tex_line[name], closure.depth_of[name], name)
                     for name in closure.nodes
                     if name != closure.root
                     and tex_line.get(name, 0) > badge.tex_line]
            if not later:
                continue
            hits += 1
            print(f"line {badge.tex_line:5d}  {badge.declaration}")
            for line_number, depth, name in sorted(later):
                print(f"    -> line {line_number:5d}  depth {depth}  {name}")
        print(f"\ntrace-manuscript-deps: {hits} badge(s) reach a later badge")
        return 0

    # Shared-helper mode: which helpers sit on many manuscript paths at once.
    if args.shared is not None:
        paths: dict[str, set[str]] = defaultdict(set)
        for badge, closure in closures:
            if closure is None:
                continue
            for name in closure.nodes:
                if name != closure.root:
                    paths[name].add(badge.declaration)
        rows = [(len(roots), name, roots) for name, roots in paths.items()
                if len(roots) >= args.shared]
        rows.sort(key=lambda row: (-row[0], row[1]))
        for count, name, roots in rows:
            marker = flags_for(name).render()
            print(f"{count:3d}  {name}{'  [' + marker + ']' if marker else ''}")
            for target in sorted(roots):
                print(f"       <- {target}")
        print(f"\ntrace-manuscript-deps: {len(rows)} helper(s) on "
              f">= {args.shared} manuscript paths")
        return 0

    problems: list[str] = []
    total_nodes = 0
    for badge, closure in closures:
        if closure is None:
            problems.append(
                f"line {badge.tex_line}: {badge.declaration} not found in the index")
            print(f"=== {badge.declaration}\n    MISSING FROM INDEX "
                  f"(tex line {badge.tex_line})\n")
            continue
        decl = dev.by_full_name[badge.declaration]
        helper_names = [name for name in closure.nodes if name != closure.root]
        total_nodes += len(helper_names)
        flagged = [name for name in helper_names if flags_for(name)]
        conditional = [name for name in helper_names if flags_for(name).conditional]
        buried = [name for name in helper_names if flags_for(name).buried]
        literature = [name for name in helper_names if flags_for(name).literature]
        abstraction = [name for name in helper_names if flags_for(name).abstraction]
        modules = {dev.by_full_name[name].module for name in helper_names
                   if name in dev.by_full_name}
        deepest = max((closure.depth_of[name] for name in helper_names), default=0)

        if args.summary:
            print(f"{len(helper_names):5d} helpers  {len(modules):3d} modules  "
                  f"depth {deepest}  "
                  f"{len(conditional)}C/{len(buried)}B/"
                  f"{len(literature)}L/{len(abstraction)}A  "
                  f"{badge.declaration}")
        else:
            print(f"=== {badge.declaration}")
            print(f"    tex line {badge.tex_line} | {_location(decl, root)}"
                  f"{' | TRUNCATED' if closure.truncated else ''}")
            print(f"    closure: {len(helper_names)} helpers over "
                  f"{len(modules)} modules, depth {deepest}")
            print(f"    flags: {len(conditional)} conditional, "
                  f"{len(buried)} buried, {len(literature)} literature, "
                  f"{len(abstraction)} abstraction, {len(flagged)} total")
            renderer = (
                render_flagged(closure, dev, flag_cache, root)
                if args.flagged_only
                else render_tree(closure, dev, flag_cache, root,
                                 max_depth=args.max_depth))
            for line in renderer:
                print(line)
            print()

        for name in conditional:
            problems.append(
                f"line {badge.tex_line}: {badge.declaration} reaches {name} "
                f"(depth {closure.depth_of[name]}), whose premises include "
                f"{', '.join(flags_for(name).conditional)}")
        for name in buried:
            problems.append(
                f"line {badge.tex_line}: {badge.declaration} reaches {name} "
                f"(depth {closure.depth_of[name]}), which names the "
                f"never-constructed package(s) "
                f"{', '.join(flags_for(name).buried)} inside a premise type")
        for name in literature:
            problems.append(
                f"line {badge.tex_line}: {badge.declaration} reaches {name} "
                f"(depth {closure.depth_of[name]}), a literature-roster name")

    if args.check:
        if problems:
            print(f"trace-manuscript-deps: {len(problems)} problem(s):",
                  file=sys.stderr)
            for problem in problems:
                print(f"  {problem}", file=sys.stderr)
            return 1
        print(f"trace-manuscript-deps: {len(selected)} badge closures are free of "
              "conditional and literature-tagged helpers")
        return 0

    print(f"trace-manuscript-deps: {len(selected)} badges, "
          f"{total_nodes} helper edges traced, "
          f"{len(dev.by_full_name)} declarations indexed")
    return 0


# ---------------------------------------------------------------------------
# Self-test
# ---------------------------------------------------------------------------


def self_test() -> int:
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        module = root / "GroupApproximation" / "Fake"
        module.mkdir(parents=True)
        (module / "Base.lean").write_text(
            "namespace GroupApproximation\n"
            "structure OpenPackage where\n"
            "  field : Nat\n"
            "def IsThing (n : Nat) : Prop := n = n\n"
            "theorem deep_helper : ∀ (n : Nat), IsThing n := fun n => rfl\n"
            "theorem conditional_helper :\n"
            "    ∀ (_p : OpenPackage) (n : Nat), IsThing n := fun _ n => rfl\n"
            "theorem buried_helper\n"
            "    (_ambient : ∀ k : Nat, k = k → OpenPackage) :\n"
            "    ∀ (n : Nat), IsThing n := fun _ => rfl\n"
            "theorem normMFResidual_bridge : ∀ (n : Nat), IsThing n :=\n"
            "  deep_helper\n"
            "end GroupApproximation\n",
            encoding="utf-8",
        )
        (module / "Mid.lean").write_text(
            "import GroupApproximation.Fake.Base\n"
            "namespace GroupApproximation\n"
            "namespace Mid\n"
            "theorem via_bridge : ∀ (n : Nat), IsThing n :=\n"
            "  normMFResidual_bridge\n"
            "theorem via_conditional : ∀ (n : Nat), IsThing n := by\n"
            "  intro n\n"
            "  exact conditional_helper ⟨0⟩ n\n"
            "theorem via_buried : ∀ (n : Nat), IsThing n := by\n"
            "  intro n\n"
            "  exact buried_helper (fun _ _ => ⟨0⟩) n\n"
            "end Mid\n"
            "end GroupApproximation\n",
            encoding="utf-8",
        )
        (module / "Top.lean").write_text(
            "import GroupApproximation.Fake.Mid\n"
            "namespace GroupApproximation\n"
            "namespace Top\n"
            "open Mid\n"
            "theorem badged_clean : ∀ (n : Nat), IsThing n := via_bridge\n"
            "theorem badged_dirty : ∀ (n : Nat), IsThing n := via_conditional\n"
            "theorem badged_buried : ∀ (n : Nat), IsThing n := via_buried\n"
            "end Top\n"
            "end GroupApproximation\n",
            encoding="utf-8",
        )
        tex = root / "paper.tex"
        tex.write_text(
            r"\leanverified{Fake/Top}{GroupApproximation.Top.badged_clean}" "\n"
            r"\leanverified{Fake/Top}{GroupApproximation.Top.badged_dirty}" "\n",
            encoding="utf-8",
        )

        dev = build_development(root)
        for expected in ("GroupApproximation.Top.badged_clean",
                         "GroupApproximation.Mid.via_bridge",
                         "GroupApproximation.normMFResidual_bridge",
                         "GroupApproximation.deep_helper"):
            if expected not in dev.by_full_name:
                print(f"self-test: {expected} was not indexed", file=sys.stderr)
                return 1

        # The whole point: a three-token top-level proof still reaches depth 3.
        clean = closure_of("GroupApproximation.Top.badged_clean", dev,
                           max_depth=8, max_nodes=200)
        for expected, depth in (("GroupApproximation.Mid.via_bridge", 1),
                                ("GroupApproximation.normMFResidual_bridge", 2),
                                ("GroupApproximation.deep_helper", 3)):
            if clean.depth_of.get(expected) != depth:
                print(f"self-test: {expected} at depth "
                      f"{clean.depth_of.get(expected)}, expected {depth}",
                      file=sys.stderr)
                return 1
        # `open Mid` must be what resolves `via_bridge`; without open tracking
        # the closure stops at depth 0.
        if len(clean.depth_of) < 4:
            print("self-test: open-namespace resolution failed", file=sys.stderr)
            return 1

        corpus = build_corpus(root)
        badged = frozenset({"GroupApproximation.Top.badged_clean",
                            "GroupApproximation.Top.badged_dirty"})
        flags = {
            name: compute_flags(dev.by_full_name[name], corpus, set(),
                                DEFAULT_ABSTRACTIONS, badged)
            for name in dev.by_full_name
        }
        bridge = flags["GroupApproximation.normMFResidual_bridge"]
        if not bridge.abstraction:
            print("self-test: abstraction pattern did not fire", file=sys.stderr)
            return 1
        if flags["GroupApproximation.deep_helper"].abstraction:
            print("self-test: abstraction false positive on deep_helper",
                  file=sys.stderr)
            return 1

        dirty = closure_of("GroupApproximation.Top.badged_dirty", dev,
                           max_depth=8, max_nodes=200)
        if "GroupApproximation.conditional_helper" not in dirty.depth_of:
            print("self-test: conditional helper not reached", file=sys.stderr)
            return 1
        if not flags["GroupApproximation.conditional_helper"].conditional:
            print("self-test: conditional helper not flagged", file=sys.stderr)
            return 1
        if flags["GroupApproximation.deep_helper"].conditional:
            print("self-test: conditional false positive on deep_helper",
                  file=sys.stderr)
            return 1
        if not flags["GroupApproximation.Top.badged_clean"].badged:
            print("self-test: badged flag did not fire", file=sys.stderr)
            return 1

        # The bundling-structure class: the package sits behind a `∀ … → …`
        # inside the premise type, so its head is not the package.  Head-only
        # detection misses it; `buried` must not.
        buried_flags = flags["GroupApproximation.buried_helper"]
        if buried_flags.conditional:
            print("self-test: head detection should not see a buried package",
                  file=sys.stderr)
            return 1
        if "OpenPackage" not in buried_flags.buried:
            print(f"self-test: buried package missed; got {buried_flags.buried}",
                  file=sys.stderr)
            return 1
        if flags["GroupApproximation.deep_helper"].buried:
            print("self-test: buried false positive on deep_helper",
                  file=sys.stderr)
            return 1
        buried_closure = closure_of("GroupApproximation.Top.badged_buried", dev,
                                    max_depth=8, max_nodes=200)
        if "GroupApproximation.buried_helper" not in buried_closure.depth_of:
            print("self-test: buried helper not reached", file=sys.stderr)
            return 1

        # An import the module does not have must not produce an edge.
        (module / "Isolated.lean").write_text(
            "namespace GroupApproximation\n"
            "theorem deep_helper_lookalike : True := trivial\n"
            "end GroupApproximation\n",
            encoding="utf-8",
        )
        dev = build_development(root)
        if "GroupApproximation.Fake.Isolated" not in dev.modules:
            print("self-test: isolated module not indexed", file=sys.stderr)
            return 1
        if "GroupApproximation.Fake.Base" in dev.import_closure(
                "GroupApproximation.Fake.Isolated"):
            print("self-test: import closure is not respecting imports",
                  file=sys.stderr)
            return 1

    print("trace-manuscript-deps: self-test passed")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(
        description="transitive proof-dependency trace for the non-MF badges")
    parser.add_argument("--root", type=Path, default=REPO)
    parser.add_argument("--tex", type=Path, default=DEFAULT_TEX)
    parser.add_argument("--literature-roster", type=Path, default=DEFAULT_ROSTER)
    parser.add_argument("--decl", default=None,
                        help="trace only badges whose declaration contains this")
    parser.add_argument("--max-depth", type=int, default=6)
    parser.add_argument("--max-nodes", type=int, default=4000)
    parser.add_argument("--format", choices=("text", "json", "dot"), default="text")
    parser.add_argument("--summary", action="store_true",
                        help="one line per badge instead of the tree")
    parser.add_argument("--flagged-only", action="store_true",
                        help="print only flagged helpers in each tree")
    parser.add_argument("--shared", type=int, default=None, metavar="N",
                        help="list helpers reached from at least N badges")
    parser.add_argument("--forward-refs", action="store_true",
                        help="list badges whose closure reaches a later badge")
    parser.add_argument("--abstraction", action="append",
                        default=list(DEFAULT_ABSTRACTIONS),
                        help="name fragment marking an abstraction layer")
    parser.add_argument("--no-suffix-fallback", action="store_true",
                        help="drop the dot-notation/export recovery heuristic")
    parser.add_argument("--check", action="store_true",
                        help="exit 1 when a closure contains a conditional or "
                             "literature-tagged helper")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()

    if args.self_test:
        return self_test()

    root = args.root if args.root.is_absolute() else REPO / args.root
    tex = args.tex if args.tex.is_absolute() else root / args.tex
    roster = (args.literature_roster if args.literature_roster.is_absolute()
              else root / args.literature_roster)
    return report(root, tex, roster, args)


if __name__ == "__main__":
    raise SystemExit(main())
