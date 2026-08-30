#!/usr/bin/env python3
"""Sentence-level census of the non-MF manuscript.

The proof ledger grades *claims*: numbered environments and the printed steps
inside their proofs.  That is the right granularity for asking whether the
mathematics is formalized, and it is the wrong granularity for asking whether
the manuscript is 1:1 with the formalization, because a paragraph of prose can
carry a claim that no numbered environment states.  `gate-blindspot-prose-claims`
is the recorded instance: the manifest gate reads only numbered environments,
so a sentence asserting something unproved could sit in the print unnoticed.

This script closes that blindspot by descending to the sentence.  It extracts
every sentence of `non_mf_groups_exist.tex`, records where it sits (section,
environment, label), and joins it to an assignment: either the Lean
declarations that formalize it, or an explicit reason why no declaration can.

    scripts/sentence_census.py                 regenerate the census
    scripts/sentence_census.py --check         fail on any unassigned sentence
    scripts/sentence_census.py --require-complete
                                              also fail on partial coverage
                                              and prose-only proof provenance
    scripts/sentence_census.py --summary       print the counts and stop

## The two files

`metadata/NON_MF_SENTENCE_MAP.tsv` is the **assignment overlay** and is edited
by hand.  Each row is `key<TAB>status<TAB>decls<TAB>note`, where `key` is the
first twelve hex digits of the sha256 of the normalized sentence.  Keying on
content and not on position means an edit elsewhere in the paragraph does not
silently re-point an assignment at a different sentence: a reworded sentence
loses its key and reappears as unassigned, which is the correct behaviour.  If
the same normalized sentence occurs more than once, its key is instead the
hash of its ledger anchor and content; this prevents one overlay judgement from
silently applying at two different manuscript locations.

`metadata/NON_MF_SENTENCE_CENSUS.tsv` is **generated** and must not be edited:
it is the join of the extraction with the overlay, and regenerating it is how
the census stays true after a manuscript edit.

## Statuses

| status | meaning |
| --- | --- |
| `formalized` | Lean declarations in `decls` prove exactly this sentence |
| `ledger` | graded by the proof ledger; `decls` names the row |
| `partial` | one clause is proved and another is not; the note says which |
| `definition` | fixes notation or names an object; the object is in Lean |
| `structural` | says where the argument is going, asserts nothing |
| `attribution` | credits or dates other people's work |
| `provenance` | resource-usage disclosure; quotes rather than asserts |
| `open` | states that something is unknown; no declaration can settle it |
| `unassigned` | not yet triaged --- the state `--check` rejects |

`attribution` and `open` are not excuses: a sentence may only carry them when
it makes no mathematical assertion of its own.  The distinction is the one the
ledger already draws between a step and a tombstone.

## The census NAMES carriers.  It does not COMMISSION them.

A row's `decls` must name a declaration that already earns its place in the
development.  Authoring a new declaration *in order to* fill a row is the same
move as writing a row from fuzzy alignment: it turns the gate green without
adding knowledge.

The concrete failure this rule exists to stop, measured 2026-08-25: of 175
`theorem manuscriptSentence*` declarations under `GroupApproximation/
Manuscript/`, **34 were pure aliases** -- the statement a bare named `Prop`
that an existing theorem already states, and the proof term nothing but that
theorem's name:

    theorem manuscriptSentence19_fullRadical_kills_MFTargets :
        FullRadicalKillsMFTargets :=
      manuscriptFullRadicalKillsMFTargets

That is a rename, not a formalization, and it is not free.  `scripts/Audit.lean`
runs a `DUPLICATE` detector -- "same proposition already proved as X" -- so every
alias is a finding, and the kernel audit was red on 2026-08-25 partly because of
them.  Four wrappers aliased `manuscriptMaximalCStarKazhdanProjectionOrder`
alone, and one aliased another alias.

So: **point the row at the existing declaration.**  Write a new one only when
the printed sentence is genuinely not stated by anything in the tree -- for
instance at the reducible form the manuscript prints, where the existing
theorem is stated in a normalised one.  When you do, the new statement must
differ from the old, or `DUPLICATE` is correct and the row is wrong.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
TEX = os.path.join(ROOT, "non_mf_groups_exist.tex")
MAP = os.path.join(ROOT, "metadata", "NON_MF_SENTENCE_MAP.tsv")
OUT = os.path.join(ROOT, "metadata", "NON_MF_SENTENCE_CENSUS.tsv")
OUT_MD = os.path.join(ROOT, "metadata", "NON_MF_SENTENCE_CENSUS.md")
# Labels printed into the generated files; main() sets them from the
# manuscript and overlay actually processed, so a companion manuscript's
# census does not describe itself as the non-MF paper's.
TEX_LABEL = "non_mf_groups_exist.tex"
MAP_LABEL = "metadata/NON_MF_SENTENCE_MAP.tsv"

# Environments whose body is display material, not prose.  Their content is
# graded through the surrounding claim, and splitting a matrix into sentences
# would be noise.
DISPLAY_ENVS = {
    "equation", "equation*", "align", "align*", "aligned", "array", "gather",
    "gather*", "multline", "multline*", "cases", "matrix", "pmatrix",
    "bmatrix", "tikzpicture", "figure", "table", "tabular", "verbatim",
    "thebibliography", "displaymath", "eqnarray", "eqnarray*", "center",
    "gathered", "split", "subequations", "smallmatrix", "tikzcd", "CD",
}

INLINE_ENV_RE = re.compile(
    r"\\begin\{([A-Za-z][A-Za-z0-9]*\*?)\}"
    r"((?:(?!\\begin\{|\\end\{).)*?)"
    r"\\end\{\1\}", re.S)


def collapse_inline_envs(line: str) -> str:
    """Remove environments that open and close on the same line.

    Only *balanced* pairs go: the regex matches an innermost pair, one whose
    body contains no further `\\begin{`/`\\end{`, so repeating to a fixpoint
    unwinds nesting from the inside out and handles several pairs on one line.
    A pair that is only opened here, or only closed here, is left alone for the
    stack dispatch to see.

    A display environment's body is display material, so it is replaced by a
    space -- keeping it would inject matrix entries into the surrounding
    sentence, which is what the stack skip does for a multi-line display.  Any
    other environment keeps its body, because there the braces are markup
    around prose that still belongs to the sentence.
    """
    while True:
        collapsed = INLINE_ENV_RE.sub(
            lambda m: " " if m.group(1) in DISPLAY_ENVS else m.group(2), line)
        if collapsed == line:
            return line
        line = collapsed


CLAIM_ENVS = {
    "theorem", "lemma", "proposition", "corollary", "definition", "mainthm",
    "question", "remark", "example", "conjecture", "notation", "convention",
    "problem", "fact", "claim", "observation", "abstract",
}

# Abbreviations after which a period does not end a sentence.
ABBREV = [
    "cf", "e.g", "i.e", "etc", "vs", "resp", "Prop", "Thm", "Def", "Cor",
    "Lem", "Ch", "Sec", "Fig", "Eq", "no", "No", "al", "Mr", "Dr", "St",
    "Jr", "approx", "Ex", "cca", "Ph.D", "pp", "vol", "ed", "eds", "Op",
]

SENTENCE_END = re.compile(r"(?<=[.!?])[\"'\)\}]?\s+")


def strip_comments(line: str) -> str:
    out = []
    i = 0
    while i < len(line):
        c = line[i]
        if c == "\\" and i + 1 < len(line):
            out.append(line[i : i + 2])
            i += 2
            continue
        if c == "%":
            break
        out.append(c)
        i += 1
    return "".join(out)


def normalize(sentence: str) -> str:
    """Whitespace-collapsed form; the key is computed from this."""
    return re.sub(r"\s+", " ", sentence).strip()


def key_of(sentence: str) -> str:
    return hashlib.sha256(normalize(sentence).encode("utf-8")).hexdigest()[:12]


def protect(text: str) -> str:
    """Hide periods that do not end sentences, so the splitter cannot see them."""
    text = re.sub(r"\$[^$]*\$", lambda m: m.group(0).replace(".", "\x00"), text)
    text = re.sub(r"\\[a-zA-Z]+\s*\{[^{}]*\}",
                  lambda m: m.group(0).replace(".", "\x00"), text)
    for a in ABBREV:
        text = text.replace(a + ".", a + "\x00")
    text = re.sub(r"(?<=\d)\.(?=\d)", "\x00", text)
    return text


def unprotect(text: str) -> str:
    return text.replace("\x00", ".")


def split_sentences(paragraph: str) -> list[str]:
    guarded = protect(paragraph)
    parts = SENTENCE_END.split(guarded)
    return [unprotect(p).strip() for p in parts if unprotect(p).strip()]


BADGE_VERIFIED = re.compile(r"\\leanverified\{([^}]*)\}\{([^}]*)\}")
BADGE_STEP = re.compile(r"\\leanstep\{([^}]*)\}")

# `check_non_mf_refs.py` defines six two-argument certification macros, not
# one.  The census used to strip only `\leanverified`, so a `\leanequivalent`,
# `\leansupporting`, `\leanconditional`, `\leanpartial` or
# `\leandifferentwitness` survived into the sentence text -- and because the
# key is the sha256 of the normalized sentence, badging a sentence with any of
# the other five silently *rekeyed* it and expired its overlay row.  A badge is
# metadata about a sentence, not part of it: stripping all six keeps the key a
# function of the prose alone, so adding or restatusing a badge never churns
# the overlay.  Keep this list in step with `check_non_mf_refs.STATUSES`.
BADGE_STATUSES = ("verified", "equivalent", "supporting", "conditional",
                  "partial", "differentwitness")
BADGE_ANY = re.compile(
    r"\\lean(?:" + "|".join(BADGE_STATUSES) + r")\{([^}]*)\}\{([^}]*)\}")

# Front-matter macros that carry no mathematical assertion.
FRONT_MATTER = re.compile(
    r"^\s*\\(title|author|subjclass|keywords|thanks|date|dedicatory|address|"
    r"email|maketitle|tableofcontents|bibliographystyle|bibliography|appendix|"
    r"part|paperauthor)\b")

# Layout, not prose.  A line that is only a page break or a counter carries no
# assertion, and letting one through would put a `\newpage` in the census as a
# sentence nobody can formalize.
LAYOUT_ONLY = re.compile(
    r"^\s*(\\(newpage|clearpage|cleardoublepage|par|noindent|smallskip|medskip|"
    r"bigskip|vspace\*?\{[^}]*\}|hspace\*?\{[^}]*\}|setcounter\{[^}]*\}\{[^}]*\}|"
    r"addtocontents\{[^}]*\}\{[^}]*\}|pagebreak|newline|hfill|centering|"
    r"tableofcontents|listoffigures|thispagestyle\{[^}]*\})\s*)+$")


def extract(path: str) -> list[dict]:
    """Walk the tex and return one record per sentence."""
    with open(path, encoding="utf-8") as fh:
        raw = fh.readlines()

    records: list[dict] = []
    env_stack: list[str] = []
    env_records: list[list[int]] = []   # indices of records opened per env
    env_badges: list[list[str]] = []    # badges seen while that env is open
    section = ""
    label = ""
    in_document = False
    para: list[str] = []
    para_line = 0

    def flush() -> None:
        nonlocal para, para_line
        if not para:
            return
        text = " ".join(para)
        para = []
        # An unnumbered display belongs to the sentence around it, not to a
        # sentence of its own: leaving it in makes the splitter cut a clause in
        # half at the display's own punctuation.
        text = re.sub(r"\\\[.*?\\\]", " ", text, flags=re.S)
        text = re.sub(r"\$\$.*?\$\$", " ", text, flags=re.S)
        if not text.strip():
            return
        env = env_stack[-1] if env_stack else ""
        for s in split_sentences(text):
            badges = [d for _, d in BADGE_VERIFIED.findall(s)]
            steps = BADGE_STEP.findall(s)
            for b in badges:
                for lst in env_badges:
                    lst.append(b)
            clean = BADGE_ANY.sub("", s)
            clean = BADGE_STEP.sub("", clean)
            clean = normalize(clean)
            if not re.search(r"[A-Za-z]", clean):
                continue
            records.append({
                "key": key_of(clean),
                "line": para_line,
                "section": section,
                "env": env,
                "label": label,
                "badges": badges,
                "steps": steps,
                "sentence": clean,
            })
            for lst in env_records:
                lst.append(len(records) - 1)

    in_display = False
    front_depth = 0

    for n, rawline in enumerate(raw, start=1):
        line = strip_comments(rawline).rstrip("\n")

        # `\\[2pt]` is a line break carrying vertical space, not the start of
        # an unnumbered display.  Reading it as one opens a display that never
        # closes: the `\end{tikzpicture}` after it is swallowed, its `figure`
        # stays open to the end of the document, and every paragraph from
        # there on is skipped as display material.
        line = re.sub(r"\\\\\[[^\]]*\]", " ", line)

        # An environment that opens and closes on the SAME line changes no
        # nesting and must not touch the stack.  The dispatch below tests
        # `\begin` before `\end` and returns early for a display environment,
        # so `\begin{pmatrix}I&0\\-X^{-1}&I\end{pmatrix}` used to push
        # `pmatrix` and never pop it.  Five such lines in
        # `eq:whitehead-factorization` left four `pmatrix` on the stack at end
        # of file; `\end{align}` popped one of them instead of the `align`, and
        # because a display environment on top of the stack skips every line
        # under it, the rest of the document after line 1528 was dropped --
        # not marked `unassigned`, but never keyed at all, so `--check` stayed
        # green over roughly the last third of the manuscript.  Collapsing
        # balanced pairs first fixes both halves: nothing spurious is pushed,
        # and `\end` again meets the environment it closes.
        line = collapse_inline_envs(line)

        # An unnumbered display that spans a paragraph break cannot be removed
        # by a regex over one paragraph, so it is tracked here instead.
        if in_display:
            if "\\]" in line:
                in_display = False
                line = line.split("\\]", 1)[1]
            else:
                continue
        if "\\[" in line and "\\]" not in line.split("\\[", 1)[1]:
            line = line.split("\\[", 1)[0]
            in_display = True

        # A front-matter macro's argument may run over several lines; consume
        # it to its closing brace rather than reading its tail as a sentence.
        if front_depth:
            front_depth += line.count("{") - line.count("}")
            if front_depth < 0:
                front_depth = 0
            continue

        # A label alone on a line belongs to the section heading above it.
        if re.match(r"^\s*\\label\{[^}]*\}\s*$", line):
            mlab = re.search(r"\\label\{([^}]*)\}", line)
            if mlab and (not env_stack or env_stack[-1] in CLAIM_ENVS):
                label = mlab.group(1)
            continue

        if not in_document:
            if r"\begin{document}" in line:
                in_document = True
            continue

        if FRONT_MATTER.match(line) or LAYOUT_ONLY.match(line):
            flush()
            front_depth = max(0, line.count("{") - line.count("}"))
            continue

        mb = re.match(r"\s*\\begin\{([^}]*)\}", line)
        me = re.match(r"\s*\\end\{([^}]*)\}", line)
        ms = re.match(r"\s*\\(sub)*section\*?\{(.*?)\}", line)

        if ms:
            flush()
            section = ms.group(2)
            label = ""
            mlab = re.search(r"\\label\{([^}]*)\}", line)
            if mlab:
                label = mlab.group(1)
            continue

        if mb:
            flush()
            env = mb.group(1)
            env_stack.append(env)
            env_records.append([])
            env_badges.append([])
            mlab = re.search(r"\\label\{([^}]*)\}", line)
            if mlab and env in CLAIM_ENVS:
                label = mlab.group(1)
            if env in DISPLAY_ENVS:
                continue
            rest = line[mb.end():]
            rest = re.sub(r"^\[[^\]]*\]", "", rest)
            rest = re.sub(r"\\label\{[^}]*\}", "", rest)
            if rest.strip():
                para_line = para_line or n
                para.append(rest.strip())
                para_line = n
            continue

        if me:
            flush()
            if env_stack:
                closing = env_stack.pop()
                idxs = env_records.pop()
                raw_badges = env_badges.pop()
                badges = raw_badges if closing in CLAIM_ENVS else []
                # a badge anywhere in a claim environment certifies the
                # statement that environment prints, so it belongs to every
                # sentence of the statement
                for i in idxs:
                    for b in badges:
                        if b not in records[i]["badges"]:
                            records[i]["badges"].append(b)
            continue

        if env_stack and env_stack[-1] in DISPLAY_ENVS:
            continue

        if not line.strip():
            flush()
            continue

        # A display's own label must not become the label of the prose around
        # it: `eq:corner-spectral` is an equation inside a proof, and letting
        # it win hides that proof's sentences from the claim they belong to.
        mlab = re.search(r"\\label\{([^}]*)\}", line)
        if mlab and (not env_stack or env_stack[-1] in CLAIM_ENVS):
            label = mlab.group(1)

        if re.match(r"\s*\\item\b", line):
            # Each list item is its own prose unit.  Without this flush an
            # entire enumerate becomes one paragraph, so every sentence in a
            # multi-question list inherits whichever prose anchor happens to
            # be visited last.  Keep the prose after the bullet, but never let
            # it share an anchor with the preceding item.
            flush()
            line = re.sub(r"^\s*\\item\s*", "", line)

        if not para:
            para_line = n
        para.append(line.strip())

    flush()
    return records


LEDGER = os.path.join(ROOT, "metadata", "NON_MF_PROOF_LEDGER.md")
ROW_ID = re.compile(r"^[A-Z]{2,4}\.\d+[a-z]?$")


def load_ledger(path: str = LEDGER) -> tuple[dict[str, list[str]], list[tuple[str, str]]]:
    """Rows by anchor and the prose probes.

    The ledger is the existing claim-level grading and the census does not
    duplicate it: where a sentence sits under an anchor the ledger already
    grades, the census says so and names the rows.  Duplicating the grade here
    would give two places to update and one of them would go stale.
    """
    rows: dict[str, list[str]] = {}
    probes: list[tuple[str, str]] = []
    if not os.path.exists(path):
        return rows, probes
    with open(path, encoding="utf-8") as fh:
        for line in fh:
            if not line.startswith("|"):
                continue
            c = [x.strip() for x in line.strip().strip("|").split("|")]
            if len(c) >= 6 and ROW_ID.match(c[0]):
                rows.setdefault(c[1], []).append(c[0])
            elif len(c) >= 3 and c[1] == "prose":
                probe = c[2].strip()
                if probe.startswith("`") and probe.endswith("`"):
                    probes.append((c[0], probe[1:-1]))
    return rows, probes


def attach_anchors(records: list[dict], path: str,
                   probes: list[tuple[str, str]]) -> None:
    """Give every record the ledger anchor whose passage contains it."""
    with open(path, encoding="utf-8") as fh:
        lines = [strip_comments(l) for l in fh]

    probe_line: dict[str, int] = {}
    for anchor, probe in probes:
        for n, line in enumerate(lines, start=1):
            if probe in line:
                probe_line[anchor] = n
                break

    starts = sorted({r["line"] for r in records})
    for r in records:
        r["anchor"] = r["label"]
    for anchor, n in probe_line.items():
        candidates = [s for s in starts if s <= n]
        if not candidates:
            continue
        para = max(candidates)
        for r in records:
            if r["line"] == para:
                r["anchor"] = anchor

    # Content hashes are stable under unrelated edits, but identical fragments
    # such as “Then” occur in unrelated proofs.  Disambiguate only collisions,
    # using the already-attached semantic anchor rather than a volatile line
    # number, and reject the one case that would still be ambiguous.
    by_key: dict[str, list[dict]] = {}
    for r in records:
        by_key.setdefault(r["key"], []).append(r)
    for same in by_key.values():
        if len(same) == 1:
            continue
        seen: dict[str, int] = {}
        for r in same:
            base = r.get("anchor", "") + "\0" + r["sentence"]
            n = seen.get(base, 0)
            seen[base] = n + 1
            # A repeated fragment inside ONE anchor (e.g. "Then" before two
            # displays) gets an occurrence counter appended to the hashed
            # text.  The first occurrence keeps the un-numbered key, so all
            # previously assigned rows are undisturbed.
            scoped = key_of(base if n == 0 else base + f"\0#{n + 1}")
            r["key"] = scoped
    if len({r["key"] for r in records}) != len(records):
        raise ValueError("sentence keys are not unique after anchor disambiguation")


def load_map(path: str) -> dict[str, dict]:
    out: dict[str, dict] = {}
    if not os.path.exists(path):
        return out
    with open(path, encoding="utf-8") as fh:
        for line in fh:
            line = line.rstrip("\n")
            if not line.strip() or line.startswith("#"):
                continue
            cols = line.split("\t")
            while len(cols) < 4:
                cols.append("")
            if cols[0] in out:
                raise ValueError(f"duplicate sentence-map key: {cols[0]}")
            out[cols[0]] = {
                "status": cols[1].strip(),
                "decls": cols[2].strip(),
                "note": cols[3].strip(),
            }
    return out


def join(records: list[dict], assignments: dict[str, dict],
         rows: dict[str, list[str]] | None = None,
         badges_need_rows: bool = False) -> list[dict]:
    """Overlay first, then the manuscript's own badges, then unassigned.

    A `\\leanverified` badge inside a claim environment is the manuscript
    asserting that a named declaration proves what that environment prints, and
    a `\\leanstep` is the same assertion for one step of a proof.  Those are
    assignments the manuscript already carries, so the census reads them rather
    than asking a human to retype them; the overlay wins where it speaks,
    because a hand assignment is a judgement and a badge is a pin.

    Under `badges_need_rows` a badge stops being an assignment.  A badge is the
    manuscript certifying itself, and while the proof ledger was live that
    self-certification was harmless because `check_badge_coverage` separately
    demanded a recorded human grading for every `\\leanverified`.  The paper's
    ledger was retired on 2026-08-25, so for the paper a badge would otherwise
    be the *only* grading a claim ever receives.  A badged sentence with no
    overlay row therefore reads `unassigned` -- the status `--check` rejects --
    and keeps the badge's declarations in `decls` so whoever assigns it can see
    what the manuscript claims.  `verify_decls` skips unassigned rows, so those
    names are recorded without being counted as verified; `check_non_mf_refs.py`
    is what checks that they resolve.

    The flag is off by default because the notes census legitimately leans on
    badge assignment (214 of its sentences at the time of writing), and its
    proof ledger is still live and still carries the badge obligation.
    """
    rows = rows or {}
    for r in records:
        a = assignments.get(r["key"])
        if a and a.get("status"):
            r.update(a)
            r.setdefault("note", "")
            continue
        if badges_need_rows and (r.get("steps") or r.get("badges")):
            r["status"] = "unassigned"
            r["decls"] = " ".join(r.get("badges") or r.get("steps"))
            r["note"] = ("printed badge recorded; an overlay assignment is "
                         "owed because the paper's proof ledger is retired")
        elif r.get("steps"):
            r["status"] = "ledger"
            r["decls"] = " ".join(r["steps"])
            r["note"] = "from the printed \\leanstep badge"
        elif r.get("badges"):
            r["status"] = "formalized"
            r["decls"] = " ".join(r["badges"])
            r["note"] = "from the printed \\leanverified badge"
        elif len(rows.get(r.get("anchor", ""), [])) == 1:
            ids = rows[r["anchor"]]
            r["status"] = "ledger"
            r["decls"] = " ".join(ids)
            r["note"] = "the single ledger row for this anchor"
        elif rows.get(r.get("anchor", "")):
            r["status"] = "unassigned"
            r["decls"] = ""
            r["note"] = (
                f"anchor has {len(rows[r['anchor']])} ledger rows; an explicit "
                "sentence-level assignment is required")
        else:
            r["status"] = "unassigned"
            r["decls"] = ""
            r["note"] = ""
    return records


# The detectors that mean *the theorem is not available unconditionally*: a
# premise nothing in the corpus produces, or a transcription of a literature
# theorem.  The standing order is that neither counts as formalization.
CONDITIONAL_DETECTORS = {
    "buried-conditional", "conditional-data", "known-conditional",
    "literature-input", "open-predicate",
}

def write_tsv(records: list[dict], path: str) -> None:
    with open(path, "w", encoding="utf-8") as fh:
        fh.write("# GENERATED by scripts/sentence_census.py -- do not edit.\n")
        fh.write(f"# Edit {MAP_LABEL} and regenerate.\n")
        fh.write("key\tline\tsection\tenv\tlabel\tstatus\tdecls\tsentence\n")
        for r in records:
            fh.write("\t".join([
                r["key"], str(r["line"]), r["section"], r["env"], r["label"],
                r["status"], r["decls"], r["sentence"],
            ]) + "\n")


def counts(records: list[dict]) -> dict[str, int]:
    out: dict[str, int] = {}
    for r in records:
        out[r["status"]] = out.get(r["status"], 0) + 1
    return out


def write_md(records: list[dict], path: str) -> None:
    c = counts(records)
    total = len(records)
    done = (c.get("formalized", 0) + c.get("ledger", 0)
            + c.get("definition", 0))
    with open(path, "w", encoding="utf-8") as fh:
        fh.write(f"# {TEX_LABEL}: sentence-level census\n\n")
        fh.write(
            "Generated by `scripts/sentence_census.py` from "
            f"`{TEX_LABEL}`.  Do not edit: the assignments live in "
            f"`{MAP_LABEL}` and everything here is their "
            "join with the extraction.\n\n")
        fh.write(
            "The proof ledger grades claims; this census grades **sentences**, "
            "which is the granularity at which a prose assertion can hide from "
            "a gate that reads only numbered environments.\n\n")
        fh.write("| status | sentences |\n| --- | --- |\n")
        for k in sorted(c, key=lambda k: -c[k]):
            fh.write(f"| `{k}` | {c[k]} |\n")
        fh.write(f"| **total** | **{total}** |\n\n")
        fh.write(f"Completely formalized or definitional: **{done}/{total}**"
                 f" ({100.0 * done / max(total, 1):.1f}%).\n\n")
        fh.write(
            "A sentence under a single-row ledger anchor inherits that forced "
            "row.  A sentence under a multi-row anchor must name its row or "
            "rows explicitly in `metadata/NON_MF_SENTENCE_MAP.tsv`; no text-"
            "similarity guess and no whole-anchor fallback is accepted.\n\n")
        gaps = [r for r in records
                if r["status"] in {"partial", "open", "unassigned"}]
        fh.write("## What no declaration establishes\n\n")
        if not gaps:
            fh.write("Every sentence carries a declaration, a ledger row, or a "
                     "reason no declaration applies.\n\n")
        else:
            fh.write(
                "These are the sentences the development does not settle, "
                "verbatim.  `open` sentences say that something is unknown and "
                "no declaration could settle them; `partial` sentences have a "
                "clause that is proved and a clause that is not; `unassigned` "
                "sentences have not been triaged at all.\n\n")
            for r in gaps:
                fh.write(f"* **`{r['status']}`**, line {r['line']} --- "
                         f"{r['sentence']}\n")
                if r.get("note"):
                    fh.write(f"  * {r['note']}\n")
            fh.write("\n")
        fh.write("## By section\n\n| section | sentences | unassigned |\n")
        fh.write("| --- | --- | --- |\n")
        secs: dict[str, list[int]] = {}
        for r in records:
            s = secs.setdefault(r["section"] or "(front matter)", [0, 0])
            s[0] += 1
            if r["status"] == "unassigned":
                s[1] += 1
        for k, v in secs.items():
            fh.write(f"| {k} | {v[0]} | {v[1]} |\n")


DECL_DEF = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|"
    r"nonrec\s+|partial\s+|unsafe\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|instance|inductive|class)\s+"
    r"([^\W\d][\w'!?.]*)", re.UNICODE)


def declared_names() -> set[str]:
    """Every declaration name the corpus defines, by its last component."""
    names: set[str] = set()
    for base, _dirs, files in os.walk(os.path.join(ROOT, "GroupApproximation")):
        for fn in files:
            if not fn.endswith(".lean"):
                continue
            with open(os.path.join(base, fn), encoding="utf-8") as fh:
                for line in fh:
                    m = DECL_DEF.match(line)
                    if m:
                        # a declaration may be written with its namespace
                        # inline, so record the last component too
                        names.add(m.group(1))
                        names.add(m.group(1).rsplit(".", 1)[-1])
    return names


def verify_decls(records: list[dict]) -> list[str]:
    """Names in the `decls` column that the corpus does not define.

    An assignment that names a declaration nobody wrote is worse than no
    assignment: it reads as coverage.  This is the check that keeps the census
    honest against typos and against a rename landing elsewhere.
    """
    known = declared_names()
    bad: list[str] = []
    for r in records:
        if r["status"] not in {"formalized", "definition", "partial"}:
            continue
        for d in r["decls"].split():
            if "." not in d:
                continue
            if d.rsplit(".", 1)[1] not in known:
                bad.append(f"{r['key']}\t{d}")
    return bad


def verify_unconditional(records: list[dict]) -> list[str]:
    """Declarations the census names that are conditional or literature-fed.

    The standing order is that a conditional formalization does not count and
    neither does a literature input: a theorem available only to a caller who
    supplies an unprovable premise formalizes nothing about the manuscript's
    sentence.  `scripts/check_non_mf_unconditional.py` already enforces that on
    the badge surface, where the manuscript itself does the citing.  The census
    names declarations the badges do not, so it runs the same classifier over
    its own assignments.
    """
    sys.path.insert(0, HERE)
    import importlib
    from pathlib import Path
    m = importlib.import_module("check_non_mf_unconditional")
    corpus = m.build_corpus(Path(ROOT))
    roster, _ = m.read_roster(Path(ROOT) / m.DEFAULT_ROSTER)
    bad: list[str] = []
    for r in records:
        if r["status"] not in {"formalized", "definition", "partial"}:
            continue
        for name in r["decls"].split():
            # the corpus indexes declarations by the name their module writes,
            # which is the short one inside a namespace
            decl = (corpus.by_name.get(name)
                    or corpus.by_name.get(name.rsplit(".", 1)[-1]))
            if decl is None:
                continue
            for detector, detail in m.classify(corpus, decl, roster, name):
                if detector not in CONDITIONAL_DETECTORS:
                    # `header-binder`, `open-variable` and `definition-only`
                    # are badge-surface hygiene: a printed badge must sit over
                    # a binder-free statement.  A census assignment is not a
                    # badge, and a theorem whose binders are its own subject
                    # matter -- a group, a homomorphism, a hypothesis about
                    # them -- is unconditional whatever its header looks like.
                    continue
                bad.append(f"{r['key']}\t{name}\t{detector}\t{detail[:140]}")
    return bad


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true",
                    help="exit nonzero if any sentence is unassigned")
    ap.add_argument("--require-complete", action="store_true",
                    help=("exit nonzero if any sentence is unassigned, only "
                          "partially formalized, or carries prose-only proof "
                          "provenance"))
    ap.add_argument("--summary", action="store_true")
    ap.add_argument("--list-unassigned", action="store_true")
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--verify-decls", action="store_true",
                    help="check that every named declaration exists")
    ap.add_argument("--verify-unconditional", action="store_true",
                    help="check that no named declaration is conditional")
    ap.add_argument("--tex", default=TEX)
    ap.add_argument("--map", dest="map_path", default=MAP)
    ap.add_argument("--ledger", default=LEDGER)
    ap.add_argument("--out", default=OUT)
    ap.add_argument("--out-md", default=OUT_MD)
    ap.add_argument("--badges-need-rows", action="store_true",
                    help=("a printed badge no longer assigns a sentence; every "
                          "badged sentence needs an overlay row.  Required for "
                          "the paper, whose proof ledger is retired and whose "
                          "badges would otherwise certify themselves"))
    args = ap.parse_args()
    global TEX_LABEL, MAP_LABEL
    TEX_LABEL = os.path.relpath(os.path.abspath(args.tex), ROOT)
    MAP_LABEL = os.path.relpath(os.path.abspath(args.map_path), ROOT)

    rows, probes = load_ledger(args.ledger)
    records = extract(args.tex)
    attach_anchors(records, args.tex, probes)
    overlay = load_map(args.map_path)
    records = join(records, overlay, rows, args.badges_need_rows)

    record_keys = {r["key"] for r in records}
    ledger_ids = {row for anchor_rows in rows.values() for row in anchor_rows}
    overlay_errors: list[str] = []
    for key in sorted(set(overlay) - record_keys):
        overlay_errors.append(f"stale overlay key {key}")
    valid_statuses = {
        "formalized", "ledger", "partial", "definition", "structural",
        "attribution", "provenance", "open",
    }
    for key, assignment in overlay.items():
        if assignment["status"] not in valid_statuses:
            overlay_errors.append(
                f"{key}: invalid overlay status {assignment['status']!r}")
        if assignment["status"] == "ledger":
            named = assignment["decls"].split()
            if not named:
                overlay_errors.append(f"{key}: ledger assignment names no row")
            for row in named:
                if row not in ledger_ids:
                    overlay_errors.append(f"{key}: unknown ledger row {row}")

    if args.json:
        print(json.dumps(records, indent=1))
        return 0

    if args.verify_unconditional:
        bad = verify_unconditional(records)
        for b in bad:
            print("CONDITIONAL\t" + b)
        print(f"{len(bad)} conditional or literature-fed assignment(s)")
        return 1 if bad else 0

    if args.verify_decls:
        bad = verify_decls(records)
        for b in bad:
            print("MISSING DECL\t" + b)
        print(f"{len(bad)} missing of "
              f"{sum(len(r['decls'].split()) for r in records)} named")
        return 1 if bad else 0

    if args.list_unassigned:
        for r in records:
            if r["status"] == "unassigned":
                print(f"{r['key']}\t{r['line']}\t{r['label'] or r['env'] or r['section']}\t{r['sentence'][:160]}")
        return 0

    if not args.summary:
        write_tsv(records, args.out)
        write_md(records, args.out_md)

    c = counts(records)
    total = len(records)
    for k in sorted(c, key=lambda k: -c[k]):
        print(f"{k:14s} {c[k]:5d}")
    print(f"{'total':14s} {total:5d}")

    for error in overlay_errors:
        print(f"OVERLAY ERROR: {error}")

    incomplete = (c.get("unassigned", 0) + c.get("partial", 0) +
                  c.get("provenance", 0))
    if ((args.check and (c.get("unassigned") or overlay_errors)) or
            (args.require_complete and (incomplete or overlay_errors))):
        if c.get("unassigned"):
            print(f"\nFAIL: {c['unassigned']} sentences carry no assignment.")
        if args.require_complete and c.get("partial"):
            print(f"FAIL: {c['partial']} sentences are only partially formalized.")
        if args.require_complete and c.get("provenance"):
            print(f"FAIL: {c['provenance']} proof-route sentences carry only "
                  "prose provenance.")
        if overlay_errors:
            print(f"FAIL: {len(overlay_errors)} overlay integrity error(s).")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
