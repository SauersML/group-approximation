#!/usr/bin/env python3
"""Validate the theorem-by-theorem manifest for the non-MF manuscript.

Unlike the margin-link checker, this gate starts from *every* numbered
theorem-like environment.  Each environment must occur exactly once in the
JSON manifest.  A machine-checked claim carries an exact declaration mapping;
a paper-proved claim or a stated literature input records that boundary
explicitly.  The manifest records source declarations, paper dependencies,
external inputs, and the proposition's object identity.

The normalized SHA-256 digest is deliberately a digest of the printed
statement, not of its proof or nearby prose.  Editing a quantified object,
hypothesis, target, or conclusion therefore forces an explicit manifest
review.  This is still not an automated proof of semantic equivalence; exact
status ultimately requires a Lean wrapper with the same outer proposition.
The gate does make that human judgment complete, explicit, and drift-proof,
without requiring the manuscript to hide a theorem merely because it is
proved on paper rather than in Lean.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from lean_decls import build_index


REPO = Path(__file__).resolve().parent.parent
DEFAULT_TEX = REPO / "non_mf_groups_exist.tex"
DEFAULT_MANIFEST = REPO / "metadata" / "NON_MF_NUMBERED_CLAIMS.json"

RESULT_ENVS = (
    "mainthm",
    "theorem",
    "proposition",
    "lemma",
    "corollary",
    "definition",
    "construction",
    "fact",
    "claim",
    "example",
)
STATUSES = {"exact", "paper-proof", "literature-input"}
ROLES = {"exact"}
BADGE_TO_ROLE = {
    "verified": "exact",
}

BEGIN_RE = re.compile(
    r"\\begin\{(?P<env>" + "|".join(RESULT_ENVS) +
    r")\}(?:\[(?P<title>[^\]]*)\])?"
)
LABEL_RE = re.compile(r"\\label\{([^{}]+)\}")
BADGE_RE = re.compile(
    r"\\lean(?P<status>verified)\s*"
    r"\{(?P<module>[^{}]+)\}\s*\{(?P<declaration>[^{}]+)\}"
)
ANY_BADGE_RE = re.compile(
    r"\\lean(?P<status>[A-Za-z]+)\s*"
    r"\{(?P<module>[^{}]+)\}\s*\{(?P<declaration>[^{}]+)\}"
)
BADGE_HEAD_RE = re.compile(r"\\lean(?P<status>[A-Za-z]+)\b")
COMMENT_RE = re.compile(r"(?<!\\)%[^\n]*")


@dataclass(frozen=True)
class PrintedClaim:
    claim_id: str
    environment: str
    title: str
    line: int
    statement_sha256: str
    badges: tuple[tuple[str, str, str], ...]
    badge_macros: tuple[str, ...]


def _strip_comments(source: str) -> str:
    return COMMENT_RE.sub("", source)


def _strip_badges(source: str) -> str:
    return ANY_BADGE_RE.sub("", source)


def _statement_digest(block: str, env: str) -> str:
    """Digest the normalized printed statement, excluding bookkeeping."""
    body = block
    body = re.sub(r"^\\begin\{" + re.escape(env) +
                  r"\}(?:\[[^\]]*\])?", "", body)
    body = re.sub(r"\\end\{" + re.escape(env) + r"\}\s*$", "", body)
    body = LABEL_RE.sub("", body)
    body = _strip_badges(body)
    body = re.sub(r"\s+", " ", body).strip()
    return hashlib.sha256(body.encode("utf-8")).hexdigest()


def read_printed_claims(tex: Path) -> list[PrintedClaim]:
    source = _strip_comments(tex.read_text(encoding="utf-8"))
    claims: list[PrintedClaim] = []
    cursor = 0
    while match := BEGIN_RE.search(source, cursor):
        env = match.group("env")
        end_token = rf"\end{{{env}}}"
        end = source.find(end_token, match.end())
        if end < 0:
            raise ValueError(
                f"line {source.count(chr(10), 0, match.start()) + 1}: "
                f"unterminated {env} environment"
            )
        stop = end + len(end_token)
        block = source[match.start():stop]
        labels = LABEL_RE.findall(block)
        line = source.count("\n", 0, match.start()) + 1
        if not labels:
            raise ValueError(
                f"line {line}: numbered {env} environment has no stable label"
            )
        # The first label belongs to the theorem environment.  A long
        # statement may legitimately contain separately numbered displayed
        # equations after it (Definition E is the important example).
        claim_id = labels[0]
        badges = tuple(
            (BADGE_TO_ROLE[b.group("status")], b.group("module").strip(),
             b.group("declaration").strip())
            for b in BADGE_RE.finditer(block)
        )
        # Scan macro heads independently of their arguments.  Otherwise a
        # legacy nonexact badge could hide beside a valid badge merely by
        # inserting TeX-legal whitespace before its first argument.
        badge_macros = tuple(
            b.group("status") for b in BADGE_HEAD_RE.finditer(block)
        )
        # A few status badges intentionally sit immediately after the theorem
        # environment.  Associate only a consecutive badge run; ordinary prose
        # ends the run, so a later theorem cannot inherit a badge accidentally.
        tail_cursor = stop
        while True:
            whitespace = re.match(r"\s*", source[tail_cursor:])
            assert whitespace is not None
            badge_at = tail_cursor + whitespace.end()
            b = ANY_BADGE_RE.match(source, badge_at)
            if b is None:
                break
            status = b.group("status")
            badge_macros += (status,)
            if status == "verified":
                badges += ((BADGE_TO_ROLE[status],
                            b.group("module").strip(),
                            b.group("declaration").strip()),)
            tail_cursor = b.end()
        claims.append(PrintedClaim(
            claim_id=claim_id,
            environment=env,
            title=(match.group("title") or "").strip(),
            line=line,
            statement_sha256=_statement_digest(block, env),
            badges=badges,
            badge_macros=badge_macros,
        ))
        cursor = stop
    return claims


def _module_path(repo: Path, module: str) -> Path:
    return repo / "GroupApproximation" / f"{module}.lean"


def _full_name(declaration: str) -> str:
    if declaration.startswith("GroupApproximation."):
        return declaration
    return f"GroupApproximation.{declaration}"


def manifest_declarations(manifest_path: Path) -> set[str]:
    """Every declaration named by the numbered-claim manifest."""
    payload = json.loads(manifest_path.read_text(encoding="utf-8"))
    return {
        _full_name(ref["declaration"])
        for entry in payload.get("claims", [])
        for ref in entry.get("lean", [])
        if isinstance(ref, dict) and isinstance(ref.get("declaration"), str)
    }


def validate(repo: Path, tex: Path, manifest_path: Path,
             dependency_manifests: tuple[Path, ...] = ()) -> list[str]:
    problems: list[str] = []
    try:
        printed = read_printed_claims(tex)
    except ValueError as error:
        return [str(error)]
    try:
        payload = json.loads(manifest_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        return [f"cannot read {manifest_path}: {error}"]

    if not isinstance(payload, dict) or payload.get("schema_version") != 1:
        return ["manifest must be an object with schema_version 1"]
    entries = payload.get("claims")
    if not isinstance(entries, list):
        return ["manifest field `claims` must be a list"]

    external_dependency_ids: set[str] = set()
    for dependency_manifest in dependency_manifests:
        try:
            dependency_payload = json.loads(
                dependency_manifest.read_text(encoding="utf-8"))
            external_dependency_ids.update(
                entry["id"] for entry in dependency_payload.get("claims", [])
                if isinstance(entry, dict) and isinstance(entry.get("id"), str))
        except (OSError, json.JSONDecodeError) as error:
            problems.append(
                f"cannot read dependency manifest {dependency_manifest}: {error}")

    printed_by_id = {claim.claim_id: claim for claim in printed}
    if len(printed_by_id) != len(printed):
        problems.append("printed theorem-like environments have duplicate labels")

    manifest_by_id: dict[str, dict] = {}
    for number, entry in enumerate(entries, 1):
        where = f"manifest entry {number}"
        if not isinstance(entry, dict):
            problems.append(f"{where} is not an object")
            continue
        claim_id = entry.get("id")
        if not isinstance(claim_id, str) or not claim_id:
            problems.append(f"{where} has no nonempty string `id`")
            continue
        if claim_id in manifest_by_id:
            problems.append(f"duplicate manifest id `{claim_id}`")
        manifest_by_id[claim_id] = entry

    for claim_id in sorted(printed_by_id.keys() - manifest_by_id.keys()):
        claim = printed_by_id[claim_id]
        problems.append(
            f"{tex.name}:{claim.line}: numbered claim `{claim_id}` has no manifest entry"
        )
    for claim_id in sorted(manifest_by_id.keys() - printed_by_id.keys()):
        problems.append(f"manifest entry `{claim_id}` has no numbered TeX claim")
    printed_order = [claim.claim_id for claim in printed]
    manifest_order = [entry.get("id") for entry in entries if isinstance(entry, dict)]
    if manifest_order != printed_order:
        problems.append(
            "manifest claim order differs from the numbered-claim order in TeX"
        )

    index = build_index(repo)
    for claim in printed:
        entry = manifest_by_id.get(claim.claim_id)
        if entry is None:
            continue
        prefix = f"{claim.claim_id}"
        if entry.get("environment") != claim.environment:
            problems.append(
                f"{prefix}: environment is `{claim.environment}` in TeX, not "
                f"`{entry.get('environment')}`"
            )
        if entry.get("title", "") != claim.title:
            problems.append(
                f"{prefix}: title drift: TeX has {claim.title!r}, manifest has "
                f"{entry.get('title', '')!r}"
            )
        if entry.get("statement_sha256") != claim.statement_sha256:
            problems.append(
                f"{prefix}: printed statement changed; review the proposition and "
                "update its statement_sha256 deliberately"
            )

        status = entry.get("status")
        if status not in STATUSES:
            problems.append(f"{prefix}: invalid status `{status}`")
        forbidden_badges = sorted({
            badge for badge in claim.badge_macros if badge != "verified"
        })
        if forbidden_badges:
            rendered = ", ".join(f"\\lean{badge}" for badge in forbidden_badges)
            problems.append(
                f"{prefix}: forbidden nonexact manuscript badge(s): {rendered}"
            )
        if status in {"paper-proof", "literature-input"}:
            if claim.badges:
                problems.append(
                    f"{prefix}: {status} claim must carry no "
                    "in-environment badge")
            if status == "literature-input" and not entry.get("external_inputs"):
                problems.append(
                    f"{prefix}: literature-input claim must state its "
                    "external inputs")
        elif not claim.badges:
            problems.append(
                f"{prefix}: exact claim must carry at least one "
                "\\leanverified badge"
            )
        elif any(role != "exact" for role, _m, _d in claim.badges):
            problems.append(f"{prefix}: manuscript badges must have the exact role")

        for field in ("dependencies", "extra_assumptions", "external_inputs"):
            value = entry.get(field)
            if not isinstance(value, list) or not all(
                    isinstance(item, str) and item for item in value):
                problems.append(f"{prefix}: `{field}` must be a list of nonempty strings")
        for dependency in entry.get("dependencies", []):
            if (dependency not in printed_by_id
                    and dependency not in external_dependency_ids):
                problems.append(
                    f"{prefix}: dependency `{dependency}` is not a numbered claim id"
                )

        gap = entry.get("coverage_gap")
        if not isinstance(gap, str):
            problems.append(f"{prefix}: `coverage_gap` must be a string")
        elif gap and status != "literature-input":
            problems.append(f"{prefix}: exact claim cannot record a coverage gap")

        identity = entry.get("object_identity")
        if not isinstance(identity, str) or not identity:
            problems.append(f"{prefix}: `object_identity` must be nonempty")

        lean = entry.get("lean")
        if not isinstance(lean, list):
            problems.append(f"{prefix}: `lean` must be a list")
            lean = []
        if not lean and status == "exact":
            problems.append(f"{prefix}: exact claim must list a Lean declaration")
        if lean and status != "exact":
            problems.append(f"{prefix}: {status} claim cannot list a Lean declaration")

        declared_refs: set[tuple[str, str, str]] = set()
        for position, ref in enumerate(lean, 1):
            rprefix = f"{prefix}: lean[{position}]"
            if not isinstance(ref, dict):
                problems.append(f"{rprefix} is not an object")
                continue
            role = ref.get("role")
            module = ref.get("module")
            declaration = ref.get("declaration")
            covers = ref.get("covers")
            if role not in ROLES:
                problems.append(f"{rprefix}: invalid role `{role}`")
            if not isinstance(module, str) or not module:
                problems.append(f"{rprefix}: module must be nonempty")
                continue
            if not isinstance(declaration, str) or not declaration:
                problems.append(f"{rprefix}: declaration must be nonempty")
                continue
            if not isinstance(covers, str) or not covers:
                problems.append(f"{rprefix}: `covers` must be nonempty")
            key = (str(role), module, declaration)
            if key in declared_refs:
                problems.append(f"{rprefix}: duplicate Lean mapping")
            declared_refs.add(key)
            expected = _module_path(repo, module)
            actual = index.get(_full_name(declaration))
            if not expected.is_file():
                problems.append(f"{rprefix}: no module GroupApproximation/{module}.lean")
            if actual is None:
                problems.append(f"{rprefix}: missing declaration {_full_name(declaration)}")
            elif actual.resolve() != expected.resolve():
                problems.append(
                    f"{rprefix}: {_full_name(declaration)} is in "
                    f"{actual.relative_to(repo)}, not GroupApproximation/{module}.lean"
                )

        for badge in claim.badges:
            if badge not in declared_refs:
                role, module, declaration = badge
                problems.append(
                    f"{prefix}: TeX badge \\lean{role}{{{module}}}{{{declaration}}} "
                    "is absent from the claim manifest"
                )

        roles = {ref.get("role") for ref in lean if isinstance(ref, dict)}
        if "exact" not in roles and status == "exact":
            problems.append(f"{prefix}: exact status requires an exact Lean mapping")
        if entry.get("extra_assumptions"):
            problems.append(f"{prefix}: exact status cannot retain extra formal assumptions")

    return problems


def self_test() -> int:
    with tempfile.TemporaryDirectory() as directory:
        repo = Path(directory)
        module = repo / "GroupApproximation" / "Demo"
        module.mkdir(parents=True)
        (module / "Exact.lean").write_text(
            "namespace GroupApproximation\ntheorem demo_exact : True := by trivial\n"
            "end GroupApproximation\n", encoding="utf-8")
        tex = repo / "paper.tex"
        tex.write_text(
            "\\begin{theorem}[Demo]\\label{thm:demo}\nTrue.\n"
            "\\leanverified{Demo/Exact}{GroupApproximation.demo_exact}\n"
            "\\end{theorem}\n", encoding="utf-8")
        claim = read_printed_claims(tex)[0]
        manifest = repo / "claims.json"
        base = {
            "schema_version": 1,
            "claims": [{
                "id": "thm:demo", "environment": "theorem", "title": "Demo",
                "statement_sha256": claim.statement_sha256, "status": "exact",
                "object_identity": "The same proposition True.",
                "dependencies": [], "extra_assumptions": [], "external_inputs": [],
                "coverage_gap": "",
                "lean": [{"role": "exact", "module": "Demo/Exact",
                          "declaration": "GroupApproximation.demo_exact",
                          "covers": "the complete printed proposition"}],
            }],
        }
        manifest.write_text(json.dumps(base), encoding="utf-8")
        if problems := validate(repo, tex, manifest):
            print(f"self-test rejected valid manifest: {problems}", file=sys.stderr)
            return 1
        bad = json.loads(json.dumps(base))
        bad["claims"][0]["statement_sha256"] = "0" * 64
        manifest.write_text(json.dumps(bad), encoding="utf-8")
        if not any("printed statement changed" in p for p in validate(repo, tex, manifest)):
            print("self-test missed statement drift", file=sys.stderr)
            return 1
        bad = json.loads(json.dumps(base))
        bad["claims"][0]["lean"] = []
        manifest.write_text(json.dumps(bad), encoding="utf-8")
        if not any("must list a Lean declaration" in p for p in validate(repo, tex, manifest)):
            print("self-test missed empty exact mapping", file=sys.stderr)
            return 1
        bad = json.loads(json.dumps(base))
        bad["claims"][0]["extra_assumptions"] = ["a hidden premise"]
        manifest.write_text(json.dumps(bad), encoding="utf-8")
        if not any("cannot retain extra" in p for p in validate(repo, tex, manifest)):
            print("self-test accepted a hidden premise on an exact claim", file=sys.stderr)
            return 1
        former_statuses = (
            "equivalent", "partial", "supporting", "conditional",
            "different-witness", "paper-only",
        )
        for forbidden_status in former_statuses:
            bad = json.loads(json.dumps(base))
            bad["claims"][0]["status"] = forbidden_status
            manifest.write_text(json.dumps(bad), encoding="utf-8")
            expected = f"invalid status `{forbidden_status}`"
            if not any(expected in p for p in validate(repo, tex, manifest)):
                print(f"self-test accepted status {forbidden_status}", file=sys.stderr)
                return 1
        former_roles = (
            "equivalent", "partial", "supporting", "conditional",
            "different-witness",
        )
        for forbidden_role in former_roles:
            bad = json.loads(json.dumps(base))
            bad["claims"][0]["lean"][0]["role"] = forbidden_role
            manifest.write_text(json.dumps(bad), encoding="utf-8")
            expected = f"invalid role `{forbidden_role}`"
            if not any(expected in p for p in validate(repo, tex, manifest)):
                print(f"self-test accepted role {forbidden_role}", file=sys.stderr)
                return 1
        former_badges = (
            "equivalent", "partial", "supporting", "conditional",
            "differentwitness",
        )
        for forbidden_badge in former_badges:
            tex.write_text(
                "\\begin{theorem}[Demo]\\label{thm:demo}\nTrue.\n"
                f"\\lean{forbidden_badge}{{Demo/Exact}}"
                "{GroupApproximation.demo_exact}\n"
                "\\end{theorem}\n", encoding="utf-8")
            bad_claim = read_printed_claims(tex)[0]
            bad = json.loads(json.dumps(base))
            bad["claims"][0]["statement_sha256"] = bad_claim.statement_sha256
            manifest.write_text(json.dumps(bad), encoding="utf-8")
            if not any("at least one \\leanverified badge" in p
                       for p in validate(repo, tex, manifest)):
                print(f"self-test accepted badge {forbidden_badge}", file=sys.stderr)
                return 1
        for forbidden_badge in former_badges:
            tex.write_text(
                "\\begin{theorem}[Demo]\\label{thm:demo}\nTrue.\n"
                "\\leanverified{Demo/Exact}{GroupApproximation.demo_exact}\n"
                f"\\lean{forbidden_badge}{{Demo/Exact}}"
                "{GroupApproximation.demo_exact}\n"
                "\\end{theorem}\n", encoding="utf-8")
            manifest.write_text(json.dumps(base), encoding="utf-8")
            if not any("forbidden nonexact manuscript badge" in p
                       for p in validate(repo, tex, manifest)):
                print(
                    "self-test accepted coexisting badge "
                    f"{forbidden_badge}", file=sys.stderr)
                return 1
        for forbidden_badge in former_badges:
            for separator in (" ", "\n  "):
                tex.write_text(
                    "\\begin{theorem}[Demo]\\label{thm:demo}\nTrue.\n"
                    "\\leanverified{Demo/Exact}{GroupApproximation.demo_exact}\n"
                    f"\\lean{forbidden_badge}{separator}{{Demo/Exact}}"
                    f"{separator}{{GroupApproximation.demo_exact}}\n"
                    "\\end{theorem}\n", encoding="utf-8")
                manifest.write_text(json.dumps(base), encoding="utf-8")
                if not any("forbidden nonexact manuscript badge" in p
                           for p in validate(repo, tex, manifest)):
                    print(
                        "self-test accepted whitespace-separated badge "
                        f"{forbidden_badge!r} with {separator!r}",
                        file=sys.stderr)
                    return 1
        bad = json.loads(json.dumps(base))
        bad["claims"] = []
        manifest.write_text(json.dumps(bad), encoding="utf-8")
        if not any("has no manifest entry" in p for p in validate(repo, tex, manifest)):
            print("self-test missed an uncovered numbered claim", file=sys.stderr)
            return 1
    print("non-MF numbered-claim manifest: self-test passed")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, default=REPO)
    parser.add_argument("--tex", type=Path, default=DEFAULT_TEX)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument(
        "--dependency-manifest", type=Path, action="append", default=[],
        help="allow dependencies on claims printed in a companion edition")
    parser.add_argument("--signature-roster", type=Path,
                        help="require every manifest declaration in this signature roster")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        return self_test()
    dependency_manifests = tuple(
        path if path.is_absolute() else args.repo / path
        for path in args.dependency_manifest)
    problems = validate(
        args.repo, args.tex, args.manifest, dependency_manifests)
    if args.signature_roster is not None:
        roster_path = (args.signature_roster if args.signature_roster.is_absolute()
                       else args.repo / args.signature_roster)
        try:
            roster = {line.strip() for line in
                      roster_path.read_text(encoding="utf-8").splitlines()
                      if line.strip()}
            for declaration in sorted(manifest_declarations(args.manifest) - roster):
                problems.append(
                    f"numbered-claim declaration `{declaration}` is absent from "
                    f"signature roster {roster_path.relative_to(args.repo)}"
                )
        except OSError as error:
            problems.append(f"cannot read signature roster {roster_path}: {error}")
    if problems:
        for problem in problems:
            print(f"::error:: {problem}")
        return 1
    count = len(read_printed_claims(args.tex))
    print(f"non-MF numbered-claim manifest: {count}/{count} claims validated")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
