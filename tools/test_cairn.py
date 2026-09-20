#!/usr/bin/env python3
"""Regression tests for exact, in-memory Cairn HEAD baselines.

Run with Python 3.12 on the authorized compute host. Temporary repositories
live beneath this project's .cairn directory, never a RAM-backed temp path.
"""

import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest import mock

import cairn


class HeadBaselineTests(unittest.TestCase):
    def setUp(self):
        disk_state = Path(__file__).resolve().parents[1] / ".cairn"
        disk_state.mkdir(exist_ok=True)
        self.temp = tempfile.TemporaryDirectory(prefix="test-head-", dir=disk_state)
        self.addCleanup(self.temp.cleanup)
        self.repo = Path(self.temp.name)
        self.research = self.repo / "research"
        self.research.mkdir()
        self.git("init", "-q", "-b", "main")
        self.git("config", "user.name", "Cairn fixture")
        self.git("config", "user.email", "cairn-fixture@example.invalid")
        self.patch = mock.patch.multiple(
            cairn, REPO=str(self.repo), RESEARCH_DIR=str(self.research),
            STATE_DIR=str(self.repo / ".cairn"))
        self.patch.start()
        self.addCleanup(self.patch.stop)

    def git(self, *args):
        return subprocess.run(
            ["git", "-C", str(self.repo), *args], check=True,
            capture_output=True, text=True).stdout

    def claim(self, nid, body="Initial claim."):
        self.write(nid, f"---\nrg: 2\nid: {nid}\nkind: claim\n"
                        f"title: Fixture {nid}\nroot: true\n---\n{body}\n")

    def route(self, nid, target, requires=()):
        reqs = ", ".join(requires)
        self.write(nid, f"---\nrg: 2\nid: {nid}\nkind: route\n"
                        f"title: Prove {target}\ntarget: {target}\n"
                        f"requires: [{reqs}]\n---\nFixture derivation.\n")

    def write(self, nid, text):
        (self.research / (nid + ".md")).write_text(text, encoding="utf-8")

    def commit(self):
        self.git("add", "research")
        self.git("commit", "-q", "-m", "Fixture baseline")

    def current(self):
        return cairn.compile_graph(
            research_dir=str(self.research), repo=str(self.repo),
            use_cache=False)

    def test_unchanged_sources_are_reused_without_sharing_derived_state(self):
        self.claim("target-claim")
        self.commit()
        self.route("new-proof", "target-claim")
        current, errors = self.current()
        self.assertFalse(any(e[0] == "error" for e in errors))
        self.assertEqual(current.nodes["target-claim"].status, "ESTABLISHED")
        with mock.patch.object(cairn, "_cat_file_batch", wraps=cairn._cat_file_batch) as batch:
            previous = cairn.previous_graph(cairn.changed_research_files(), current)
        self.assertEqual(batch.call_args.args[1], [])
        self.assertEqual(previous.nodes["target-claim"].status, "OPEN")
        self.assertEqual(current.nodes["target-claim"].status, "ESTABLISHED")
        self.assertIsNot(previous.nodes["target-claim"], current.nodes["target-claim"])
        self.assertEqual(set(previous.nodes), {"target-claim"})
        self.assertFalse((self.repo / ".cairn").exists())

    def test_rename_reports_both_ids_and_restores_old_head_node_in_memory(self):
        self.claim("old-claim", "Long common fixture body. " * 40)
        self.claim("untouched-claim")
        self.commit()
        old = self.research / "old-claim.md"
        renamed = self.research / "renamed-claim.md"
        os.rename(old, renamed)
        renamed.write_text(renamed.read_text().replace("old-claim", "renamed-claim"))
        self.git("add", "research")
        changed = cairn.changed_research_files()
        self.assertEqual(changed, {"old-claim", "renamed-claim"})
        current, _ = self.current()
        previous = cairn.previous_graph(changed, current)
        self.assertEqual(set(previous.nodes), {"old-claim", "untouched-claim"})
        self.assertIn("renamed-claim", current.nodes)
        self.assertTrue(renamed.exists())
        self.assertFalse(old.exists())

    def test_policy_findings_do_not_disable_validated_source_reuse(self):
        self.claim("target-claim")
        self.commit()
        self.route("new-proof", "target-claim")
        current, errors = self.current()
        errors.append(("error", "duplicate", "Fixture policy-only finding."))
        self.assertTrue(any(e[0] == "error" for e in current.errors))
        self.assertFalse(any(e[0] == "error" for e in current.compile_errors))
        with mock.patch.object(cairn, "_cat_file_batch", wraps=cairn._cat_file_batch) as batch:
            previous = cairn.previous_graph(cairn.changed_research_files(), current)
        self.assertEqual(batch.call_args.args[1], [])
        self.assertEqual(set(previous.nodes), {"target-claim"})
        self.assertEqual(previous.nodes["target-claim"].status, "OPEN")
        self.assertEqual(current.nodes["target-claim"].status, "ESTABLISHED")
        self.assertFalse(any(e[0] == "error" for e in previous.compile_errors))

    def test_more_than_two_hundred_changes_keep_the_complete_baseline(self):
        for i in range(205):
            self.claim(f"claim-{i:03}")
        self.commit()
        for i in range(205):
            self.claim(f"claim-{i:03}", "Edited working claim.")
        current, _ = self.current()
        changed = cairn.changed_research_files()
        self.assertEqual(len(changed), 205)
        with mock.patch.object(cairn, "_cat_file_batch", wraps=cairn._cat_file_batch) as batch:
            previous = cairn.previous_graph(changed, current)
        self.assertIsNotNone(previous)
        self.assertEqual(len(previous.nodes), 205)
        self.assertTrue(all(n.body == "Initial claim." for n in previous.nodes.values()))
        self.assertEqual(batch.call_count, 1)
        self.assertEqual(len(batch.call_args.args[1]), 205)

    def test_deleted_route_and_untracked_replacement_have_correct_states(self):
        self.claim("target-claim")
        self.route("old-proof", "target-claim")
        self.commit()
        (self.research / "old-proof.md").unlink()
        self.claim("new-claim")
        current, _ = self.current()
        previous = cairn.previous_graph(cairn.changed_research_files(), current)
        self.assertEqual(previous.nodes["target-claim"].status, "ESTABLISHED")
        self.assertEqual(current.nodes["target-claim"].status, "OPEN")
        self.assertNotIn("new-claim", previous.nodes)
        self.assertFalse((self.research / "old-proof.md").exists())

    def test_baseline_keeps_document_and_reference_validation(self):
        self.claim("target-claim")
        self.route("bad-proof", "target-claim", ["missing-claim"])
        self.write("bad-node", "---\nrg: 2\nid: bad-node\nkind: invalid\n---\nBad.\n")
        self.write("malformed-node", "No frontmatter.\n")
        self.commit()
        _, expected = self.current()
        self.route("bad-proof", "target-claim")
        self.claim("bad-node")
        self.claim("malformed-node")
        current, errors = self.current()
        self.assertFalse(any(e[0] == "error" for e in errors))
        previous, actual = cairn.head_graph(current)
        self.assertEqual(sorted(actual), sorted(expected))
        self.assertNotIn("bad-node", previous.nodes)
        self.assertNotIn("malformed-node", previous.nodes)
        self.assertIn("missing-claim", previous.nodes["bad-proof"].get_list("requires"))

    def test_source_change_after_compile_does_not_reuse_stale_text(self):
        self.claim("target-claim")
        self.commit()
        self.claim("target-claim", "Intermediate source.")
        current, _ = self.current()
        # Restore via an ordinary write, never a git working-tree command.
        self.claim("target-claim")
        previous, _ = cairn.head_graph(current)
        self.assertEqual(previous.nodes["target-claim"].body, "Initial claim.")
        self.assertEqual(current.nodes["target-claim"].body, "Intermediate source.")

    def test_empty_head_and_unavailable_git_are_distinguished(self):
        self.claim("first-claim")
        current, _ = self.current()
        self.assertEqual(cairn.changed_research_files(), {"first-claim"})
        previous = cairn.previous_graph({"first-claim"}, current)
        self.assertEqual(previous.nodes, {})
        self.assertIsNone(cairn.previous_graph(None, current))
        self.assertIs(cairn.previous_graph(set(), current), current)

    def test_missing_head_blob_is_an_error_not_a_partial_baseline(self):
        self.claim("target-claim")
        self.commit()
        with mock.patch.object(cairn, "_cat_file_batch", return_value=iter(())):
            with self.assertRaisesRegex(RuntimeError, "incomplete Cairn baseline"):
                cairn.head_graph()

    def test_unresolved_proved_equivalence_is_not_a_dependency_warning(self):
        self.claim("left-claim")
        self.claim("right-claim")
        self.route("forward-route", "left-claim", ["right-claim"])
        self.route("reverse-route", "right-claim", ["left-claim"])
        graph, errors = self.current()
        self.assertEqual(graph.nodes["left-claim"].status, "OPEN")
        self.assertEqual(graph.nodes["right-claim"].status, "OPEN")
        self.assertFalse(any(rule == "cycle" for _, rule, _ in errors))

    def test_established_equivalence_keeps_its_explicit_dependency_edges(self):
        self.claim("left-claim")
        self.claim("right-claim")
        self.claim("side-claim")
        self.route("left-proof", "left-claim")
        self.route("right-proof", "right-claim")
        self.route("side-proof", "side-claim")
        self.route("forward-route", "left-claim", ["right-claim", "side-claim"])
        self.route("reverse-route", "right-claim", ["left-claim"])
        graph, errors = self.current()
        self.assertEqual(graph.nodes["forward-route"].blocked_on, [])
        self.assertEqual(graph.nodes["reverse-route"].blocked_on, [])
        self.assertFalse(any(rule == "cycle" for _, rule, _ in errors))

    def test_an_unproved_side_condition_does_not_certify_an_equivalence(self):
        self.claim("left-claim")
        self.claim("right-claim")
        self.claim("side-claim")
        self.route("left-proof", "left-claim")
        self.route("right-proof", "right-claim")
        self.route("forward-route", "left-claim", ["right-claim", "side-claim"])
        self.route("reverse-route", "right-claim", ["left-claim"])
        graph, errors = self.current()
        self.assertEqual(graph.nodes["side-claim"].status, "OPEN")
        self.assertEqual(graph.nodes["forward-route"].blocked_on, ["side-claim"])
        cycles = [message for _, rule, message in errors if rule == "cycle"]
        self.assertEqual(len(cycles), 1)
        self.assertIn("left-claim", cycles[0])
        self.assertIn("right-claim", cycles[0])

    def test_missing_requires_cannot_establish_target_or_consumers(self):
        self.claim("target-claim")
        self.claim("consumer-claim")
        self.claim("valid-claim")
        self.route("valid-proof", "valid-claim")
        self.route("consumer-proof", "consumer-claim", ["target-claim"])
        self.write("bad-proof", "---\nrg: 2\nid: bad-proof\nkind: route\n"
                   "title: Unfinished proof\ntarget: target-claim\nstatus: OPEN\n"
                   "---\nOutstanding proof obligations.\n")
        graph, errors = self.current()
        self.assertTrue(any(rule == "requires" for _, rule, _ in errors))
        self.assertTrue(any(rule == "unknown-key" for _, rule, _ in errors))
        self.assertEqual(graph.nodes["bad-proof"].status, "INVALIDATED")
        self.assertIn("schema-invalid route", graph.nodes["bad-proof"].status_reasons[0])
        self.assertEqual(graph.nodes["target-claim"].status, "OPEN")
        self.assertEqual(graph.nodes["consumer-claim"].status, "OPEN")
        self.assertEqual(graph.nodes["valid-claim"].status, "ESTABLISHED")
        self.assertNotIn("target-claim", graph.provenance)
        self.assertIn("target-claim", graph.frontier)

    def test_invalid_route_metadata_never_becomes_a_direct_proof(self):
        self.claim("target-claim")
        self.claim("known-claim")
        self.route("known-proof", "known-claim")
        base = ("---\nrg: 2\nid: bad-proof\nkind: route\ntitle: Proposed proof\n"
                "target: target-claim\nrequires: []\n---\nProof text.\n")
        cases = {
            "unknown premise": ("requires: []", "requires: [missing-claim]"),
            "mixed unknown premise": ("requires: []", "requires: [known-claim, missing-claim]"),
            "route premise": ("requires: []", "requires: [known-proof]"),
            "null premises": ("requires: []", "requires: null"),
            "scalar premises": ("requires: []", "requires: known-claim"),
            "integer premise": ("requires: []", "requires: [17]"),
            "duplicate premises": ("requires: []", "requires: [known-claim, known-claim]"),
            "self target premise": ("requires: []", "requires: [target-claim]"),
            "missing target": ("target: target-claim\n", ""),
            "unknown target": ("target: target-claim", "target: missing-claim"),
            "route target": ("target: target-claim", "target: known-proof"),
            "list target": ("target: target-claim", "target: [target-claim]"),
            "unknown key": ("requires: []", "requires: []\nstatus: OPEN"),
            "wrong schema": ("rg: 2", "rg: 1"),
            "missing title": ("title: Proposed proof\n", ""),
            "wrong title type": ("title: Proposed proof", "title: [bad, title]"),
            "missing artifact": ("requires: []", "requires: []\nartifacts: [missing.md]"),
        }
        for name, (old, new) in cases.items():
            with self.subTest(name=name):
                self.write("bad-proof", base.replace(old, new))
                graph, errors = self.current()
                self.assertTrue(any(sev == "error" for sev, _, _ in errors))
                self.assertEqual(graph.nodes["bad-proof"].status, "INVALIDATED")
                self.assertEqual(graph.nodes["target-claim"].status, "OPEN")
                self.assertEqual(graph.nodes["known-claim"].status, "ESTABLISHED")
                self.assertNotIn("target-claim", graph._solve({"known-claim"})[0])
                if name == "mixed unknown premise":
                    self.assertEqual(graph.route_requires["bad-proof"],
                                     ["known-claim", "missing-claim"])

    def test_raw_graph_and_unhashable_premises_fail_closed(self):
        self.claim("target-claim")
        self.route("bad-proof", "target-claim")
        nodes = cairn.load_nodes([], str(self.research), str(self.repo))
        nodes["bad-proof"].meta["requires"] = [{"not": "an id"}]
        errors = []
        cairn.lint_nodes(nodes, errors, str(self.repo))
        self.assertTrue(any(rule == "ref" for _, rule, _ in errors))
        # Even callers constructing Graph without lint must not admit a proof.
        graph = cairn.Graph(nodes, [], str(self.repo))
        self.assertEqual(graph.nodes["bad-proof"].status, "INVALIDATED")
        self.assertEqual(graph.nodes["target-claim"].status, "OPEN")

    def test_invalid_route_does_not_create_a_false_refutation_conflict(self):
        self.claim("target-claim")
        self.claim("refuter-claim")
        self.route("refuter-proof", "refuter-claim")
        target = self.research / "target-claim.md"
        target.write_text(target.read_text().replace(
            "root: true", "root: true\nrefuted_by: [refuter-claim]"))
        self.write("bad-proof", "---\nrg: 2\nid: bad-proof\nkind: route\n"
                   "title: Unfinished proof\ntarget: target-claim\n---\nPending.\n")
        graph, errors = self.current()
        self.assertEqual(graph.nodes["target-claim"].status, "REFUTED")
        self.assertFalse(any(rule == "contradiction" for _, rule, _ in errors))

    def test_head_baseline_preserves_schema_invalidation(self):
        self.claim("target-claim")
        self.write("bad-proof", "---\nrg: 2\nid: bad-proof\nkind: route\n"
                   "title: Unfinished proof\ntarget: target-claim\n---\nPending.\n")
        self.commit()
        self.route("bad-proof", "target-claim")
        current, _ = self.current()
        previous, errors = cairn.head_graph(current)
        self.assertEqual(current.nodes["target-claim"].status, "ESTABLISHED")
        self.assertEqual(previous.nodes["target-claim"].status, "OPEN")
        self.assertEqual(previous.nodes["bad-proof"].status, "INVALIDATED")
        self.assertTrue(any(rule == "requires" for _, rule, _ in errors))

    def test_cached_route_lint_errors_still_disable_derivation(self):
        self.claim("target-claim")
        self.route("bad-proof", "target-claim")
        route = self.research / "bad-proof.md"
        route.write_text(route.read_text().replace(
            "requires: []", "requires: []\nartifacts: [missing.md]"))
        current, errors = self.current()
        self.assertTrue(any(rule == "artifact" for _, rule, _ in errors))
        cache = self.repo / ".cairn"
        cache.mkdir(exist_ok=True)
        with mock.patch.object(cairn, "CACHE_DIR", str(cache)):
            cairn.write_node_cache(current)
            cached, cached_errors = cairn.read_graph_cache(
                str(self.research), str(self.repo))
        self.assertTrue(cached.cache_hit)
        self.assertEqual(cached.nodes["target-claim"].status, "OPEN")
        self.assertEqual(cached.nodes["bad-proof"].status, "INVALIDATED")
        self.assertEqual(cached_errors, errors)


if __name__ == "__main__":
    unittest.main(verbosity=2)
