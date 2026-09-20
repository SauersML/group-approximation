#!/usr/bin/env python3
"""Validate the live QPCP proof boundary, links, and exact replay receipts.

Uses Cairn's own parser, linter, status compiler and duplicate checker. Global
errors are reported separately; failures in the selected proof closure fail
this check. This is graph/replay validation, not formal proof verification.
"""
from hashlib import sha256
import json
from pathlib import Path
import re
import subprocess
import sys

REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO / 'tools'))
import cairn

NEW_CLAIMS = (
    'shared-records-obey-complementary-check-uncertainty',
    'coherent-records-have-exact-phase-energy',
    'distance-code-local-tests-are-label-diagonal',
    'distance-code-leakage-bounds-phase-energy',
    'diagonal-penalty-transitions-have-distance-order',
    'one-copy-choi-tests-cannot-enforce-channel-legality',
)
ROOT = 'quantum-pcp-constant-gap-local-hamiltonian'
REDUCER = 'global-walk-reducer-has-net-energy-gain'
OPEN = (ROOT, REDUCER, 'locality-reduction-with-amplifier-independent-loss',
        'qpcp-from-global-walk-reduction', 'qpcp-by-dinur-iteration')
ESTABLISHED = NEW_CLAIMS + (
    'global-walk-linearly-amplifies-hamiltonian-energy',
    'factorwise-complete-composition-returns-the-input-energy',
    'regular-graph-parity-has-uniform-single-defects',
    'correctable-data-tests-are-logically-blind',
    'tracial-internality-does-not-supply-local-witness-control',
    'gap-and-floor-do-not-force-compatible-syndrome-effects',
    'combinatorial-gap-and-rounder-give-energy-gap',
)
ARTIFACTS = REPO / 'research/artifacts'
RECEIPT = ARTIFACTS / 'qpcp-full-target-validation-2026-09-20.json'


def proof_closure(graph, seeds):
    """Include incoming proof routes, premises, refuters and invalidators."""
    scope = set(seeds)
    while True:
        before = set(scope)
        for nid in before:
            node = graph.nodes[nid]
            if node.kind == 'route':
                scope.add(node.meta['target'])
                scope.update(node.get_list('requires'))
            else:
                scope.update(graph.routes_into.get(nid, ()))
                scope.update(node.get_list('refuted_by'))
        for nid, node in graph.claims.items():
            if scope.intersection(node.get_list('invalidates')):
                scope.add(nid)
        if scope == before:
            return scope


def main():
    graph, diagnostics = cairn.compile_graph(
        research_dir=str(REPO / 'research'), repo=str(REPO), use_cache=False)
    expected = {**dict.fromkeys(OPEN, 'OPEN'), **dict.fromkeys(ESTABLISHED, 'ESTABLISHED')}
    missing = sorted(set(expected) - graph.nodes.keys())
    assert not missing, missing
    scope = proof_closure(graph, expected)
    scope_paths = {graph.nodes[nid].relpath for nid in scope}
    errors = [entry for entry in diagnostics if entry[0] == 'error']
    scope_errors, outside_errors = [], []
    for entry in errors:
        path = entry[2].split(':', 1)[0]
        relevant = path in scope_paths or not path.startswith('research/')
        # A malformed route omitted by the loader must not disappear from
        # this audit if its declared target or prerequisites are in scope.
        if not relevant and (REPO / path).is_file():
            text = (REPO / path).read_text()
            frontmatter = text.split('---', 2)[1] if text.startswith('---') else text
            relevant = any(re.search(r'(?<![a-z0-9-])' + re.escape(nid) + r'(?![a-z0-9-])',
                                     frontmatter) for nid in scope)
        (scope_errors if relevant else outside_errors).append(entry)
    assert not scope_errors, scope_errors
    observed = {nid: graph.nodes[nid].status for nid in expected}
    assert observed == expected, (observed, expected)
    remaining = {}
    for rid, prerequisite in (('qpcp-from-global-walk-reduction', REDUCER),
                              ('qpcp-by-dinur-iteration', OPEN[2])):
        remaining[rid] = [nid for nid in graph.route_requires[rid]
                          if graph.nodes[nid].status != 'ESTABLISHED']
        assert remaining[rid] == [prerequisite], remaining
    for nid in NEW_CLAIMS:
        route = graph.nodes[nid + '-proof']
        wanted = ['distance-code-local-tests-are-label-diagonal'] if 'leakage' in nid else []
        assert route.meta['target'] == nid
        assert route.get_list('requires') == wanted
        assert route.status == 'COMPLETE', (route.id, route.status)
        # No scoped limitation is declared a refutation of QPCP or reducer.
        assert not graph.nodes[nid].get_list('invalidates')
        for target in (ROOT, REDUCER):
            assert nid not in graph.nodes[target].get_list('refuted_by')
            assert f'[[{nid}]]' in graph.nodes[target].body
    duplicates = cairn.duplicate_findings(graph, only_ids=set(NEW_CLAIMS))
    assert not duplicates, duplicates

    paths = [REPO / graph.nodes[nid].relpath for nid in
             (*NEW_CLAIMS, *(nid + '-proof' for nid in NEW_CLAIMS), ROOT, REDUCER,
              'correctable-data-tests-are-logically-blind',
              'tracial-internality-does-not-supply-local-witness-control')]
    paths += [ARTIFACTS / name for name in (
        'qpcp-full-target-continuation-2026-09-20.md',
        'qpcp-integration-ledger-2026-09-20.md',
        'qpcp-strengthened-amplification-2026-09-20.md')]
    checked_links = 0
    for path in paths:
        text = path.read_text()
        for target in re.findall(r'\[\[([a-z0-9-]+)\]\]', text):
            assert target in graph.nodes, (path, target)
            checked_links += 1
        for link in re.findall(r'\[[^\]]+\]\(([^)]+)\)', text):
            if '://' in link or link.startswith('#'):
                continue
            linked = (path.parent / link.split('#', 1)[0]).resolve()
            # This receipt is the output of this command, checked below by
            # callers; no pre-existing placeholder receipt is required.
            assert linked == RECEIPT or linked.is_file(), (path, link)
            checked_links += 1
    replay_files = {}
    for stem, receipt in (
        ('global-walk-2026-09-11', 'qpcp-global-walk-replay-2026-09-11.json'),
        ('strengthened-amplification-2026-09-20', 'qpcp-strengthened-amplification-replay-2026-09-20.json'),
        ('full-target-continuation-2026-09-20', 'qpcp-full-target-continuation-replay-2026-09-20.json'),
    ):
        script = ARTIFACTS / ('check-qpcp-' + stem + '.py')
        run = subprocess.run([sys.executable, str(script)], check=True, capture_output=True, text=True)
        actual = json.loads(run.stdout)
        saved = json.loads((ARTIFACTS / receipt).read_text())
        assert actual == saved, f'Replay receipt differs: {receipt}'
        replay_files[receipt] = {
            'script_sha256': sha256(script.read_bytes()).hexdigest(),
            'receipt_sha256': sha256((ARTIFACTS / receipt).read_bytes()).hexdigest(),
            'matches_fresh_execution': True,
        }
    output = {
        'scope': 'Live QPCP proof dependency closure, six continuation claims, links, and three exact replay receipts; unrelated global errors are reported, not certified.',
        'full_graph_node_count': len(graph.nodes),
        'proof_closure_node_count': len(scope),
        'proof_closure_ids': sorted(scope),
        'scope_errors': scope_errors,
        'global_graph_valid': not errors,
        'outside_scope_errors': outside_errors,
        'duplicate_findings': duplicates,
        'expected_statuses': observed,
        'iteration_route_remaining_prerequisites': remaining,
        'local_links_checked': checked_links,
        'replays': replay_files,
        'scope_checks_passed': True,
        'proof_scope': 'Written proofs support universal claims; finite regressions and graph closure are not formal verification or a QPCP reduction.',
    }
    print(json.dumps(output, indent=2))


if __name__ == '__main__':
    main()
