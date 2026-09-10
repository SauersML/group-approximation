#!/usr/bin/env python3
"""Validate a full Cairn archive and overlay with the repository's pinned core.

This avoids sequential NFS reads; it does not replace Cairn's mathematical
dependency rules or claim to be a successful invocation of the timed-out CLI.
Run on MSI. Archives must be trusted source snapshots, not arbitrary uploads.
"""

import argparse
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import tarfile
import time


def read_archive(path):
    raw = path.read_bytes()
    with tarfile.open(fileobj=io.BytesIO(raw)) as archive:
        files = {m.name: archive.extractfile(m).read()
                 for m in archive.getmembers()
                 if m.isfile() and not any(p.startswith('._') for p in Path(m.name).parts)}
    return files, hashlib.sha256(raw).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--kernel', type=Path, required=True,
                        help='Explicit captured Cairn kernel; leaves shared warm tools untouched.')
    parser.add_argument('--baseline', type=Path, required=True)
    parser.add_argument('--overlay', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    start = time.monotonic()
    tool_path = args.kernel
    spec = importlib.util.spec_from_file_location('pinned_cairn', tool_path)
    cairn = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(cairn)
    baseline, baseline_hash = read_archive(args.baseline)
    overlay, overlay_hash = read_archive(args.overlay)
    current = baseline | overlay

    def node_sources(files):
        return {path: content for path, content in files.items()
                if Path(path).parent == Path('research')
                and path.endswith('.md') and Path(path).name not in cairn.NON_NODE_FILES}

    old_sources, new_sources = node_sources(baseline), node_sources(current)

    def compile_sources(sources):
        errors, nodes = [], {}
        for path, content in sorted(sources.items()):
            cairn.load_node_text(content.decode('utf-8'), str(args.repo/path),
                                 nodes, errors, str(args.repo))
        cairn.lint_nodes(nodes, errors, str(args.repo))
        graph = cairn.Graph(nodes, errors, str(args.repo))
        return graph, errors

    before, baseline_errors = compile_sources(old_sources)
    after, errors = compile_sources(new_sources)
    changed = {Path(p).stem for p in new_sources
               if old_sources.get(p) != new_sources[p]}
    duplicates = cairn.duplicate_findings(after, only_ids=changed)
    # Include every proof and explicit refutation/invalidator relevant to the
    # fpbs region, rather than dropping unrelated findings from a global check.
    cone = {node for node in after.nodes if node.startswith('fpbs-')}
    while True:
        expanded = set(cone)
        for node in cone:
            metadata = after.nodes[node].meta
            for key in ('requires', 'invalidates', 'refuted_by'):
                expanded.update(metadata.get(key, []))
            if metadata.get('target'):
                expanded.add(metadata['target'])
            expanded.update(metadata.get('distinct_from', {}))
        for node, value in after.nodes.items():
            if value.meta.get('target') in cone:
                expanded.add(node)
            if set(value.meta.get('invalidates', [])) & cone:
                expanded.add(node)
        if expanded == cone:
            break
        cone = expanded
    task_graph, task_errors = compile_sources({
        path: content for path, content in new_sources.items() if Path(path).stem in cone})
    expected = {
        'fpbs-critical-cluster-stability-modulus': 'ESTABLISHED',
        'fpbs-finite-spectrum-total-variation-continuity': 'ESTABLISHED',
        'fpbs-uniqueness-spectrum-critical-remainder': 'ESTABLISHED',
        'fpbs-integrated-sensitivity-universal': 'OPEN',
        'fpbs-benjamini-schramm-universal': 'OPEN',
        'fpbs-fixed-price-universal': 'OPEN',
        'fpbs-free-action-cost-at-least-bernoulli-cost': 'OPEN',
        'fpbs-correlated-reuse-flags-removable': 'OPEN',
        'fpbs-fixed-price-countable-from-finitely-generated': 'OPEN',
        'fpbs-bernoulli-cycle-tail-compactness': 'OPEN',
        'fpbs-graphing-cost-betti-cycle-dimension-identity': 'ESTABLISHED',
        'fpbs-relative-cycle-operator-descent': 'ESTABLISHED',
        'fpbs-relative-cycle-dpp-disconnects': 'ESTABLISHED',
        'fpbs-finite-block-forest-cost-normal-form': 'ESTABLISHED',
        'fpbs-relative-cycle-block-rounding-bound': 'ESTABLISHED',
        'fpbs-relative-cycle-retraction-rounding': 'ESTABLISHED',
        'fpbs-relative-cycle-block-localization': 'OPEN',
        'fpbs-reduced-circulation-tail-bounds-cost-excess': 'ESTABLISHED',
        'fpbs-optimistic-search-certified-growth': 'ESTABLISHED',
        'fpbs-optimistic-search-linear-wall-cost': 'ESTABLISHED',
        'fpbs-universal-optimistic-certificate-budget': 'OPEN',
    }
    statuses = {node: task_graph.nodes[node].status for node in expected}
    removed = sorted(set(before.nodes)-set(after.nodes))
    changes = {node: [before.nodes[node].status if node in before.nodes else None,
                      after.nodes[node].status]
               for node in after.nodes
               if node not in before.nodes or before.nodes[node].status != after.nodes[node].status}
    new_open = [node for node in after.claims
                if node not in before.nodes and after.claims[node].status == 'OPEN']
    # Named, explicitly unproved constructions are actual frontier premises.
    # Keep all goals OPEN and reject unexpected new unresolved claims.
    allowed_new_open = {'fpbs-universal-optimistic-certificate-budget',
                        'fpbs-bernoulli-cycle-tail-compactness',
                        'fpbs-relative-cycle-block-localization'}
    unexpected_new_open = sorted(set(new_open)-allowed_new_open)
    goal_view, _ = cairn.frontier_view(task_graph,
                                     only_goal='fpbs-benjamini-schramm-universal')
    goal_view[0]['necessary'] = sorted(goal_view[0]['necessary'])
    search_chain = cairn.why_chain(task_graph, 'fpbs-optimistic-search-certified-growth')
    wired = ('fpbs-universal-optimistic-certificate-budget' in goal_view[0]['holes']
             and search_chain
             and search_chain[0][0] == 'fpbs-benjamini-schramm-universal'
             and search_chain[-1][2] == 'fpbs-optimistic-search-certified-growth')
    price_view, _ = cairn.frontier_view(task_graph,
                                      only_goal='fpbs-fixed-price-universal')
    price_view[0]['necessary'] = sorted(price_view[0]['necessary'])
    reuse_chain = cairn.why_chain(task_graph, 'fpbs-correlated-reuse-flags-removable')
    cycle_chain = cairn.why_chain(task_graph, 'fpbs-bernoulli-cycle-tail-compactness')
    block_chain = cairn.why_chain(task_graph, 'fpbs-relative-cycle-block-localization')
    retraction_chain = cairn.why_chain(task_graph, 'fpbs-relative-cycle-retraction-rounding')
    price_wired = (
        {'fpbs-correlated-reuse-flags-removable',
         'fpbs-bernoulli-cycle-tail-compactness',
         'fpbs-relative-cycle-block-localization',
         'fpbs-fixed-price-countable-from-finitely-generated'}
        <= set(price_view[0]['holes'])
        and reuse_chain
        and reuse_chain[0][0] == 'fpbs-fixed-price-universal'
        and reuse_chain[-1][2] == 'fpbs-correlated-reuse-flags-removable'
        and cycle_chain
        and cycle_chain[0][0] == 'fpbs-fixed-price-universal'
        and cycle_chain[-1][2] == 'fpbs-bernoulli-cycle-tail-compactness'
        and block_chain
        and block_chain[0][0] == 'fpbs-fixed-price-universal'
        and block_chain[-1][2] == 'fpbs-relative-cycle-block-localization'
        and retraction_chain
        and retraction_chain[0][0] == 'fpbs-fixed-price-universal'
        and retraction_chain[-1][2] == 'fpbs-relative-cycle-retraction-rounding')
    new_errors = [finding for finding in errors if finding not in baseline_errors]
    passed = (not any(severity == 'error' for severity, _, _ in task_errors)
              and not new_errors and not duplicates and not removed
              and statuses == expected and not unexpected_new_open
              and wired and price_wired)
    report = {
        'status': 'passed_task_graph' if passed else 'failed',
        'execution': 'MSI acn112, shared project storage; archive-fed pinned Cairn core; no local code execution.',
        'scope': 'Full captured graph comparison plus dependency-closed fpbs graph validation with unchanged Cairn parser, linter, compiler and changed-claim duplicate checker. Global baseline errors are retained explicitly. Raw CLI checks exceeded their time limits during NFS source loading. No Lean proof verification or resolution of Benjamini-Schramm or Fixed Price.',
        'cairn_sha256': hashlib.sha256(tool_path.read_bytes()).hexdigest(),
        'cairn_asset_sha256': {
            name: hashlib.sha256((tool_path.parent/name).read_bytes()).hexdigest()
            for name in ('math_explainer.css', 'math_macros.js', 'math_explainer.js')},
        'baseline_archive_sha256': baseline_hash,
        'overlay_archive_sha256': overlay_hash,
        'claims': len(after.claims), 'routes': len(after.routes),
        'task_claims': len(task_graph.claims), 'task_routes': len(task_graph.routes),
        'task_findings': task_errors, 'new_findings': new_errors,
        'full_snapshot_clean': not any(f[0] == 'error' for f in errors),
        'baseline_findings': baseline_errors,
        'findings': errors, 'duplicate_findings': duplicates,
        'removed_nodes': removed, 'new_open_claims': new_open,
        'allowed_new_open_claims': sorted(allowed_new_open),
        'unexpected_new_open_claims': unexpected_new_open,
        'benjamini_schramm_frontier': goal_view[0],
        'optimistic_search_goal_chain': search_chain,
        'fixed_price_frontier': price_view[0],
        'correlated_reuse_goal_chain': reuse_chain,
        'cycle_compactness_goal_chain': cycle_chain,
        'block_localization_goal_chain': block_chain,
        'cycle_retraction_goal_chain': retraction_chain,
        'state_changes': changes, 'selected_statuses': statuses,
        'overlay_source_sha256': {p: hashlib.sha256(data).hexdigest()
                                  for p, data in sorted(overlay.items())},
        'task_source_sha256': {p: hashlib.sha256(data).hexdigest()
                              for p, data in sorted(new_sources.items())
                              if Path(p).stem in cone},
        'elapsed_seconds': round(time.monotonic()-start, 3),
    }
    args.output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items()
                      if k not in ('overlay_source_sha256', 'task_source_sha256',
                                   'baseline_findings')}, indent=2))
    raise SystemExit(0 if passed else 1)


if __name__ == '__main__':
    main()
