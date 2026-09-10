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
import posixpath
import re
import tarfile
import time


def read_archive(path):
    raw = path.read_bytes()
    with tarfile.open(fileobj=io.BytesIO(raw)) as archive:
        files = {m.name: archive.extractfile(m).read()
                 for m in archive.getmembers()
                 if m.isfile() and not any(p.startswith('._') for p in Path(m.name).parts)}
    return files, hashlib.sha256(raw).hexdigest()


def integration_view(graph):
    """Separate genuine premise reachability from complete catalog navigation."""
    ids = {node for node in graph.nodes if node.startswith('fpbs-')}
    goals = ('fpbs-benjamini-schramm-universal', 'fpbs-fixed-price-universal')

    def reachable(goal, live):
        seen, pending = set(), [goal]
        while pending:
            node = pending.pop()
            if node in seen:
                continue
            seen.add(node)
            value = graph.nodes[node]
            if value.kind == 'claim':
                pending.extend(r for r in graph.routes_into.get(node, [])
                               if not live or graph.nodes[r].status != 'INVALIDATED')
            else:
                pending.extend(value.meta.get('requires', []))
        return seen & ids

    all_paths = {g: reachable(g, False) for g in goals}
    live_paths = {g: reachable(g, True) for g in goals}
    live_union = set().union(*live_paths.values())
    lines = [
        '# Fixed Price and Benjamini–Schramm: complete Cairn navigation', '',
        'Generated from the captured graph by `scripts/validate_critical_cluster_stability.py`.',
        'Both universal goals remain OPEN. ESTABLISHED records Cairn dependency closure;',
        'it does not certify mathematical correctness or a Lean proof.', '',
        'Every fpbs claim and route is listed below. Catalog links make supporting work',
        'discoverable without pretending that it is a proof premise. A live goal path',
        'uses declared claim-to-route and route-to-requirement edges and excludes',
        'INVALIDATED routes; it can still contain OPEN premises.', '',
        '| Scope | Nodes |', '| --- | ---: |',
        f'| Complete catalog | {len(ids)} |',
        f'| Live proof paths from either goal | {len(live_union)} |',
        f'| All declared paths, including invalidated routes | {len(set().union(*all_paths.values()))} |',
        f'| Supporting catalog outside live goal paths | {len(ids-live_union)} |', '',
        'Direct percolation: [new-result scope checks](docs/direct-bs-new-results.md)',
        'identify the small-cell obstruction to the weighted profile criterion and',
        'the distinct-infinite-cluster term introduced by exterior wiring.', '',
        'New conditional work: [sparse base surgery](docs/sparse-base-surgery.md).',
        'It transfers coupled separators to the base action and rounds certificates',
        'already supported in a sufficiently sparse base region. Producing that support',
        'at source-optimal cost and handling nonexact groups remain unresolved.', '',
        '| Claim or route | Kind | Cairn status | Live goal path | Declared premises or routes |',
        '| --- | --- | --- | --- | --- |',
    ]

    def link(node):
        return f'[{node}](../../{node}.md)'

    for node in sorted(ids):
        value = graph.nodes[node]
        paths = ', '.join(label for g, label in zip(goals, ('BS', 'FP'))
                          if node in live_paths[g]) or 'supporting catalog'
        adjacent = (graph.routes_into.get(node, []) if value.kind == 'claim'
                    else value.meta.get('requires', []))
        references = ', '.join(link(n) for n in sorted(adjacent)) or 'none'
        lines.append(f'| {link(node)} | {value.kind} | {value.status} | {paths} | {references} |')
    return '\n'.join(lines)+'\n', {
        'catalog_nodes': len(ids),
        'catalog_ids': sorted(ids),
        'live_proof_reachable': {g: sorted(v) for g, v in live_paths.items()},
        'all_declared_reachable': {g: sorted(v) for g, v in all_paths.items()},
        'outside_live_goal_paths': sorted(ids-live_union),
        'meaning': 'Catalog coverage is navigation, not additional proof dependency or mathematical verification.',
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--kernel', type=Path, required=True,
                        help='Explicit captured Cairn kernel; leaves shared warm tools untouched.')
    parser.add_argument('--baseline', type=Path, required=True)
    parser.add_argument('--overlay', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--write-navigation', action='store_true',
                        help='Generate navigation only; rebuild the overlay and validate separately.')
    parser.add_argument('--source-rename', nargs=2, action='append', default=[],
                        metavar=('OLD', 'NEW'),
                        help='Explicit source rename omitted from the overlay; verify unchanged text except id.')
    args = parser.parse_args()
    start = time.monotonic()
    tool_path = args.kernel
    spec = importlib.util.spec_from_file_location('pinned_cairn', tool_path)
    cairn = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(cairn)
    baseline, baseline_hash = read_archive(args.baseline)
    overlay, overlay_hash = read_archive(args.overlay)
    current = baseline | overlay
    for old, new in args.source_rename:
        assert old in baseline and old not in overlay and new in overlay
        assert not (args.repo/old).exists() and (args.repo/new).is_file()
        old_text = baseline[old].decode('utf-8')
        expected_text = old_text.replace('id: '+Path(old).stem+'\n',
                                         'id: '+Path(new).stem+'\n', 1)
        assert overlay[new].decode('utf-8') == expected_text
        del current[old]

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
    navigation, integration = integration_view(after)
    navigation_path = 'research/artifacts/fpbs/navigation.md'
    if args.write_navigation:
        (args.repo/navigation_path).write_text(navigation)
        print(json.dumps({'status': 'navigation_generated_not_validated',
                          'catalog_nodes': integration['catalog_nodes']}))
        return
    navigation_matches = (current.get(navigation_path) == navigation.encode('utf-8')
                          and (args.repo/navigation_path).read_text() == navigation)
    integration['navigation_matches_compiled_graph'] = navigation_matches
    checked_documents = (
        navigation_path,
        'research/artifacts/fpbs/docs/sparse-base-surgery.md',
        'research/artifacts/fpbs/docs/direct-bs-new-results.md',
        'research/artifacts/boone-higman-full-cantor-clopen-action-2026-09-08.md',
    )
    missing_links = []
    for path in checked_documents:
        for target in re.findall(r'\]\(([^)]+)\)', current[path].decode('utf-8')):
            if '://' in target or target.startswith('#'):
                continue
            resolved = posixpath.normpath(posixpath.join(posixpath.dirname(path),
                                                        target.split('#', 1)[0]))
            if resolved not in current:
                missing_links.append([path, target, resolved])
    integration['checked_document_links'] = list(checked_documents)
    integration['missing_document_links'] = missing_links
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
        'fpbs-cycle-retraction-contractive-transport': 'ESTABLISHED',
        'fpbs-finite-fiber-cost-bound': 'ESTABLISHED',
        'fpbs-infinite-contact-zero-relative-cost': 'ESTABLISHED',
        'fpbs-cost-subgraph-rank-obstruction': 'ESTABLISHED',
        'fpbs-pulled-back-graphing-isoperimetry': 'ESTABLISHED',
        'fpbs-cluster-contact-merger-balance': 'ESTABLISHED',
        'fpbs-contact-dispersion-sign-obstruction': 'ESTABLISHED',
        'fpbs-critical-quotient-small-profile-obstruction': 'ESTABLISHED',
        'fpbs-sparse-fiid-approximate-hyperfiniteness': 'ESTABLISHED',
        'fpbs-local-equivalence-separator-rounding': 'ESTABLISHED',
        'fpbs-sparse-base-connected-cycle-rounding': 'ESTABLISHED',
        'fpbs-measurable-matroid-approximate-exchange': 'ESTABLISHED',
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
    transport_chain = cairn.why_chain(task_graph, 'fpbs-cycle-retraction-contractive-transport')
    finite_fiber_chain = cairn.why_chain(task_graph, 'fpbs-finite-fiber-cost-bound')
    contact_chain = cairn.why_chain(task_graph, 'fpbs-infinite-contact-zero-relative-cost')
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
        and retraction_chain[-1][2] == 'fpbs-relative-cycle-retraction-rounding'
        and transport_chain
        and transport_chain[0][0] == 'fpbs-fixed-price-universal'
        and transport_chain[-1][2] == 'fpbs-cycle-retraction-contractive-transport'
        and finite_fiber_chain
        and finite_fiber_chain[0][0] == 'fpbs-fixed-price-universal'
        and finite_fiber_chain[-1][2] == 'fpbs-finite-fiber-cost-bound'
        and contact_chain
        and contact_chain[0][0] == 'fpbs-fixed-price-universal'
        and contact_chain[-1][2] == 'fpbs-infinite-contact-zero-relative-cost')
    new_errors = [finding for finding in errors if finding not in baseline_errors]
    passed = (not any(severity == 'error' for severity, _, _ in task_errors)
              and not new_errors and not duplicates and not removed
              and statuses == expected and not unexpected_new_open
              and wired and price_wired and navigation_matches and not missing_links
              and not any(severity == 'error' for severity, _, _ in errors))
    report = {
        'status': 'passed_task_graph' if passed else 'failed',
        'execution': 'MSI acn112, shared project storage; archive-fed pinned Cairn core; no local code execution.',
        'scope': 'Full captured graph comparison plus dependency-closed fpbs graph validation with unchanged Cairn parser, linter, compiler and changed-claim duplicate checker. Reports original baseline findings and remaining findings separately. Verifies complete navigation against compiled graph without adding proof premises. Raw CLI checks exceeded their time limits during NFS source loading. No Lean proof verification or resolution of Benjamini-Schramm or Fixed Price.',
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
        'source_renames': args.source_rename,
        'integration': integration,
        'allowed_new_open_claims': sorted(allowed_new_open),
        'unexpected_new_open_claims': unexpected_new_open,
        'benjamini_schramm_frontier': goal_view[0],
        'optimistic_search_goal_chain': search_chain,
        'fixed_price_frontier': price_view[0],
        'correlated_reuse_goal_chain': reuse_chain,
        'cycle_compactness_goal_chain': cycle_chain,
        'block_localization_goal_chain': block_chain,
        'cycle_retraction_goal_chain': retraction_chain,
        'contractive_transport_goal_chain': transport_chain,
        'finite_fiber_goal_chain': finite_fiber_chain,
        'infinite_contact_goal_chain': contact_chain,
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
                                   'baseline_findings', 'integration')}, indent=2))
    raise SystemExit(0 if passed else 1)


if __name__ == '__main__':
    main()
