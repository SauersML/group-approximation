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
    parser.add_argument('--baseline', type=Path, required=True)
    parser.add_argument('--overlay', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    start = time.monotonic()
    tool_path = args.repo / 'tools/cairn.py'
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
    expected = {
        'fpbs-critical-cluster-stability-modulus': 'ESTABLISHED',
        'fpbs-finite-spectrum-total-variation-continuity': 'ESTABLISHED',
        'fpbs-uniqueness-spectrum-critical-remainder': 'ESTABLISHED',
        'fpbs-integrated-sensitivity-universal': 'OPEN',
        'fpbs-benjamini-schramm-universal': 'OPEN',
        'fpbs-fixed-price-universal': 'OPEN',
    }
    statuses = {node: after.nodes[node].status for node in expected}
    removed = sorted(set(before.nodes)-set(after.nodes))
    changes = {node: [before.nodes[node].status if node in before.nodes else None,
                      after.nodes[node].status]
               for node in after.nodes
               if node not in before.nodes or before.nodes[node].status != after.nodes[node].status}
    new_open = [node for node in after.claims
                if node not in before.nodes and after.claims[node].status == 'OPEN']
    passed = (not any(severity == 'error' for severity, _, _ in errors)
              and not duplicates and not removed and statuses == expected and not new_open)
    report = {
        'status': 'passed' if passed else 'failed',
        'execution': 'MSI acn112, shared project storage; archive-fed pinned Cairn core; no local code execution.',
        'scope': 'Full captured research graph; unchanged Cairn parser, linter, dependency compiler and changed-claim duplicate checker. Raw CLI checks exceeded their time limits during NFS source loading. No Lean proof verification or resolution of Benjamini-Schramm.',
        'cairn_sha256': hashlib.sha256(tool_path.read_bytes()).hexdigest(),
        'baseline_archive_sha256': baseline_hash,
        'overlay_archive_sha256': overlay_hash,
        'claims': len(after.claims), 'routes': len(after.routes),
        'baseline_findings': baseline_errors,
        'findings': errors, 'duplicate_findings': duplicates,
        'removed_nodes': removed, 'new_open_claims': new_open,
        'state_changes': changes, 'selected_statuses': statuses,
        'overlay_source_sha256': {p: hashlib.sha256(data).hexdigest()
                                  for p, data in sorted(overlay.items())},
        'elapsed_seconds': round(time.monotonic()-start, 3),
    }
    args.output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items()
                      if k not in ('overlay_source_sha256', 'baseline_findings')}, indent=2))
    raise SystemExit(0 if passed else 1)


if __name__ == '__main__':
    main()
