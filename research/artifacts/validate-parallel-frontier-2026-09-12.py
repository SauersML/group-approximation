#!/usr/bin/env python3
"""Compile a proposed source overlay against a pinned upstream tree on MSI.

Git objects are read into memory; no historical sources are restored into a
worktree. Artifact existence is checked against the same tree plus overlay.
This checks Cairn semantics and provenance, not the mathematics of proofs.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tarfile
import types


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--revision', required=True)
    parser.add_argument('--overlay', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    repo = args.repo.resolve()

    def git(*arguments, data=None):
        return subprocess.run(['git', '-C', str(repo), *arguments], input=data,
                              stdout=subprocess.PIPE, check=True).stdout

    revision = git('rev-parse', args.revision+'^{commit}').decode().strip()
    paths = set(git('ls-tree', '-r', '-z', '--name-only', revision).decode().split('\0')) - {''}
    source_paths = sorted(p for p in paths if Path(p).parent == Path('research')
                          and p.endswith('.md'))
    requests = source_paths + ['tools/cairn.py']
    batch = git('cat-file', '--batch', data=''.join(revision+':'+p+'\n' for p in requests).encode())
    blobs, offset = {}, 0
    for path in requests:
        end = batch.index(b'\n', offset)
        header = batch[offset:end].split()
        assert len(header) == 3 and header[1] == b'blob', (path, header)
        size = int(header[2])
        blobs[path] = batch[end+1:end+1+size]
        offset = end+size+2
    assert offset == len(batch)
    with tarfile.open(args.overlay, 'r:') as archive:
        overlay = {m.name: archive.extractfile(m).read() for m in archive
                   if m.isfile() and not any(part.startswith('._') for part in Path(m.name).parts)}
    assert all(not p.startswith('/') and '..' not in Path(p).parts for p in overlay)

    kernel = types.ModuleType('pinned_cairn')
    kernel.__file__ = str(repo/'tools/cairn.py')
    exec(compile(blobs['tools/cairn.py'], kernel.__file__, 'exec'), kernel.__dict__)
    kernel.REPO = str(repo)
    # Keep virtual artifact lookup local to this module; do not patch Python's os.
    kernel.os = types.SimpleNamespace(**vars(os))
    kernel.os.path = types.SimpleNamespace(**vars(os.path))

    def compile_sources(files, available):
        def exists(path):
            try:
                relative = str(Path(path).relative_to(repo))
            except ValueError:
                return os.path.exists(path)
            return relative in available

        kernel.os.path.exists = exists
        nodes, errors = {}, []
        for path, body in sorted(files.items()):
            if Path(path).parent != Path('research') or not path.endswith('.md'):
                continue
            if Path(path).name in kernel.NON_NODE_FILES:
                continue
            kernel.load_node_text(body.decode(), str(repo/path), nodes, errors, str(repo))
        kernel.lint_nodes(nodes, errors, str(repo))
        graph = kernel.Graph(nodes, errors, str(repo))
        return graph, errors

    before, old_errors = compile_sources(blobs, paths)
    after, errors = compile_sources(blobs | overlay, paths | set(overlay))
    changed = {Path(p).stem for p in overlay if Path(p).parent == Path('research')
               and p.endswith('.md') and blobs.get(p) != overlay[p]}
    duplicates = kernel.duplicate_findings(after, only_ids=changed)
    new_errors = sorted(set(tuple(e) for e in errors if e[0] == 'error')
                        - set(tuple(e) for e in old_errors if e[0] == 'error'))
    expected = {
        'fpbs-fixed-price-universal': 'OPEN',
        'fpbs-correlated-reuse-flags-removable': 'OPEN',
        'fpbs-binary-entropy-traffic-tail-bound': 'ESTABLISHED',
        'fpbs-benjamini-schramm-universal': 'OPEN',
        'fpbs-universal-subcritical-pivotal-growth-rate': 'OPEN',
        'fpbs-global-pivotal-tail-at-uniqueness': 'ESTABLISHED',
        'fpbs-pivotal-volume-defect-criterion': 'ESTABLISHED',
        'unique-games-conjecture': 'OPEN',
        'finite-density-moments-control-noisy-tails': 'ESTABLISHED',
        'finite-moment-pairing-2to1-hardness': 'OPEN',
    }
    states = {key: after.nodes[key].status if key in after.nodes else 'MISSING'
              for key in expected}
    parked = [key for key in changed if key in after.claims
              and key not in before.nodes and after.claims[key].status == 'OPEN'
              and kernel.missing_attempts(after.claims[key].body)]
    report = {
        'status': 'passed' if not (new_errors or duplicates or parked) and states == expected else 'failed',
        'scope': 'Pinned upstream tree plus exact overlay; graph validation, not mathematical proof verification',
        'revision': revision,
        'kernel_sha256': hashlib.sha256(blobs['tools/cairn.py']).hexdigest(),
        'overlay_sha256': hashlib.sha256(args.overlay.read_bytes()).hexdigest(),
        'files_sha256': {p: hashlib.sha256(b).hexdigest() for p, b in sorted(overlay.items())},
        'claims': len(after.claims), 'routes': len(after.routes),
        'baseline_errors': [e for e in old_errors if e[0] == 'error'],
        'candidate_errors': [e for e in errors if e[0] == 'error'],
        'introduced_errors': new_errors,
        'duplicate_candidates': duplicates,
        'new_open_claims_without_attempts': parked,
        'expected_states': expected, 'actual_states': states,
        'changed_ids': sorted(changed),
        'newly_established': sorted(after.established-before.established),
        'newly_refuted': sorted(after.refuted-before.refuted),
    }
    args.output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k: report[k] for k in ('status', 'revision', 'claims', 'routes',
                                          'introduced_errors', 'duplicate_candidates', 'actual_states')}))
    if report['status'] != 'passed':
        raise SystemExit(1)


if __name__ == '__main__':
    main()
