"""Run unchanged Cairn checks over exact archived sources on MSI.

Only source/HEAD acquisition is replaced. Parser, lint, solver, duplicate
policy, parked-hole policy, check, preview, and output writers are Cairn's.
The tracked-path manifest supplies the same artifact-existence predicate
as an exact checkout; revision-pinned artifacts are checked in the warm
repository's actual Git object database.
"""
import contextlib
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import sys
import tarfile
import time
from types import SimpleNamespace

started = time.monotonic()
root = Path('/projects/standard/hsiehph/sauer354/pestov91-hall-20260913')
parent = root.parent
os.chdir(root)
spec = importlib.util.spec_from_file_location('cairn_archive', root / 'tools/cairn.py')
cairn = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = cairn
spec.loader.exec_module(cairn)

def archive_sources(path):
    sources, paths = {}, set()
    with tarfile.open(path) as archive:
        for member in archive:
            if not member.isfile():
                continue
            paths.add(member.name)
            if (member.name.startswith('research/')
                    and member.name.count('/') == 1
                    and member.name.endswith('.md')
                    and Path(member.name).name not in cairn.NON_NODE_FILES):
                raw = archive.extractfile(member).read()
                try:
                    sources[member.name] = raw.decode('utf-8')
                except UnicodeDecodeError:
                    print('Non-UTF-8 archive entry:', member.name, repr(raw[:80]))
                    raise
    return sources, paths

baseline_path = parent / 'pestov91-hall-baseline-20260913.tar'
previous_upstream = parent / 'pestov91-three-coordinate-upstream-20260913.tar'
upstream_path = root / 'memo-validation/upstream.tar.gz'
delta_path = root / 'memo-validation/changes.tar.gz'
base_sources, _ = archive_sources(baseline_path)
previous, _ = archive_sources(previous_upstream)
base_sources.update(previous)
upstream, _ = archive_sources(upstream_path)
base_sources.update(upstream)
deleted = (root / 'memo-validation/deleted-paths.txt').read_text().splitlines()
for path in deleted:
    base_sources.pop(path, None)
delta, delta_paths = archive_sources(delta_path)
current_sources = {**base_sources, **delta}
tracked = set((root / 'memo-validation/tracked-paths.txt').read_text().splitlines())
base_paths = set(tracked)
current_paths = base_paths | delta_paths
changed = {Path(name).stem for name in current_sources
           if current_sources[name] != base_sources.get(name)}

real_exists = os.path.exists
real_objects = cairn.existing_git_objects
warm_repo = '/projects/standard/hsiehph/sauer354/nonsofic_existence'
prefix = str(root) + '/'

def compile_sources(sources, paths):
    nodes, errors = {}, []
    for name, content in sorted(sources.items()):
        cairn.load_node_text(content, str(root / name), nodes, errors, str(root))

    def archived_exists(path):
        value = os.fspath(path)
        if value.startswith(prefix):
            return value[len(prefix):] in paths
        return real_exists(path)

    os.path.exists = archived_exists
    cairn.existing_git_objects = lambda repo, objects: real_objects(warm_repo, objects)
    try:
        cairn.lint_nodes(nodes, errors, str(root))
    finally:
        os.path.exists = real_exists
        cairn.existing_git_objects = real_objects
    graph = cairn.Graph(nodes, errors, str(root))
    graph.compile_errors = list(errors)
    graph.source_manifest = None
    graph.cache_hit = False
    return graph, errors

base, base_errors = compile_sources(base_sources, base_paths)
current, current_errors = compile_sources(current_sources, current_paths)
cairn.compile_graph = lambda *args, **kwargs: (current, current_errors)
cairn.changed_research_files = lambda: changed
cairn.previous_graph = lambda *args: base
cairn.head_graph = lambda *args: (base, base_errors)

with (root / 'memo-cairn-check.json').open('w') as output, contextlib.redirect_stdout(output):
    check_code = cairn.cmd_check(SimpleNamespace(changed=True, strict=False, json=True))
with (root / 'memo-cairn-preview.txt').open('w') as output, contextlib.redirect_stdout(output):
    preview_code = cairn.cmd_preview(SimpleNamespace(json=False))
targets = [
    'fixed-marked-mf-consequences-are-uniformly-polynomial',
    'seam-recursive-presentability-forces-computable-intercept',
    'every-word-degree-is-dense-in-one-marked-mf-fiber',
    'seam-mf-amenable-and-locally-finite-radicals-agree',
    'ordinary-seam-consequences-retain-all-turing-degrees',
]
report = {
    'base_commit': '519394f6fa43a224e240b535a4e1aa25dde6ae87',
    'cairn_version': cairn.__version__,
    'check_code': check_code,
    'preview_code': preview_code,
    'claims': len(current.claims),
    'routes': len(current.routes),
    'changed_nodes': sorted(changed),
    'upstream_deleted_paths': deleted,
    'targets': {name: current.claims[name].status for name in targets},
    'baseline_errors': [entry for entry in base_errors if entry[0] == 'error'],
    'errors': [entry for entry in current_errors if entry[0] == 'error'],
    'seconds': round(time.monotonic() - started, 3),
    'delta_sha256': hashlib.sha256(delta_path.read_bytes()).hexdigest(),
    'runner_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
}
(root / 'memo-cairn-receipt.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
sys.exit(check_code or preview_code or
         int(any(current.claims[name].status != 'ESTABLISHED' for name in targets)))
