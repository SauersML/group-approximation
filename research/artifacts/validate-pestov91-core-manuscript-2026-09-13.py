"""Validate the manuscript delta on MSI without scanning unrelated Lean files.

Use the repository's unchanged manifest validator and declaration parser,
indexing exactly the modules named by the complete current manifest.  No
Lean source or declaration mapping changes in this manuscript-only batch.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys
import time

started = time.monotonic()
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--work-dir', type=Path, required=True,
                    help='directory containing the exact manuscript audit inputs')
parser.add_argument('--repo', type=Path, required=True,
                    help='group-approximation checkout containing cited Lean modules')
args = parser.parse_args()
root = args.work_dir.resolve()
repo = args.repo.resolve()
sys.path.insert(0, str(root / 'scripts'))
import check_non_mf_claim_manifest as checker
from lean_decls import index_file

manifest = json.loads((root / 'NON_MF_NUMBERED_CLAIMS.json').read_text())
stored_baseline = json.loads((root / 'manuscript-baseline-manifest.json').read_text())
printed_baseline = {claim.claim_id: claim for claim in
                    checker.read_printed_claims(root / 'baseline.tex')}
old = {claim['id']: {**claim, 'statement_sha256':
                    printed_baseline[claim['id']].statement_sha256}
       for claim in stored_baseline['claims']}
current = {claim['id']: claim for claim in manifest['claims']}
added = set(current) - set(old)
expected = {'lem:chain-core-models', 'lem:transient-matrices',
            'thm:core-ring-reflection', 'thm:core-mf-radical'}
assert added == expected, added
drift = {name: {key: [entry.get(key), current[name].get(key)]
                for key in entry.keys() | current[name].keys()
                if entry.get(key) != current[name].get(key)}
         for name, entry in old.items() if current[name] != entry}
assert not drift, json.dumps(drift, indent=2)
stored = {claim['id']: claim for claim in stored_baseline['claims']}
stale = {name: {key: [entry.get(key), old[name].get(key)]
                for key in entry.keys() | old[name].keys()
                if entry.get(key) != old[name].get(key)}
         for name, entry in stored.items() if old[name] != entry}
assert set(stale) == {'thm:headline', 'cor:regular-nonmf-algebra'}, stale
assert all(set(changes) == {'statement_sha256'} for changes in stale.values())
assert all(current[name]['status'] == 'paper-proof' and
           current[name]['lean'] == [] for name in added)

modules = sorted({ref['module'] for claim in manifest['claims']
                  for ref in claim['lean']})
index = {}
for module in modules:
    index.update(index_file(repo / 'GroupApproximation' / (module + '.lean')))
checker.build_index = lambda _repo: index
errors = checker.validate(repo, root / 'non_mf_groups_exist.tex',
                          root / 'NON_MF_NUMBERED_CLAIMS.json')
report = {
    'new_paper_proof_claims': sorted(added),
    'unchanged_existing_claims': len(old),
    'preexisting_stale_statement_hashes_refreshed': stale,
    'total_claims': len(current),
    'indexed_cited_lean_modules': len(modules),
    'errors': errors,
    'seconds': round(time.monotonic() - started, 3),
    'tex_sha256': hashlib.sha256((root / 'non_mf_groups_exist.tex').read_bytes()).hexdigest(),
    'manifest_sha256': hashlib.sha256((root / 'NON_MF_NUMBERED_CLAIMS.json').read_bytes()).hexdigest(),
}
(root / 'manuscript-check-receipt.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
sys.exit(bool(errors))
