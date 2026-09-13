"""Audit the rank-three manuscript delta using the repository's validators.

Index only the cited Lean modules: no Lean code or badge mapping changes.
All execution is intended for MSI, using explicit paths, not a fixed worktree.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys
import time

started = time.monotonic()
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--work-dir', type=Path, required=True)
parser.add_argument('--repo', type=Path, required=True)
args = parser.parse_args()
root, repo = args.work_dir.resolve(), args.repo.resolve()
sys.path.insert(0, str(root / 'scripts'))
import check_non_mf_claim_manifest as checker
from lean_decls import index_file

manifest = json.loads((root / 'NON_MF_NUMBERED_CLAIMS.json').read_text())
baseline = json.loads((root / 'manuscript-baseline-manifest.json').read_text())
old = {claim['id']: claim for claim in baseline['claims']}
current = {claim['id']: claim for claim in manifest['claims']}
printed_old = {claim.claim_id: claim for claim in
               checker.read_printed_claims(root / 'baseline.tex')}
assert all(printed_old[name].statement_sha256 == claim['statement_sha256']
           for name, claim in old.items())
added = set(current) - set(old)
assert added == {'prop:bilateral-three', 'lem:involution-localization',
                 'cor:dynamic-rank-budget'}, added
changed = {name for name, claim in old.items() if current.get(name) != claim}
assert changed == {'thm:core-mf-radical'}, changed
changed_fields = {key for key in current['thm:core-mf-radical']
                  if current['thm:core-mf-radical'][key] != old['thm:core-mf-radical'][key]}
assert changed_fields == {'statement_sha256', 'dependencies'}, changed_fields
assert all(current[name]['status'] == 'paper-proof' and not current[name]['lean']
           for name in added | changed)
old_badges = {(ref['module'], ref['declaration'])
              for claim in old.values() for ref in claim['lean']}
new_badges = {(ref['module'], ref['declaration'])
              for claim in current.values() for ref in claim['lean']}
assert old_badges == new_badges

modules = sorted({module for module, _declaration in new_badges})
index = {}
for module in modules:
    index.update(index_file(repo / 'GroupApproximation' / (module + '.lean')))
checker.build_index = lambda _repo: index
errors = checker.validate(repo, root / 'non_mf_groups_exist.tex',
                          root / 'NON_MF_NUMBERED_CLAIMS.json')
report = {
    'new_paper_proof_claims': sorted(added),
    'strengthened_paper_proof_claims': sorted(changed),
    'unchanged_existing_claims': len(old) - len(changed),
    'total_claims': len(current),
    'indexed_cited_lean_modules': len(modules),
    'lean_badge_mappings_unchanged': True,
    'errors': errors,
    'seconds': round(time.monotonic() - started, 3),
    'tex_sha256': hashlib.sha256((root / 'non_mf_groups_exist.tex').read_bytes()).hexdigest(),
    'manifest_sha256': hashlib.sha256((root / 'NON_MF_NUMBERED_CLAIMS.json').read_bytes()).hexdigest(),
}
(root / 'three-coordinate-manuscript-receipt.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
sys.exit(bool(errors))
