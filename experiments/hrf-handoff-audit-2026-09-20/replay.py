"""Bounded remote replay of three archived exact certificates.

Run on MSI against an exported, pinned Git tree. Generated outputs stay in
that task-owned export; this does not update the research worktree.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import time


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--revision', required=True)
    args = parser.parse_args()
    root = args.root.resolve(strict=True)
    if not str(root).startswith('/projects/standard/hsiehph/sauer354/'):
        parser.error('replay root must be the task-owned MSI shared-storage export')
    checks = [
        ('hrf-wave4-four-generator-2026-09-20', 'verify_finite_witness.py',
         ['class_five_lie_witness.json']),
        ('hrf-wave4-h31-2026-09-20', 'verify_module_rank.py',
         ['retraction_module_rows.json']),
        ('hrf-wave3-detectors-2026-09-20', 'verify_cycles.py',
         ['borel_square_cycles.json']),
    ]
    report = {
        'snapshot_revision': args.revision,
        'host': platform.node(),
        'python': platform.python_version(),
        'cpu_affinity': sorted(os.sched_getaffinity(0)),
        'timeout_seconds_per_check': 40,
        'scope': 'Three exact certificate replays, not all archived computations or a Lean proof.',
        'checks': [],
    }
    for directory, script, inputs in checks:
        base = root / 'experiments' / directory
        hashes = {
            str(path.relative_to(root)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in [base / script, *(base / name for name in inputs)]
        }
        started = time.monotonic()
        try:
            result = subprocess.run([sys.executable, str(base / script)],
                                    cwd=root, capture_output=True, text=True,
                                    timeout=40, check=False)
            entry = {'return_code': result.returncode, 'timed_out': False,
                     'stdout': result.stdout, 'stderr': result.stderr}
        except subprocess.TimeoutExpired as error:
            entry = {'return_code': None, 'timed_out': True,
                     'error': str(error)}
        entry.update(script=str((base / script).relative_to(root)),
                     seconds=round(time.monotonic() - started, 3), hashes=hashes)
        report['checks'].append(entry)
        report['all_passed'] = (len(report['checks']) == len(checks)
                                and all(x['return_code'] == 0 for x in report['checks']))
        args.output.write_text(json.dumps(report, indent=2) + '\n')
        print(json.dumps(entry), flush=True)
        if entry['return_code'] != 0:
            return 1
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
