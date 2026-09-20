# Supplied polynomial-germ arithmetic checks

`check_polynomial_germs.py` preserves the supplied Python script. The supplied
output is recorded separately as `supplied-check-results.json`.
`check_results.json` is the output downloaded from a fresh MSI replay, not a copy
of the supplied output. The two JSON files are byte-for-byte identical.

Fresh replay:

- Host: MSI `acn112`.
- Start: `2026-09-20T17:24:15Z` (UTC).
- Interpreter: `/usr/bin/python3.12`, Python `3.12.13`, standard library only.
- Working directory:
  `/projects/standard/hsiehph/sauer354/bh-finalize-20260920/polynomial-germs`.
- Source SHA-256:
  `d87751d0b557d2c8513c504f74a64e002f043759b8dad56d400fdf06515946ab`.
- Limits: 60-second wall timeout, one CPU (affinity 63), nice level 10,
  1 GiB virtual-memory cap (`ulimit -v 1048576`).
- Result: exit 0, `PASS`, 26,296 checks, seed `20260920`.
- Measured runtime: 1.94 seconds; maximum RSS: 16,036 KiB; stderr empty.

Command, executed remotely through `/Users/user/msi-node/msi -n acn112`:

```sh
cd /projects/standard/hsiehph/sauer354/bh-finalize-20260920/polynomial-germs
ulimit -v 1048576
/usr/bin/time -f 'elapsed_seconds=%e max_rss_kib=%M exit_status=%x' \
  -o timing.txt timeout 60s nice -n 10 taskset -c 63 \
  /usr/bin/python3.12 check_polynomial_germs.py \
  > check_results.json 2> check.stderr
```

The remote directory also retains `environment.txt`, `timing.txt`, and
`check.stderr`. No local Python execution, dependency installation, or build was
performed. The replay completed; it left no running job.

## Scope

These are exact rational/integer arithmetic checks of finitely many selected
inputs. The polynomial checks use degrees 0 through 7 and finitely many integer
arguments. The unitriangular checks use dimensions 2 through 6, `p=3`, `q=2`,
and bounded randomly generated rational entries. The seed makes these samples
reproducible. The graded-index check tests a finite arithmetic sum; it does not
prove the group index formula. The final Heisenberg check tests the exponent
identity `-(n-1)+n=1`; it does not construct a faithful group representation.

Passing does not prove the infinite-group embedding, faithfulness for all
parameters, the stabilizer HNN decomposition, punctured-space induction,
type `F_infinity`, finite presentation, simplicity, or any Boone–Higman theorem.
Those require independent mathematical and Lean proofs. The script's original
disclaimer is retained.
