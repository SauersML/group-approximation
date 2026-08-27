# Atlas BAT1 remote collection: MSI job 17081018

Submitted on 2026-08-26 through the configured MSI wrapper.  The job was
accepted by Slurm as

```text
17081018  amdsmall  atlas-bat1  PD  0:00  4:00:00  (None)
```

The checked-in submission file is
`research/artifacts/atlas-rank5-balanced-area.sbatch`.  Its exact payload is

```text
module load python3/3.12.4_anaconda2024.06-1_libmamba
python3 experiments/atlas_three_mode_balanced_area.py \
  --state-cap 500000 --stop-gcd-one \
  --emit experiments/atlas-rank5-balanced-area.json
```

It uses one CPU, 8 GB, and a four-hour limit on `amdsmall`.  Both the collector
and the complete-packet serializer were uploaded explicitly and passed remote
`py_compile` before submission.  The collector never allocates a dense regular
`A8` matrix.  Its 500,000-state cap is a second remote safety boundary: hitting
it produces a `LIGHTWEIGHT STOP` rather than an uncontrolled allocation.

Expected remote outputs are

```text
experiments/atlas-rank5-balanced-area-17081018.log
experiments/atlas-rank5-balanced-area.json
```

Successful completion is marked by

```text
SENTINEL_ATLAS_BAT1_DONE
```

Audit and retrieval commands:

```text
/Users/user/msi-node/msi \
  "sacct -j 17081018 --format=JobID,State,Elapsed,MaxRSS,ExitCode"
/Users/user/msi-node/msi get \
  /projects/standard/hsiehph/sauer354/nonsofic_existence/experiments/atlas-rank5-balanced-area-17081018.log \
  experiments/atlas-rank5-balanced-area-17081018.log
/Users/user/msi-node/msi get \
  /projects/standard/hsiehph/sauer354/nonsofic_existence/experiments/atlas-rank5-balanced-area.json \
  experiments/atlas-rank5-balanced-area.json
```

### Submission result and retry

Job `17081018` failed safely after four seconds with exit `1:0` and peak RSS
46,808 KB, before the collector ran.  The remote checkout had an older
`atlas_relator_rank5_full_family.py` without the packet exporter's
`generate_relators` API.  The collector itself did not fail and no local
fallback was attempted.

The four packet-source scripts were then synchronized explicitly.  A remote
preflight reconstructed all 4,648 entries and verified the packet SHA-256
above.  The identical batch file was resubmitted as MSI job

```text
17081560
```

At that point the coefficient-table and common-root claims remained open
pending the retry's JSON, packet hash, exact gcd, and Bezout audit.

### Retry result

Job `17081560` completed successfully in 54 seconds with peak RSS 200,356 KB
and exit `0:0`.  The log ends in `SENTINEL_ATLAS_BAT1_DONE`.  The packet hash
matches, and the exact collector stopped after the first relation because its
incremental gcd was already one.  A separate remote rational-arithmetic audit
reconstructed the relation polynomial from the sparse row and verified the
exported Bezout identity exactly.  The fetched files have SHA-256 hashes

```text
d33e4f44a1a357b0e084e73bacfe8d7f1421c438422b4757f85efb4e4c404fce  experiments/atlas-rank5-balanced-area.json
c10a7e534429b6303ca69ae5dfb7529f8c2a2e835637bf2779652d808eb83c51  experiments/atlas-rank5-balanced-area-17081560.log
```
