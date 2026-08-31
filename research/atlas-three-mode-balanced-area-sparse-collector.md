---
rg: 2
id: atlas-three-mode-balanced-area-sparse-collector
kind: claim
title: The balanced-area table has a capped sparse exact collector and Bezout exporter
---

**ESTABLISHED.**
`experiments/atlas_three_mode_balanced_area.py` implements `(BAT1)` for the
complete packet produced by `atlas-rank-five-complete-packet-exporter`.  It
never allocates a regular `A8` matrix.  Its exact label states use only

```text
L_g W^epsilon
```

and a first-`E` cyclic-reset state.  Indeed, after expanding

```text
U = E tensor 1 + ((I+W)/2-E) tensor S + ((I-W)/2) tensor D,
```

terms containing no `E` remain affine permutations.  For a term containing
`E`, choose its first `E` in the original projector-slot order and cyclically
rotate the trace to that occurrence.  Between consecutive resets only one
affine permutation remains, and the segment survives precisely when its
translation part is the identity.  Every expansion term is assigned to one
and only one distinguished reset.  In parallel, coefficient words are
normalized exactly to

```text
t^A S^a D^b,                 S D = t D S.
```

Only balanced states `a=b=0` enter the exported Laurent coefficient.  Exact
dyadic/rational arithmetic is used throughout.  The script verifies five
closed-form controls: the empty word, nonidentity words in either chart, the
second-chart identity, and second-chart cancellation.

The exporter also forms `f_s(t)-1`, clears its Laurent shift, maintains an
exact incremental polynomial gcd over `Q`, and exports a checked Bezout
certificate.  With `--stop-gcd-one` it stops at the first rigorous negative
certificate; otherwise it exports the full table required by a positive
decision.  The artifact records the complete packet SHA-256

```text
9e751115287b18fbe847309379d2710ffa0b1466c836d32ff4ec24446e6c2b99.
```

### Lightweight boundary

Packet assembly takes about three seconds and negligible memory locally.  A
calibration on the first nonempty relation already took about 23 seconds even
after the first-reset compression (with fewer than 50,000 live sparse states).
Consequently the complete 4,648-entry collection was deliberately **not** run
locally.  The capped local command aborts before a large allocation.  MSI job
`17081018` was submitted on 2026-08-26 using the checked-in batch file
`research/artifacts/atlas-rank5-balanced-area.sbatch`; its exact payload is

```text
python3 experiments/atlas_three_mode_balanced_area.py \
  --state-cap 500000 --stop-gcd-one \
  --emit experiments/atlas-rank5-balanced-area.json
```

Submission provenance and retrieval commands are recorded in
`research/artifacts/atlas-rank5-balanced-area-job-17081018.md`.
The first submission exposed a stale remote packet-source API and stopped in
four seconds before collection.  After explicit source synchronization and a
remote 4,648-entry/checksum preflight, the same job was resubmitted as
`17081560`.  The retry completed in 54 seconds with peak RSS 200,356 KB and
the sentinel `SENTINEL_ATLAS_BAT1_DONE`.  Its first relation made the exact gcd
equal to one, so `--stop-gcd-one` terminated after one row.  The fetched JSON
and log are `experiments/atlas-rank5-balanced-area.json` and
`experiments/atlas-rank5-balanced-area-17081560.log`; the mathematical no-go is
recorded in `atlas-first-rank-five-relator-kills-order-one-weyl-slice`.

This establishes the collector and certificate format, not the coefficient
table or common-root decision.  Those remain open until the remote artifact is
returned and audited.
