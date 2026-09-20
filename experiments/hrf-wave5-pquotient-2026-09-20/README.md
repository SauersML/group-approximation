# Exact group p-quotients of the marked canonical cover

## Archived execution boundary

The commands below document the originating session, not a currently running
job or instructions to compute on the local workstation. Class ten completed.
Class eleven processed all 24 lift relators, then stopped in finalization:
`class11-finish-run.json` records return code -15 after about 60 seconds, and
`class11-finish.log` ends at `PHASE source relations`. There is no completed
`class11.json` and no certified central order at class eleven.

The saved local workspace identifies its GAP kernel as `4.15dev`; the warm
MSI Sage installation inspected during handoff uses GAP 4.14.0. These are not
interchangeable workspace formats. Do not alter a workspace header to bypass
the version check. Reproduction must use an explicitly compatible runtime,
or start from the source presentation on MSI with new, separately labelled
receipts. Historical `/tmp` locations below are not shared-storage paths and
are not a portable part of the mathematical certificate.

## Original run instructions and provenance

The GAP source presents the full integral cover with six generators,
24 relations, and marked central word `C_1^-1`. It does not impose
seventh power one on that marked word. Modular exponents are used only
inside the three known exponent-seven vertex groups.

The installed GAP 4.15.1 core is `/tmp/gap-4.15.1/gap`; use `--bare`
because no optional package is required. The Python runner captures
both output streams, exit status, and an explicit timeout.

```sh
python3 experiments/hrf-wave5-pquotient-2026-09-20/run_gap.py --class-bound 9 --seconds 45 --save /tmp/hrf-pquot-class9.ws
```

The quotient class here is lower exponent-seven central class,
not ordinary nilpotency class. Completed JSON results record all layer
ranks, total order as a power of seven, and the order of the canonical
central image. Every completed quotient checks all 24 source relators
and commutation of the marked word with every pc generator.

## Checkpoint a larger step

`advance.g` follows GAP core's `PQuotient` phase order. It can save after
consistency, after each source relator in the lift, and after completion.
For example, to advance class ten to eleven:

```sh
python3 experiments/hrf-wave5-pquotient-2026-09-20/run_gap.py --class-bound 11 --stage prepare --seconds 90 --restore /tmp/hrf-pquot-class10.ws --save /tmp/hrf-pquot-class11-prelift.ws
python3 experiments/hrf-wave5-pquotient-2026-09-20/run_gap.py --class-bound 11 --stage lift --label batch1 --seconds 120 --restore /tmp/hrf-pquot-class11-prelift.ws --save /tmp/hrf-pquot-class11-lift.ws
```

Each lift batch saves immediately after every fully processed relator,
advancing the stored next-relator index only after its vector is added
to the central relation matrix. It stops between relators after about
20 CPU seconds. Resume using the most recent lift workspace and a new
log label:

```sh
python3 experiments/hrf-wave5-pquotient-2026-09-20/run_gap.py --class-bound 11 --stage lift --label batch2 --seconds 120 --restore /tmp/hrf-pquot-class11-lift.ws --save /tmp/hrf-pquot-class11-lift.ws
```

Only when the log says `CHECKPOINT before source relations` is the lift
finished. Then run:

```sh
python3 experiments/hrf-wave5-pquotient-2026-09-20/run_gap.py --class-bound 11 --stage finish --seconds 300 --restore /tmp/hrf-pquot-class11-lift.ws --save /tmp/hrf-pquot-class11.ws
```

Stage and class guards reject inconsistent restarts. Restored runs require
an explicit save destination, so an inherited workspace setting cannot
silently select one. A timeout preserves the last completed per-relator
workspace; it proves nothing about the next uncompleted relator or final
quotient. Workspaces in `/tmp` are local operational checkpoints, not
committed mathematical certificates.
