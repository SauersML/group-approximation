# Probe artifact restores hide build messages: a false GREEN on the hole gate (2026-09-13)

Lane pc-infra. This applies to every copy of the shared-clone probe job:
- `tools/bc-swarm/remote/bcjob.template.sh` on main;
- the copy on MSI that `bcprobe.sh` and `fzprobe.sh` upload from;
- the pc campaign copy.

## Mechanism

The probe job builds with the shared Lake artifact cache (`LAKE_ARTIFACT_CACHE=true`, `LAKE_RESTORE_ARTIFACTS=true`).
When an overlay module's input hash is already in the cache, Lake restores its outputs without elaborating the module
and writes a synthetic trace, `"synthetic": true, "log": []`. A restored module prints nothing, so no
`#print axioms` closures and no warnings reach the job log. Two gates read that log:
- The hole gate (rc=6) looks for the incomplete-proof warning. In the Palomar libs that warning is the only signal,
  because those libs build without `-DwarningAsError=true`.
- The closure gate (rc=7) parses the `#print axioms` output and compares the number of closures with the overlay's
  number of `#print axioms` lines.

A restored module therefore passes the hole gate by silence, and fails the closure count by silence. The first probe of
some bytes always builds and prints correctly; the defect hits a later probe of identical bytes, by any lane of any
campaign sharing the cache. Lake does replay the stored logs of up-to-date modules that have real traces (a
`Replayed <Module>` line followed by the warnings). Only the synthetic restore case loses them.

## Consequence

A green record lists the md5 of every overlay file that compiled. The landers' evidence gates (`fzgate.sh`, `pcland.sh`)
accept a file whose md5 appears in such a record. So a Palomar solution with an incomplete proof could pass the probe
and land, provided the same bytes had been built once before, for example by an earlier failed probe.

## Evidence (shared clone `bc_clones/bc`, 2026-09-13)

| probe tag | overlay | template | result |
|---|---|---|---|
| 0913-020954-89615 | smoke module with two `#print axioms` lines | original | Built; 2 closures printed; PROBE GREEN (correct) |
| 0913-021434-13436 | the same smoke bytes, plus a dependent whose theorem uses a newly declared constant outside propext, Classical.choice and Quot.sound | original | smoke module restored, not Built; "1 printed, 3 requested"; rc=7 caught the declared constant, but the count alone would have failed a clean probe (false red) |
| 0913-022958-80841 | a Palomar-lib module whose only theorem has an incomplete proof, plus a lakefile lib entry | original | Built; warning printed; rc=6 (correct) |
| 0913-082034-20007 | bytes identical to 0913-022958-80841; its outputs absent from the clone | original | "rebuilt modules: 0"; no warning printed; **PROBE GREEN, and a green record carrying the file's md5 was written** (false GREEN; the record was renamed `.calib-falsegreen.`) |
| 0913-082211-21312 | bytes identical to 0913-022958-80841 | v1 fix: remove outputs, rebuild with `LAKE_RESTORE_ARTIFACTS=false` | restored again, still not Built; rc=8. This Lake build does not honour the variable |
| 0913-082231-21596 | the smoke module | v1 fix | still not Built; rc=8 on a clean module, so v1 is rejected |
| 0913-082512-24488 | bytes identical to 0913-022958-80841, restored | v2 fix (below) | `[job] replay:` elaborated it; warning printed; rc=6 (correct: the false GREEN is closed) |
| 0913-082532-24859 | the smoke module, restored | v2 fix | `[job] replay:` elaborated it; "2 printed, 2 requested"; PROBE GREEN (correct: clean probes still pass) |

The smoke module's trace after 0913-021434-13436 read `"synthetic": true`, with `"log": []` and a hardlinked olean.

## Fix (v2)

The fix adds one rule to the job template, placed right after the main `lake build`. Every overlay module whose
messages a gate reads, and that this build did not report as Built, is handled as follows:
- which modules: Palomar/*.lean outside *Challenge.lean, and any file with `#print axioms` lines;
- it is elaborated once more with `lake env lean <file>`, which writes no outputs and does not touch the cache;
- its messages are appended to the log in Lake's `severity: file:l:c:` form, and a closure line printed without a
  position gets `info: file:0:0:`;
- the hole and closure gates then read them as usual, and an elaboration failure fails the probe with rc=8.

The summary prints the `[job] replay:` lines. The fix lands together with this artifact, in `tools/bc-swarm/remote/bcjob.template.sh`.

## Adoption

- A campaign with its own remote copy of the job template must reinstall it on MSI.
- Green records that the old template wrote for Palomar modules, or for drivers with `#print axioms` lines, certify a
  module only if its build log shows it as Built. Re-probe any other such bytes with the fixed template before landing.
