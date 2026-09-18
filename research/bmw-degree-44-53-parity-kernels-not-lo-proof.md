---
rg: 2
id: bmw-degree-44-53-parity-kernels-not-lo-proof
kind: route
title: The small-degree BMW census pipeline run on the (4,4) patterns with involutions and all (5,3) patterns, with streamed radius-8 SAT instances and a larger finiteness cap for the stragglers
target: bmw-degree-44-53-parity-kernels-not-left-orderable
requires: []
artifacts:
  - experiments/bmw-census-left-orders-2026-09-17/README.md
  - experiments/bmw-census-left-orders-2026-09-17/vh_enum.py
  - experiments/bmw-census-left-orders-2026-09-17/lo_census.py
  - experiments/bmw-census-left-orders-2026-09-17/selfcheck.py
  - experiments/bmw-census-left-orders-2026-09-17/summarize.py
  - experiments/bmw-census-left-orders-2026-09-17/run_all.sh
  - experiments/bmw-census-left-orders-2026-09-17/run_all.log
  - experiments/bmw-census-left-orders-2026-09-17/resume.sh
  - experiments/bmw-census-left-orders-2026-09-17/run_53.sh
  - experiments/bmw-census-left-orders-2026-09-17/run_53.log
  - experiments/bmw-census-left-orders-2026-09-17/rerun_40_40.log
  - experiments/bmw-census-left-orders-2026-09-17/rerun_40_40_tail.jsonl
  - experiments/bmw-census-left-orders-2026-09-17/rerun_50_30.log
  - experiments/bmw-census-left-orders-2026-09-17/rerun_50_30.jsonl
  - experiments/bmw-census-left-orders-2026-09-17/enum_4040.log
  - experiments/bmw-census-left-orders-2026-09-17/selfcheck_2.log
  - experiments/bmw-census-left-orders-2026-09-17/bigsat.py
  - experiments/bmw-census-left-orders-2026-09-17/bigsat.log
  - experiments/bmw-census-left-orders-2026-09-17/bigsat256.log
  - experiments/bmw-census-left-orders-2026-09-17/bigsat5030.log
  - experiments/bmw-census-left-orders-2026-09-17/bigcap.py
  - experiments/bmw-census-left-orders-2026-09-17/bigcap.log
  - experiments/bmw-census-left-orders-2026-09-17/bigcap5030.log
  - experiments/bmw-census-left-orders-2026-09-17/run_5030.sh
---

Scripts are in `experiments/bmw-census-left-orders-2026-09-17/`. The mathematics is §1–§5 of
`small-degree-bmw-parity-kernels-not-left-orderable-proof`, which is degree-independent; this route
reuses it verbatim and adds only the new finite computations.

## 1. What is reused

From `small-degree-bmw-parity-kernels-not-left-orderable-proof`:
- **§1 Data.** Every BMW group of degree `(m,n)` is `Γ(SQ)` for a Klein-closed bijection
  `SQ : A × B → B × A`, with any numbers `p_A`, `p_B` of transposed letter pairs.
- **§2 Normal forms.** Confluence is checked per datum by `VH.confluence()`, which `lo_census.py`
  runs on every class it processes.
- **§3 Parity kernel.** `Γ^+` has index 4 and is torsion-free.
- **§4 SAT lemma.** An UNSAT positive-cone instance on `Γ^+ ∩ B_R` proves `Γ^+` is not left-orderable.
- **§5 Reducibility certificate.** If both automaton images are finite, `Γ` is reducible.
- **§6 Soundness of the census.** The enumeration, the three symmetries, and the orbit-sum
  completeness assertion. None of it depends on the degree.

## 2. Enumeration of the new patterns

`vh_enum.py m pA n pB` writes `census_mpA_npB.json` for the patterns
40_40, 41_40, 41_41, 42_40, 42_41 (degree (4,4)) and 50_30, 50_31, 51_30, 51_31, 52_30, 52_31
(degree (5,3)). `census` asserts that the orbit sizes sum to the raw count (`enum_4040.log` for the
largest, 444508 raw data in 824 classes).

`selfcheck_2.log` reruns `selfcheck.py` on all eleven new census files: for every class it checks that
the critical pairs of the rewriting system resolve, and that the fast normal-form multiplication used by
`lo_census.py` agrees with the rewriting normal form on random words. All 6147 classes pass.

## 3. Pipeline runs

`run_all.sh` / `resume.sh` (degree (4,4)) and `run_53.sh` / `resume.sh` (degree (5,3)) run
`lo_census.py` on every class, in chunks of 100 under `nice -n 10 timeout 1200`. The records are the same
as in §7 of the reused route: radius 4 with all products; then, if an image is not certified finite,
R6 (short 4), R6 (all), R8 (short 2), stopping at the first UNSAT.

**Timeouts.** Three chunks timed out (exit 124): 40_40 from 200 and 50_30 from 200 and from 400. The
indices missing from them (40_40 #292–#299; 50_30 #283–#299 and #481–#500) were rerun per class
(`rerun_40_40.*`) or in chunks of 5 (`rerun_50_30.*`), all with exit 0, and merged. Every
`out_*.jsonl` has exactly one record for each class index; the class counts in §5 equal the census
sizes.

## 4. Stragglers

**Streamed radius-8 instances.** `bigsat.py census idx R short` produces the same CNF as
`lo_census.lo_sat(G, R, short)`: the same ball, the same element set `S`, and the same three clause
families. It streams the clauses into the solver instead of storing them. It is run once with
CaDiCaL 1.5.3 and once with Glucose 4.

The five non-certified 40_40 and two non-certified 50_30 classes that were SAT through R8 (short 2) in
the pipeline were rerun at R8 (short 4):

| class | clauses | CaDiCaL | Glucose | log |
|---|---|---|---|---|
| 40_40#176 | 5756592 | UNSAT | UNSAT | `bigsat.log` |
| 40_40#256 | 5756592 | UNSAT | UNSAT | `bigsat256.log` |
| 50_30#258 | 11045771 | UNSAT | UNSAT | `bigsat5030.log` |
| 50_30#470 | 11045771 | UNSAT | UNSAT | `bigsat5030.log` |
| 40_40#193, #281, #332 | 5756592 | SAT | SAT | `bigsat.log` |

**Larger finiteness cap.** `bigcap.py census cap idx...` reruns `finite_image` with a larger
minimal-automaton cap.
- `51_30#506` had one image certified finite at cap 4000. It is the only such class in the new
  patterns. At cap 60000 both images are finite, of orders 6 and 6912 (`bigcap.log`), so it is
  reducible by §5 of the reused route.
- The other stragglers are not certified finite at cap 60000 (`bigcap.log`, `bigcap5030.log`). That
  is irrelevant, because each of them is either refuted above or excluded by the theorem.

## 5. Assembly

`summarize.py` tallies `out_*.jsonl`. For the new patterns, every class falls into one of these
outcomes:
- certified reducible (both images finite);
- not certified finite, and UNSAT at R4 (all products) or at R6 (short 4);
- one of the seven stragglers in §4;
- `51_30#506`.

The per-pattern counts are the table in `bmw-degree-44-53-parity-kernels-not-left-orderable`.

**Proof of the theorem.** Let `Γ` be an irreducible BMW group of degree (4,4) or (5,3).
- By §1 of the reused route, `Γ ≅ Γ(SQ)` for a datum in some pattern. If the pattern is 40_30, 41_30,
  41_31, 42_30, 42_31 or 42_42, the claim is `small-degree-irreducible-bmw-parity-kernels-not-left-orderable`.
- Otherwise the class is in one of the census files above (§2 and §6 of the reused route, applied to
  the new census files).
- It is not certified reducible, since `Γ` is irreducible (§5 of the reused route; for `51_30#506`, §4
  here).
- So by §3 and §4 here it has an UNSAT positive-cone instance with both solvers, unless it is
  40_40#193, #281 or #332.
- By the SAT lemma, `Γ^+` is not left-orderable. Left-orderability passes to subgroups, so no group
  containing `Γ^+` is left-orderable. ∎

**Verification tier.** Computer-certified: exhaustive enumeration with a completeness assertion,
a per-class confluence and multiplication check, exact automaton finiteness certificates, and two independent SAT
solvers agreeing on every refuting instance. No proof certificates (DRAT) were stored.
