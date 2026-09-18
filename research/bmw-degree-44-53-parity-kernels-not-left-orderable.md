---
rg: 2
id: bmw-degree-44-53-parity-kernels-not-left-orderable
kind: claim
title: Every irreducible BMW lattice of degree (4,4) or (5,3), except three (4,4) classes with intransitive local actions, has a non-left-orderable parity kernel
distinct_from:
  small-degree-irreducible-bmw-parity-kernels-not-left-orderable: that covers degrees (3,3), (4,3) and torsion-free (4,4) and has no survivor; this covers the remaining 3704 classes of degree (4,4), those with involution letters, and all 2443 classes of degree (5,3), and here three classes survive every refutation
  irreducible-tree-product-lattices-are-not-left-orderable: that is the OPEN class-wide statement for boundary-2-transitive dense projections; this is an exhaustive census of two small degrees with arbitrary local actions, and the three survivors have intransitive local actions on both factors, so they lie outside that statement
  minimal-torsion-free-small-tree-lattices-not-left-orderable: that treats lattices with four vertex orbits in degrees (3,3) and (3,4); this treats vertex-transitive lattices of degrees (4,4) and (5,3)
  bmw-44-sat-survivor-parity-kernels-not-left-orderable: that is the OPEN statement for the three survivors excluded here
artifacts:
  - experiments/bmw-census-left-orders-2026-09-17/README.md
  - experiments/bmw-census-left-orders-2026-09-17/run_all.sh
  - experiments/bmw-census-left-orders-2026-09-17/run_all.log
  - experiments/bmw-census-left-orders-2026-09-17/run_53.sh
  - experiments/bmw-census-left-orders-2026-09-17/run_53.log
  - experiments/bmw-census-left-orders-2026-09-17/resume.sh
  - experiments/bmw-census-left-orders-2026-09-17/enum_4040.log
  - experiments/bmw-census-left-orders-2026-09-17/census_40_40.json
  - experiments/bmw-census-left-orders-2026-09-17/census_41_40.json
  - experiments/bmw-census-left-orders-2026-09-17/census_41_41.json
  - experiments/bmw-census-left-orders-2026-09-17/census_42_40.json
  - experiments/bmw-census-left-orders-2026-09-17/census_42_41.json
  - experiments/bmw-census-left-orders-2026-09-17/census_50_30.json
  - experiments/bmw-census-left-orders-2026-09-17/census_50_31.json
  - experiments/bmw-census-left-orders-2026-09-17/census_51_30.json
  - experiments/bmw-census-left-orders-2026-09-17/census_51_31.json
  - experiments/bmw-census-left-orders-2026-09-17/census_52_30.json
  - experiments/bmw-census-left-orders-2026-09-17/census_52_31.json
  - experiments/bmw-census-left-orders-2026-09-17/out_40_40.jsonl
  - experiments/bmw-census-left-orders-2026-09-17/out_41_40.jsonl
  - experiments/bmw-census-left-orders-2026-09-17/out_41_41.jsonl
  - experiments/bmw-census-left-orders-2026-09-17/out_42_40.jsonl
  - experiments/bmw-census-left-orders-2026-09-17/out_42_41.jsonl
  - experiments/bmw-census-left-orders-2026-09-17/out_50_30.jsonl
  - experiments/bmw-census-left-orders-2026-09-17/out_50_31.jsonl
  - experiments/bmw-census-left-orders-2026-09-17/out_51_30.jsonl
  - experiments/bmw-census-left-orders-2026-09-17/out_51_31.jsonl
  - experiments/bmw-census-left-orders-2026-09-17/out_52_30.jsonl
  - experiments/bmw-census-left-orders-2026-09-17/out_52_31.jsonl
  - experiments/bmw-census-left-orders-2026-09-17/selfcheck_2.log
  - experiments/bmw-census-left-orders-2026-09-17/bigsat.py
  - experiments/bmw-census-left-orders-2026-09-17/bigsat.log
  - experiments/bmw-census-left-orders-2026-09-17/bigsat256.log
  - experiments/bmw-census-left-orders-2026-09-17/bigsat5030.log
  - experiments/bmw-census-left-orders-2026-09-17/bigcap.py
  - experiments/bmw-census-left-orders-2026-09-17/bigcap.log
  - experiments/bmw-census-left-orders-2026-09-17/bigcap5030.log
  - experiments/bmw-census-left-orders-2026-09-17/run_5030.sh
  - experiments/bmw-census-left-orders-2026-09-17/irred_tw.py
  - experiments/bmw-census-left-orders-2026-09-17/localact.py
  - experiments/bmw-census-left-orders-2026-09-17/localact.log
---

**ESTABLISHED (computer-certified: exhaustive enumeration, two agreeing SAT solvers, automaton
finiteness certificates).** Proof: `bmw-degree-44-53-parity-kernels-not-lo-proof`.

**Setting.** As in `small-degree-irreducible-bmw-parity-kernels-not-left-orderable`: a BMW group of
degree `(m,n)` acts simply transitively on the vertices of `T_m × T_n` without swapping the factors.
Its parity kernel `Γ^+` (both lengths even) has index 4 and is torsion-free. Letters may be
involutions. Classes are pattern `mpA_npB`, where `pA`, `pB` count transposed letter pairs, and
`#i` is the class index in `census_mpA_npB.json`.

**Theorem.** Let `Γ` be an irreducible BMW group of degree (4,4) or (5,3). Suppose `Γ` is not in one
of the classes `40_40#193`, `40_40#281`, `40_40#332`. Then `Γ^+` is not left-orderable, and neither
is any group containing `Γ^+`.

Together with `small-degree-irreducible-bmw-parity-kernels-not-left-orderable`, this means that every
irreducible BMW group of degree (3,3), (4,3), (4,4) or (5,3) has a non-left-orderable parity kernel,
with those three possible exceptions.

**What was computed.** The (4,4) patterns with involutions are 40_40, 41_40, 41_41, 42_40 and 42_41;
42_42 was done earlier. The (5,3) patterns are all six.

| pattern | raw data | classes | reducible, R4 SAT | reducible, R4 UNSAT | candidates UNSAT at R4 | at R6 (short 4) | at R8 (short 4) | open |
|---|---|---|---|---|---|---|---|---|
| 40_40 | 444508 | 824 | 523 | 0 | 101 | 195 | 2 (#176, #256) | 3 |
| 41_40 | 34724 | 1242 | 1017 | 3 | 96 | 126 | 0 | 0 |
| 41_41 | 3212 | 544 | 480 | 4 | 27 | 33 | 0 | 0 |
| 42_40 | 20508 | 543 | 491 | 0 | 31 | 21 | 0 | 0 |
| 42_41 | 2980 | 551 | 505 | 0 | 28 | 18 | 0 | 0 |
| 50_30 | 186944 | 604 | 414 | 0 | 54 | 134 | 2 (#258, #470) | 0 |
| 50_31 | 18536 | 276 | 233 | 0 | 27 | 16 | 0 | 0 |
| 51_30 | 14848 | 662 | 532 | 2 | 52 | 76 | 0 | 0 |
| 51_31 | 1672 | 310 | 268 | 2 | 28 | 12 | 0 | 0 |
| 52_30 | 5056 | 389 | 351 | 0 | 27 | 11 | 0 | 0 |
| 52_31 | 680 | 202 | 184 | 0 | 16 | 2 | 0 | 0 |

- **Reducible classes.** These have both automaton images `⟨A⟩ → Aut(T_B)` and `⟨B⟩ → Aut(T_A)`
  certified finite. The pipeline caps the minimal automaton at 4000 states. `51_30#506` needed cap
  60000 (`bigcap.log`): its images have orders 6 and 6912.
- **Irreducible candidates.** Every one of the 1138 classes not certified reducible has an UNSAT
  positive-cone CNF for `Γ^+`, except the three open classes. CaDiCaL 1.5.3 and Glucose 4 agree on
  every instance.
  - For most classes radius 4 or radius 6 (one factor of length at most 4) suffices.
  - Four classes needed the radius-8 instance with one factor of length at most 4. For `40_40#176`
    and `#256` it has 5756592 clauses; for `50_30#258` and `#470` it has 11045771.
- **The three open classes.**
  - Their radius-8 (short 4) instances are SAT with both solvers, and so are their radius-10
    (short 2) instances, with 9373692 clauses.
  - They are not certified finite even at cap 60000.
  - Both local actions are `S_3` fixing one letter, so they are intransitive.
  - Their status is the OPEN claim `bmw-44-sat-survivor-parity-kernels-not-left-orderable`.

**By-products.**
- **Promislow-type classes.** Eleven more reducible classes have radius-4 UNSAT: `41_40#657`, `#925`,
  `#1174`; `41_41#480`, `#484`, `#486`, `#541`; `51_30#655`, `#657`; `51_31#277`, `#278`. Their
  parity kernels are torsion-free, virtually `F_k × F_l`, and not left-orderable.
- **Irreducible, locally 2-transitive on both factors.** The Thompson–Wielandt test
  (`irred_tw.py`, radius 3, tallied in `localact.log`) certifies 73 candidate classes as irreducible
  with 2-transitive local actions on both factors. There are 41 in degree (4,4) and 32 in (5,3). All
  of them are refuted, which is further evidence for
  `irreducible-tree-product-lattices-are-not-left-orderable` in these degrees.
- **Irreducible classes needing radius 8.** `40_40#176` and `#256` are Thompson–Wielandt-certified
  irreducible, each with one local action of order 24 (`S_4`, 2-transitive) and the other of order 2.
  Neither is refuted below radius 8.

**Scope.**
- The theorem says nothing about the three open classes, about proper finite-index subgroups of
  `Γ^+`, or about degree ≥ 5 other than (5,3).
- BMW lattices are not Kazhdan. Their bearing on Navas Question 3 is through Kazhdan groups
  containing `Γ^+`, as in `small-degree-irreducible-bmw-parity-kernels-not-left-orderable`.
