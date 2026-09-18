---
rg: 2
id: small-degree-irreducible-bmw-parity-kernels-not-left-orderable
kind: claim
title: Every irreducible BMW lattice of degree (3,3), (4,3) or torsion-free (4,4) has a non-left-orderable parity kernel
distinct_from:
  irreducible-tree-product-lattices-are-not-left-orderable: that is the OPEN class-wide statement for lattices with boundary-2-transitive dense projections, approached through Deroin–Hurtado; this settles, by exhaustive enumeration and SAT certificates, every vertex-transitive lattice of small degree, whatever its local actions are
  exotic-c2-tilde-simple-kazhdan-lattices-are-not-left-orderable: that certifies two named complexes (Radu's (3,3) complex and Janzen–Wise); here they are two of the 62 irreducible-candidate classes, recovered by identify.py
  rattaggi-simple-lattices-are-not-left-orderable: that treats Rattaggi's simple lattices of large degree through commutator collapse; this treats all one-vertex complexes of small degree
  radu-simple-six-six-lattices-are-not-left-orderable: that treats Radu's (6,6) lattices; this is the complete small-degree census
artifacts:
  - experiments/bmw-census-left-orders-2026-09-17/README.md
  - experiments/bmw-census-left-orders-2026-09-17/vh_enum.py
  - experiments/bmw-census-left-orders-2026-09-17/crosscheck_33.py
  - experiments/bmw-census-left-orders-2026-09-17/crosscheck_33.log
  - experiments/bmw-census-left-orders-2026-09-17/lo_census.py
  - experiments/bmw-census-left-orders-2026-09-17/selfcheck.py
  - experiments/bmw-census-left-orders-2026-09-17/selfcheck_1.log
  - experiments/bmw-census-left-orders-2026-09-17/identify.py
  - experiments/bmw-census-left-orders-2026-09-17/summarize.py
  - experiments/bmw-census-left-orders-2026-09-17/run_all.sh
  - experiments/bmw-census-left-orders-2026-09-17/census_30_30.json
  - experiments/bmw-census-left-orders-2026-09-17/census_31_30.json
  - experiments/bmw-census-left-orders-2026-09-17/census_31_31.json
  - experiments/bmw-census-left-orders-2026-09-17/census_40_30.json
  - experiments/bmw-census-left-orders-2026-09-17/census_41_30.json
  - experiments/bmw-census-left-orders-2026-09-17/census_41_31.json
  - experiments/bmw-census-left-orders-2026-09-17/census_42_30.json
  - experiments/bmw-census-left-orders-2026-09-17/census_42_31.json
  - experiments/bmw-census-left-orders-2026-09-17/census_42_42.json
  - experiments/bmw-census-left-orders-2026-09-17/out_30_30.jsonl
  - experiments/bmw-census-left-orders-2026-09-17/out_31_30.jsonl
  - experiments/bmw-census-left-orders-2026-09-17/out_31_31.jsonl
  - experiments/bmw-census-left-orders-2026-09-17/out_40_30.jsonl
  - experiments/bmw-census-left-orders-2026-09-17/out_41_30.jsonl
  - experiments/bmw-census-left-orders-2026-09-17/out_41_31.jsonl
  - experiments/bmw-census-left-orders-2026-09-17/out_42_30.jsonl
  - experiments/bmw-census-left-orders-2026-09-17/out_42_31.jsonl
  - experiments/bmw-census-left-orders-2026-09-17/out_42_42.jsonl
---

**ESTABLISHED (computer-certified: exhaustive enumeration, two agreeing SAT solvers, automaton
finiteness certificates).** Proof: `small-degree-bmw-parity-kernels-not-left-orderable-proof`.

**Setting.** A *BMW group of degree (m,n)* is a group `Γ ≤ Aut(T_m) × Aut(T_n)` acting simply
transitively on the vertices of `T_m × T_n` without swapping the factors. Equivalently, `Γ` is the
fundamental group of a one-vertex square complex whose link is the complete bipartite graph
`K_{m,n}`. Its *parity kernel* `Γ^+` is the index-4 subgroup of elements with even horizontal and
even vertical length. `Γ^+` is torsion-free and preserves the vertex types of both trees. `Γ` is
*reducible* if it has a finite-index subgroup `Λ_1 × Λ_2` with `Λ_i ≤ Aut(T_i)`, and *irreducible*
otherwise.

**Theorem.** Let `Γ` be an irreducible BMW group of degree (3,3) or (4,3), or a torsion-free
irreducible BMW group of degree (4,4). Then `Γ^+` is not left-orderable. Hence no group containing
`Γ^+` is left-orderable.

**What was computed.**
- Every datum is enumerated, for every involution pattern of the letters. Classes are taken up to
  relabelling, inversion (`Γ ≅ Γ^op`) and factor swap. The backtracking count is checked against
  brute force over all `9!` bijections in degree (3,3).

  | degree, pattern | raw data | classes | certified reducible | irreducible candidates |
  |---|---|---|---|---|
  | (3,3), all patterns | 610 | 60 | 56 | 4 |
  | (4,3), all patterns | 10908 | 639 | 589 | 50 |
  | (4,4), torsion-free | 1564 | 118 | 110 | 8 |

- **Reducible classes.** For 755 of the 817 classes, both "letter automaton" images, `⟨A⟩` in
  `Aut(T_B)` and `⟨B⟩` in `Aut(T_A)`, are certified finite (order at most 108). That makes `Γ`
  virtually `N_A × N_B` with `N_A`, `N_B` free.
- **Irreducible candidates.** For every one of the 62 remaining classes, the positive-cone CNF of
  `Γ^+` is UNSAT. Radius 4 suffices for 32 classes, while 30 need radius 6 with one factor of
  length at most 4. CaDiCaL and Glucose agree on every instance.
- **No survivor.** The census contains no left-orderable irreducible candidate: the search for a
  lattice whose positive-cone SAT stays satisfiable as the ball grows ends negatively in these degrees.
- **Calibration.**
  - Radu's all-involution (3,3) complex is class `30_30#10` (UNSAT at radius 6 with short factors
    of length 4). Janzen–Wise is class `42_42#98` (UNSAT at radius 4). This matches
    `exotic-c2-tilde-simple-kazhdan-lattices-are-not-left-orderable`.
  - The commuting product complexes are certified reducible, and their radius-4 CNFs are SAT, as
    they must be for `F × F`.

**By-product.** Two reducible classes, `41_30#172` (image orders 6 and 8) and `41_31#107` (image
orders 6 and 4), already have radius-4 UNSAT. Their parity kernels are torsion-free, virtually
`F_k × F_l`, and not left-orderable. They are Promislow-type examples commensurable with a product
of free groups.

**Relevance to Navas Question 3.**
- BMW lattices themselves are not Kazhdan. But they embed in Kazhdan groups: Titz Mite–Witzel
  C~2 lattices contain the parity kernel of Radu's complex
  (`radu-bmw-lattice-embeds-in-titz-witzel-kernel`).
- The theorem kills every construction of a left-orderable Kazhdan group that contains the parity
  kernel of a small-degree irreducible BMW lattice. It does so irrespective of local actions,
  including those that are not 2-transitive, which lie outside
  `irreducible-tree-product-lattices-are-not-left-orderable`.
- Only reducible pieces, virtually `F × F`, survive in these degrees.
- It says nothing about proper finite-index subgroups of `Γ^+`, or about degree ≥ 5.
