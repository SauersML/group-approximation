---
rg: 2
id: minimal-torsion-free-small-tree-lattices-not-left-orderable
kind: claim
title: Every irreducible torsion-free type-preserving lattice with four vertex orbits in Aut(T_3)xAut(T_3) or Aut(T_3)xAut(T_4) is not left-orderable
distinct_from:
  small-degree-irreducible-bmw-parity-kernels-not-left-orderable: that treats parity kernels of vertex-transitive (BMW) lattices; here every lattice of minimal covolume among torsion-free type-preserving ones is covered, and 1 of the 11 classes in degree (3,3) and 15 of the 98 classes in degree (3,4) are not parity kernels of any BMW group, among them 8 irreducible candidates in degree (3,4)
  irreducible-tree-product-lattices-are-not-left-orderable: that is the OPEN class-wide statement for boundary-2-transitive local actions; this is an exhaustive census of one covolume, with arbitrary local actions
  exotic-c2-tilde-simple-kazhdan-lattices-are-not-left-orderable: that certifies Radu's (3,3) complex; its parity kernel is class 6 of the (3,3) census here
artifacts:
  - experiments/bmw-census-left-orders-2026-09-17/README.md
  - experiments/bmw-census-left-orders-2026-09-17/cx4.py
  - experiments/bmw-census-left-orders-2026-09-17/census_cx4_33.json
  - experiments/bmw-census-left-orders-2026-09-17/out_cx4_33.jsonl
  - experiments/bmw-census-left-orders-2026-09-17/cx4_parity.py
  - experiments/bmw-census-left-orders-2026-09-17/cx4_parity.log
  - experiments/bmw-census-left-orders-2026-09-17/cxmn.py
  - experiments/bmw-census-left-orders-2026-09-17/crosscheck_cx.py
  - experiments/bmw-census-left-orders-2026-09-17/crosscheck_cx.log
  - experiments/bmw-census-left-orders-2026-09-17/summarize_cx.py
  - experiments/bmw-census-left-orders-2026-09-17/summarize_cx.log
  - experiments/bmw-census-left-orders-2026-09-17/census_cx_33.json
  - experiments/bmw-census-left-orders-2026-09-17/census_cx_34.json
  - experiments/bmw-census-left-orders-2026-09-17/out_cx_34.jsonl
  - experiments/bmw-census-left-orders-2026-09-17/err_cx_34.log
  - experiments/bmw-census-left-orders-2026-09-17/cxmn_parity.py
  - experiments/bmw-census-left-orders-2026-09-17/cxmn_parity.log
---

**ESTABLISHED (computer-certified: exhaustive enumeration checked against brute force, two
agreeing SAT solvers, automaton finiteness certificates).** Proof:
`minimal-torsion-free-small-tree-lattices-not-lo-proof`.

**Setting.**
- A lattice `Γ ≤ Aut(T_m) × Aut(T_n)` is *type-preserving* if it preserves the bipartition of both
  trees. Then the product has four vertex types `(i,j) ∈ {0,1}^2`.
- If `Γ` is also torsion-free, it acts freely on vertices, so it has at least four vertex orbits.
  *Minimal covolume* means exactly four orbits, one per type.
- Equivalently, `Γ = π_1 X` for a square complex `X` with four vertices `(i,j)`:
  - `m` horizontal edges `(0,j)–(1,j)` in each row `j`;
  - `n` vertical edges `(i,0)–(i,1)` in each column `i`;
  - squares such that every vertex link is `K_{m,n}`.
- `Γ` is *irreducible* if it has no finite-index subgroup of the form `Λ_1 × Λ_2` with
  `Λ_1 ≤ Aut(T_m)` and `Λ_2 ≤ Aut(T_n)`.

**Theorem.** Let `(m,n) ∈ {(3,3), (3,4)}`. Every irreducible torsion-free type-preserving lattice
in `Aut(T_m) × Aut(T_n)` with four vertex orbits is not left-orderable. Hence no group containing
such a lattice is left-orderable.

**What was computed.** Classes of degree (3,3) are numbered as in `census_cx4_33.json`, and classes of
degree (3,4) as in `census_cx_34.json`.

| degree | normalized data | classes | certified reducible | irreducible candidates | UNSAT at R4 | UNSAT at R6, short 4 | UNSAT at R8, short 2 |
|---|---|---|---|---|---|---|---|
| (3,3) | 244 | 11 | 9 | 2 | 1 | 1 | 0 |
| (3,4) | 7584 | 98 | 64 | 34 | 13 | 20 | 1 |

- **Enumeration.** Data are counted after normalizing two label sets. The backtracker agrees with
  brute force, and the class orbits partition the data (`crosscheck_cx.py`). In degree (3,3) the
  normalized count, multiplied by `3!·3!`, reproduces the 8784 data of the independent
  enumerator `cx4.py`, which yields the same 11 classes.
- **Reducible classes.** Both automaton images, of the horizontal loop group on `T_n` and of the
  vertical loop group on `T_m`, are certified finite, with order at most 108.
- **Irreducible candidates.** Every candidate has an UNSAT positive-cone CNF, and CaDiCaL 1.5.3 and
  Glucose 4 agree on every instance.
  - The hardest is class `(3,4)#72`. It is SAT at radius 6 with all products (2227 elements,
    256590 clauses) and UNSAT at radius 8 with one factor of length at most 2 (20935 elements,
    250530 clauses).
- **No survivor.** Among lattices of minimal covolume in these degrees, no irreducible lattice has a
  positive-cone SAT instance that stays satisfiable as the ball grows.

**Relation to the BMW census.**
- The parity kernel of a BMW group of degree `(m,n)` is `π_1` of a four-vertex complex.
- `cx4_parity.py` maps all 60 BMW classes of degree (3,3) into the (3,3) census:
  - they hit classes `0`–`9`;
  - Radu's `Γ_R` gives class 6;
  - `30_30#16`, `31_30#26` and `31_31#12` give class 9.
- `cxmn_parity.py` maps all 639 BMW classes of degree (4,3) into 83 of the 98 classes of degree
  (3,4). Classes `19, 20, 39, 40, 42, 44, 56, 72, 73, 76, 78, 79, 81, 92, 95` are not parity
  kernels of any BMW group.
- In both maps the certified-reducible verdicts of the two censuses agree class by class. The
  finiteness computations are independent, one on the one-vertex complex and one on the
  four-vertex complex.
- New lattices in this theorem:
  - `(3,3)#10`, which is reducible;
  - the eight irreducible candidates `(3,4)#20, 40, 56, 72, 73, 76, 78, 92`, none of which is
    the parity kernel of a BMW group.

**By-product.** The reducible classes `(3,3)#10` (image orders 6 and 6), `(3,4)#44` (8 and 12),
`(3,4)#81` (6 and 6) and `(3,4)#97` (8 and 12) are already UNSAT at radius 4. Each is a torsion-free
lattice that is virtually a product of free groups and is not left-orderable.

**Relevance to Navas Question 3.**
- This extends the negative answer from vertex-transitive lattices to all minimal-covolume
  torsion-free lattices in the two smallest degrees.
- A left-orderable Kazhdan group built from an irreducible `T_3 × T_3` or `T_3 × T_4` lattice
  cannot contain a lattice of minimal covolume.
- The remaining room in these degrees is lattices with more vertex orbits. A proper finite-index
  subgroup of a non-left-orderable group can still be left-orderable, so this theorem says nothing
  about them.
