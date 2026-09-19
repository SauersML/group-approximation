---
rg: 2
id: fg-simple-mf-group-with-full-compression-defect
kind: claim
title: A finitely generated simple MF group has full compression defect, so the finite-generation survivor of the simple-defect collapse is dead
artifacts:
  - experiments/fg-simple-mf-defect-2026-09-17/check_three_lane_cell.py
distinct_from:
  simple-mf-group-with-full-compression-defect: that gives a countable simple MF group with full defect that is not finitely generated, and lists finite generation as a survivor; this gives a finitely generated one, so that survivor dies.
  fg-mf-group-with-full-compression-defect: that gives a finitely generated MF group with full defect that is not simple; this one is simple.
  nekrashevych-symmetric-and-alternating-full-groups: that imports simplicity and finite generation of A(G); this places a defect cell inside A(G) and proves A(G) is MF for one amenable free subshift.
---

**ESTABLISHED (written proof from established nodes; exact computer check
of the cell group; not Lean-verified).**  This is a counterexample to a
class of approaches.  `property-t-free-manuscript-results` stays OPEN.

Notation is that of `simple-mf-group-with-full-compression-defect`: a
*cell* is a triple `(u, c, l)` with `L = < u^k l u^-k : k >= 0 >`,
`u L u^-1 <= L`, `c in C(L)` and `[u c u^-1, l] != 1`.  MF means
operator-MF.

## Theorem

Let `Omega = Z x Z/3`.  Let `rho(i,j) = (i, j+1)` and
`t(i,j) = (i + d_j, j)` with `d = (1, 0, -1)`.  Let
`Delta = FAlt(Omega) x| <t, rho>`.  Let `X` be a free minimal subflow of
`2^Delta` and `G = Delta x| X` its action groupoid.  Then
`S = A(G)`, Nekrashevych's alternating full group, satisfies:

1. `S` is simple and finitely generated.
2. `S` is MF.
3. `Delta` embeds in `S`.  With `u = t`, `l = ((0,0),(1,0),(2,0))` and
   `c = ((-3,0),(-2,0),(-1,0))`, the triple `(u, c, l)` is a cell in `S`.
   So `D_S(L) = S` and `Rad_MF(S) = 1`.
4. `L` is locally finite, `u` has infinite order, and the cell lies in
   the elementary amenable subgroup `Delta`.

Derivation: `fg-simple-mf-group-with-full-compression-defect-proof`.

## What this kills

In `simple-mf-group-with-full-compression-defect`, a Kazhdan-free
replacement of the manuscript criterion is false whenever its hypotheses
hold for that countable group.  That group is not finitely generated, so
finite generation of the ambient group was listed as a survivor.

This theorem kills that survivor.  Every Kazhdan-free replacement whose
hypotheses are properties of `(S, L, u, c)` is false.  Those properties
include finite generation, simplicity, `D = S`, a locally finite `L`, an
infinite-order compressor and a cell inside an amenable subgroup.  The
invariant is the pair `(S, L)`.  Every member dies when the collapse is
specialized to `S`, because its conclusion `Rad_MF(S) = S` contradicts
the MF embedding.

The OPEN sub-question of Attempt 1 in the parent claim asked for a cell in
`D([[phi]])` of a minimal Z-subshift.  That question is no longer needed.
The obstruction met there was that disjoint supports die by Poincare
recurrence.  It does not apply here, because `c` and the `l_k` act freely on
`X`: each has full support there, and they commute through the algebra of
`Delta` rather than through disjoint supports.

**Survivors now.** The hypotheses that `S` does not satisfy, or is not
known to satisfy, are:

- finite presentation;
- torsion-freeness, since `S` contains `Alt(6)`;
- amenability of the ambient group, which is not known for `S` and not
  used;
- a spectral input on `L` or on the models;
- the ring data of the Leavitt and `EL_20` hosts.
