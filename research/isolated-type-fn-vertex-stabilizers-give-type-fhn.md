---
rg: 2
id: isolated-type-fn-vertex-stabilizers-give-type-fhn
kind: claim
title: "A cocompact action on an (n-1)-acyclic complex whose only nontrivial stabilizers are isolated type F_n vertex groups gives FH_n"
distinct_from:
  proper-and-free-type-fhn-coincide: that claim replaces finite stabilizers; this replaces infinite vertex stabilizers of type F_n acting freely on the links of isolated vertices
  fn-groups-mod-acyclic-normal-subgroups-are-type-fhn: that claim starts from a presentation Q/P with acyclic kernel; this starts from a geometric action with singular vertices
artifacts:
  - research/artifacts/zp-fpn-fhn-2026-09-13-part3.md
---

Let `n ≥ 2`. Suppose `G` acts cellularly, with finitely many orbits of cells,
on an `(n−1)`-acyclic CW complex `X`. Let `V` be a `G`-invariant set of
vertices with the following properties.

1. Every cell of `X` outside `V` has trivial stabilizer.
2. Each `v ∈ V` has a closed subcomplex neighbourhood `N_v`, with
   `gN_v = N_{gv}`, pairwise disjoint.
3. `N_v` is `G_v`-equivariantly and cellularly the cone, with cone point
   `v`, on a free `G_v`-CW complex `Lk_v` with finitely many orbits of cells.
4. Each stabilizer `G_v` is finitely presented and of type `FP_n`, i.e. of
   type `F_n`.

Then `G` acts freely, with finitely many orbits of cells, on an
`(n−1)`-acyclic CW complex. That is, `G` is of type `FH_n`.

Proof sketch (artifact part 3, Proposition V):
- Build an `(n−1)`-connected free cocompact `G_v`-complex `E_v ⊇ Lk_v`:
  - attach finitely many orbits of 1-cells to connect;
  - attach finitely many orbits of 2-cells along normal generators of the
    kernel `π_1(Lk_v/G_v) ↠ G_v`, which is finitely normally generated because
    `G_v` is finitely presented;
  - kill `H_2, …, H_{n−1}` with finitely many orbits of spherical cells,
    using Hurewicz and Lemma S with `FP_n`.
- Replace each cone `N_v` by the mapping cylinder of `Lk_v ↪ E_v`. By
  Mayer–Vietoris and the five lemma, homology in degrees `≤ n−1` is
  unchanged.

This is a geometric, `FH_n`-level version of Brown's criterion for
isolated singular vertices.
