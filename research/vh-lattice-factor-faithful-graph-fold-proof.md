---
rg: 2
id: vh-lattice-factor-faithful-graph-fold-proof
kind: route
title: Split the lattice along either tree factor and fold its graph of groups onto the surjunctive target
target: vh-lattices-surjunctive-when-a-factor-maps-faithfully
requires:
  - graph-folds-over-surjunctive-groups-are-surjunctive
  - sofic-groups-are-surjunctive
artifacts:
  - research/artifacts/vh-lattice-table-hosts-2026-09-12.md
---

Section 9 of the artifact, Proposition G.

1. `Gamma` preserves vertical and horizontal edges, so it acts on the factor `T_H`,
   transitively on vertices. The base vertex of `T_H` is the vertical slice through the
   base point `o`, with vertices `F_V . o`. An element fixing it sends `o` to some `u . o`
   with `u in F_V`, and freeness makes it equal to `u`. So the stabilizer is `F_V`.
2. `Gamma` is torsion-free: a finite subgroup fixes a point of the CAT(0) complex
   `T_V x T_H`, and the action is free.
3. Bass–Serre theory, after subdividing edges of `T_H` that `Gamma` inverts, writes `Gamma`
   as the fundamental group of a graph of groups with injective edge maps. Its vertex
   groups are conjugates of `F_V` and, after subdivision, midpoint stabilizers `P`
   containing an edge stabilizer `Q <= F_V^g` with `[P : Q] <= 2`.
4. `f` is injective on each conjugate of `F_V`. On `P`, `ker f ∩ P` meets `Q` trivially, so it
   injects into `P / Q`, has order at most two, and is trivial by step 2.
5. `graph-folds-over-surjunctive-groups-are-surjunctive` makes `Gamma` surjunctive. The
   case of `F_H` uses `T_V`. The finite-residual consequence uses that the residually
   finite quotient `Gamma / Gamma_0` is sofic.
