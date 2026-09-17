---
rg: 2
id: finitary-permanence-closures-collapse-boone-higman-to-base
kind: claim
title: Simple width survives extensions and finite graphs of groups, so permanence closures of a Boone--Higman class reach every decidable group only if the base class already does
distinct_from:
  decidable-edge-tower-premise-is-equivalent-to-boone-higman: that collapses closures under graph towers alone, through the FA wreath square of fg-perfect-wreath-c2-has-property-fa; this adds extensions, direct products, finite wreath products and graph products, needs no property FA, and uses established prerequisites only, so it re-proves that collapse as the special case with (R3) alone.
  fa-subgroups-of-graph-towers-lie-in-base-pieces: that moves one FA subgroup down a tower; this moves an unbounded family of commuting simple subgroups, none of which has FA, down extensions and finite graphs of groups through the S-width bound w(X) <= 1 + max w(Y_v).
  profinite-tree-hosts-make-fa-subgroups-residually-finite: that excludes one kind of host through the finite residual of FA subgroups; this excludes a kind of reduction, closure of a base class under permanence operations, through the simple width of the inputs.
  boone-higman-iff-infinite-simple-inputs: that shrinks the inputs of Boone--Higman to simple groups; this uses those simple inputs as probes that every finitary permanence operation must carry down to a base piece.
  compilers-cannot-drop-the-decidability-hypothesis: that shows permanence steps need decidable edge data; this shows that permanence steps of the finitary kinds add nothing toward Boone--Higman under any side conditions.
  boone-higman-type-a-class-closed-under-finite-extensions: that is one permanence property of the permutational class; this shows that such permanence properties, together with all finitary ones, cannot be the engine of a proof of Boone--Higman.
artifacts: []
---

**ESTABLISHED** through `finitary-permanence-closures-collapse-proof`.

## Definitions

For a nonabelian simple group `S`, the *S-width* of a group `X` is
`w_S(X) = sup { n : S^n embeds in X }`. For a class `C` of groups, the
following closures are used:
- `Fin(C)`: close `C` under subgroups, extensions (a group `X` with `N` and
  `X/N` in the class), and fundamental groups of graphs of groups over
  **finite** graphs;
- `Inf(C)`: close `C` under subgroups, extensions, arbitrary restricted or
  unrestricted direct products, and directed unions;
- `All(C)`: `Inf(C)` together with fundamental groups of arbitrary graphs of
  groups.

`C` *hosts* a class of groups if each group of that class embeds in a member of
`C`.

## Statements

Let `S` be finitely generated and infinite simple.

1. **Width bounds.**
   - `w_S(X) <= w_S(N) + w_S(X/N)`.
   - For a finite graph of groups, `w_S(π_1) <= 1 + max_v w_S(Y_v)`.

   Hence if every member of `C` has finite S-width, so does every member of
   `Fin(C)`.
2. **(A) Finitary collapse.** If `Fin(C)` hosts every finitely generated group
   with solvable word problem, then `C` does.
3. **(B) Infinitary collapse.** If `Inf(C)` hosts every finitely generated group
   with solvable word problem, then `C` does.
4. **(C) Mixed collapse on LEF inputs.** If `All(C)` hosts every finitely
   generated group with solvable word problem, then `C` hosts every finitely
   generated LEF group with solvable word problem, in particular every
   residually finite one.
5. **(D) Conditional mixed collapse.** If
   `decidable-groups-embed-in-decidable-simple-fa-groups` holds, then (C)
   holds for all finitely generated groups with solvable word problem.

## The invariant and where every such reduction dies

A *permanence reduction* of Boone--Higman takes a base class `C` of groups
that embed in finitely presented simple groups. It proves that embeddability
is preserved by some of the operations above, under any side conditions, and
concludes that every decidable group is hosted.

Such a reduction needs a probe: the decidable group `S wr Z`, where `S` is a
decidable infinite simple envelope of the input. Its S-width is infinite.
- **(A)** Extensions add widths and finite graphs of groups add at most one. So
  the reduction dies at the base, which must already contain all powers of
  `S`.
- **(B)** Infinitary operations are harmless for the same reason with a single
  copy of `S`: its intersection with a kernel, a coordinate or a term of a
  union is all or nothing.

In each case the permanence steps are idle. The base class `C` must already
host every decidable group, which is Boone--Higman for `C`.

This kills the following as engines toward `boone-higman-conjecture`, though
not as theorems:
- the open `boone-higman-closed-under-finite-direct-products`;
- `bh-embeddability-survives-decidable-edge-hnn`;
- the established permanence of the permutational class under finite
  extensions, graph products over finite graphs, common-retract amalgams,
  relative holomorphs and stable-permutation HNN extensions, in any
  combination (by (A));
- permutational wreath products, arbitrary products and directed unions, in
  any combination with extensions but without tree steps (by (B));
- combinations of all of these, for inputs that are LEF (by (C)).

## What survives

1. **Quotients.** Free groups lie in every Boone--Higman class, and every group
   is a quotient of one. A reduction to closure under one explicit operation
   must use a quotient-type step, such as passing to a simple quotient, or a
   compiler that is not a closure operation, such as the actor-orbit problems
   of twisted Brin--Thompson groups.
2. **Tree steps mixed with infinitary steps, for non-LEF inputs.** This gap is
   exactly `decidable-groups-embed-in-decidable-simple-fa-groups`. A decidable
   input all of whose decidable simple envelopes split as amalgams could be
   manufactured by a mixture such as `S = A *_C B` followed by
   `S wr Z`. The Burger--Mozes calibration in Step 8 of the proof shows that
   such mixtures do create simple subgroups from free pieces.
