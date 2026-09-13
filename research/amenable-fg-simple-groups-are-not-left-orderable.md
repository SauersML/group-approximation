---
rg: 2
id: amenable-fg-simple-groups-are-not-left-orderable
kind: claim
title: A finitely generated infinite simple amenable group is not left-orderable, so every action of it on the line or the circle is trivial
distinct_from:
  amenable-infinite-simple-circle-groups-fix-a-point: that shows an amenable infinite simple circle group fixes a point, with no finite generation; this adds finite generation and Witte Morris's theorem to exclude the remaining action on the line, and with it every nontrivial action on the circle
  hyde-lodha-periodic-simple-groups-are-not-amenable: that is a direct compression argument for Hyde–Lodha's periodic group Q_2; this is the general statement for every finitely generated simple group of homeomorphisms of the line
---

**ESTABLISHED.** Let `S` be a finitely generated infinite simple amenable group.
1. `S` is not left-orderable. In particular `S` has no faithful action on `R` by
   homeomorphisms.
2. Every action of `S` by homeomorphisms on `R` or on `S^1` is trivial.

**Consequences for `fp-infinite-simple-amenable-group`.** No example acts nontrivially
on a one-manifold. This removes:
- every finitely generated simple group of homeomorphisms of the line, including
  Hyde–Lodha's finitely presented `Q_n` and their finitely generated groups from
  quasi-periodic labellings;
- every simple group of homeomorphisms of the circle, including Thompson's `T` and
  Lodha's finitely presented circle group;
- every group that acts faithfully on one orbit of a flow by orientation-preserving
  homeomorphisms of that orbit (a dense orbit of a minimal flow suffices, by
  continuity).

**Model test.** `F'` is infinite, simple and left-orderable, and it is not finitely
generated, so the statement says nothing about its amenability, correctly. The
Juschenko–Monod groups `D([[phi]])` are finitely generated, infinite, simple and
amenable, and they contain torsion, so they are indeed not left-orderable.

Route: `amenable-fg-simple-groups-are-not-left-orderable-proof`.
