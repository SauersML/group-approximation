---
rg: 2
id: accessible-non-virtually-cyclic-groups-carry-end-euler-measures
kind: claim
title: An infinite accessible group that is not virtually cyclic carries a right-invariant finitely additive measure on its end compactification giving every point mass one
distinct_from:
  one-ended-shell-inputs-admit-no-shift-normalizing-enumeration: that is a counting argument on the unique infinite component of a one-ended group; this is an invariant on the whole clopen algebra of the Freudenthal compactification, defined for every accessible group with any number of ends, and it fails exactly for the two-ended groups.
  accessible-half-tree-pieces-generate-end-clopen-algebra: that is only the topological step 3 of the route (the half-tree pieces and the finite sets generate the clopen algebra); this is the existence of the measure, which also needs the linear vertex equations.
  regular-enumeration-displacement-bounds-growth: that bounds growth through bounded displacement of the enumeration; the measure here is a finitely additive invariant and is insensitive to the enumeration.
artifacts:
  - experiments/window-zero-enumerations-2026-09-17/end_measure_check.py
---

**OPEN** (demoted 2026-09-17 by audit: referee lenses 1 and 2 refuted step 2
of `accessible-end-euler-measure-proof` when some vertex group is infinite.
The route now requires the open step-3 claim
`accessible-half-tree-pieces-generate-end-clopen-algebra`. See `## Attempts`).

Let `P` be an infinite finitely generated group with finite generating set
`S`, and let `Gamma` be the Cayley graph with edges `{y, gy}` for `g` in `S`.
Right multiplications are graph automorphisms of `Gamma`. Write
`Pbar = P ∪ ∂P` for the Freudenthal (end) compactification. Its clopen
subsets are exactly the closures of the subsets `U` of `P` with finite
coboundary in `Gamma`, together with the finite subsets of `P`.

An **end Euler measure** is a map `mu` from the clopen subsets of `Pbar` to
`Q` that is

- finitely additive,
- invariant under every right multiplication `y -> yd`, and
- equal to 1 on every singleton `{y}` with `y` in `P`.

**Theorem.** Suppose `P` is accessible, meaning it is the fundamental group
of a finite graph of groups with finite edge groups and vertex groups having
at most one end. This includes every finitely presented group (Dunwoody).
If `P` is not virtually cyclic, then `P` carries an end Euler measure.

- If `P` has one end, any value `T = mu(Pbar)` works:
  `mu(finite F) = |F|` and `mu(Pbar minus F) = T - |F|`.
- If `P` has infinitely many ends and some vertex group is infinite, again
  any `T` works.
- If every vertex group is finite (`P` virtually free), the measure exists,
  and every end Euler measure has `mu(Pbar) = 1/chi(P)`, where `chi` is the
  rational Euler characteristic.

The hypothesis cannot be dropped. For `P = Z`, finite additivity and
invariance of `[r, +infinity]` give
`mu([r, +infinity]) = 1 + mu([r+1, +infinity]) = 1 + mu([r, +infinity])`, so
no measure exists. The linear system of the route is also inconsistent for
`D_inf`, `Z x Z/2` and `Z/4 *_(Z/2) Z/4`, as checked by the script.

Example: `P = F_2` has `mu(Pbar) = -1 = 1/chi(F_2)`.

Groups that are finitely generated but inaccessible are not treated.

DERIVATION
accessible-end-euler-measure-proof

## Attempts

- **2026-09-17: direct proof via route `accessible-end-euler-measure-proof`
  (refuted by referees; kept as an attempt).** The route and the script
  `experiments/window-zero-enumerations-2026-09-17/end_measure_check.py`
  remain as the proof artifacts. The referees judged steps 4-6 (the linear
  system, `sum kappa_v = chi`, the forced total `1/chi`) and the one-ended case
  sound. The route now requires the open claim
  `accessible-half-tree-pieces-generate-end-clopen-algebra`, which is step 3.
  The referee reasons, verbatim:
  - Lens 1 (refuted=true): The proof breaks at step 2(a) of the route research/accessible-end-euler-measure-proof.md, in the multi-ended case where some vertex group is infinite. That case covers the theorem's "any T works" bullet. The virtually free and one-ended cases look fine.

    Step 2(a) says that orbit vertices v0.y and v0.y' at tree distance at most 2R0+1 "differ by one of finitely many G_(v0)-orbit types", so their fibres are within bounded word distance. That needs the Bass-Serre tree to be locally finite, and it is not when a vertex group G_w is infinite. Suppose v0 (a subdivided midpoint, with finite G0) is next to a vertex w with infinite G_w. Then the midpoints at distance 2 from v0 through w form one infinite G_w-orbit, so they fall into infinitely many G0-orbit types. The elements y'y^{-1} carrying v0 to those midpoints form an infinite set, so their word lengths are unbounded, and the bounded-distance claim is false. Chain connectivity of P_e may still hold, but this argument does not prove it.

    Step 2(b) has the same gap. It claims N_v = pi^-1(B_T(v,R1)) is a union of finitely many orbits y_i G_v. Take P = Z^2*Z^2*Z^2 with graph A-B-C, trivial edge groups, and edge A-B subdivided to give v0. At v = C you need R1 = 2 to reach v0.P through the B-neighbours, and the pairs (C-B edge, A-B midpoint at that B-vertex) form infinitely many G_C-orbits. So the orbit decomposition is infinite. The linking bound d(y_i h, y_j h) = |y_j y_i^-1| is then not uniform, so the step does not establish that N_v is L-chain connected or coarsely one-ended.

    Steps 3 and 4 use 2(a) and 2(b) to show that the P_e and the finite sets generate the whole clopen algebra, so that the measure is defined on every clopen set. That conclusion is therefore unsupported whenever a vertex group is infinite.

    The route imports nothing that would fill the gap: F1-F3 are only Dunwoody, basic Bass-Serre facts and chi facts. The script end_measure_check.py ran and passed, but it only checks the linear vertex/edge equations of steps 4-6, not the topology in steps 2-3. The route also requires no prerequisite claims, so there was nothing else to check.
  - Lens 2 (refuted=true): Refuted at route accessible-end-euler-measure-proof, Step 2 (coarse connectivity), which Step 3 (every clopen set lies in A) depends on. Both parts of Step 2 are argued with finiteness claims that only hold when the Bass-Serre tree is locally finite, meaning all vertex groups are finite. But the theorem claims more than that: it covers accessible groups with infinite one-ended vertex groups, and says any total T works for them.

    (1) Step 2(b) says N_v = pi^-1(B_T(v,R1)) is a finite union of right G_v-orbits y_i G_v, so it is coarsely one-ended. This is false. Counterexample: P = A*B*C with each factor Z^2, graph of groups the path A-B-C with trivial edge groups, the A-B edge orbit subdivided, and v = the C-vertex. The branch at v through the B-vertex Bc reaches its nearest orbit point, the midpoint m_{bc}, only at distance 2, so R1 >= 2. Then N_v contains BC = {bc}. That set has infinitely many right C-orbits (bC, one for each b in B). It is also not coarsely one-ended. For |b| > L, the distance from b to b'c with c != 1 is |b'cb^-1| >= |b| > L. So B minus a ball is an infinite L-chain component separate from the infinite C-part. The fact actually true here is that G_v has finitely many orbits of incident edges, not of vertices within radius R1 >= 2.

    (2) Step 2(a) says orbit vertices at tree distance <= 2R0+1 differ by one of finitely many G_(v0)-orbit types, so a short representative g_i exists. G_(v0) is finite and the tree is not locally finite, so there are infinitely many such vertices and the word lengths are unbounded. For example, v0.h with h in an infinite G_w adjacent to v0 is at tree distance 2. So no uniform L follows.

    Step 3 uses 2(a) to put each P_e wholly inside or outside U, and 2(b) to make almost all branches at an infinite vertex follow one side. So the identification of the clopen algebra with A, and with it the well-definedness of mu on all clopen sets, is not proven in the infinite-vertex case. The statements are probably repairable, for example by choosing v0 and R1 more carefully, or by proving coarse connectivity of half-spaces with a different argument. As written, though, the step is unfilled and one of its lemmas is false.

    The theorem is fine elsewhere. The one-ended case, Step 5 (linear algebra, sum kappa_v = chi) and Step 6 (the total forced to 1/chi) check out. The script experiments/window-zero-enumerations-2026-09-17/end_measure_check.py runs and passes, but it only tests the linear system. Its infinite-vertex examples are Z^2*Z, Z^2*Z/2 and Z^2*Z^2, all with the one-ended vertex next to the midpoint, so none of them exercises Step 2 or 3. The claim also says of itself that it was not independently reviewed.
