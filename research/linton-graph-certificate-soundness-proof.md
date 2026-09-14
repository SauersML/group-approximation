---
rg: 2
id: linton-graph-certificate-soundness-proof
kind: route
title: The certificate over-approximates Linton's graph of cyclic stabilisers, so its acyclicity gives Theorems 6.14 and 7.1
target: linton-graph-certificate-for-free-magnus-pieces
requires:
  - linton-z-stable-one-relator-hierarchy-theorem
  - rank-two-free-subgroups-are-strongly-inert
artifacts:
  - research/artifacts/one-relator-linton-graph-certificates-scripts/lintongraph.py
---

Notation as in the claim. Page numbers refer to Linton, arXiv:2202.11324v3 (PDF read locally,
pp. 2–4 and 23–31). Convention: `t a t^(-1) = psi(a)`, so `H cap t P t^(-1) = psi(P cap A)` and
`H cap t^(-1) P t = psi^(-1)(P cap B)` by Britton's lemma.

**Step 1 (hypotheses of Theorems 6.14 and 7.1).** `K` is free, hence hyperbolic. `A` and `B` are
finitely generated, hence quasi-convex in `K`. By (C0) they have rank 2, so they are strongly
inert (`rank-two-free-subgroups-are-strongly-inert`). By Remark 6.2, `G = K *_psi` is an inertial
one-relator extension. Since `W` is primitive in `F(a_0, a_1, a_2)` (the letter `a_1` occurs once),
this splitting is a one-relator hierarchy of length one ending in the free group `K`, exactly as in
Linton's Examples 1.2 and 6.12.

**Step 2 (segment stabilisers).** Let `S` be a geodesic segment of length `n >= 1` starting at the
vertex `K`, with first edge from `K` to `c t^e K` (`c in K`, `e = +-1`), and let `S'` be the translate
of the rest of `S` by `(c t^e)^(-1)`. Then `Stab(S) = c (K cap t^e Stab(S') t^(-e)) c^(-1)`, which is
`c psi(Stab(S') cap A) c^(-1)` for `e = 1` and `c psi^(-1)(Stab(S') cap B) c^(-1)` for `e = -1`. As `S'`
runs over the `K`-translates of segments of length `n - 1`, `Stab(S')` runs over the conjugates `P^h`
of the enumerated classes. The intersections `A cap P^h` up to `A`-conjugacy are given by the
positive-rank components of the pullback of the Stallings graphs of `A` and `P` (Stallings), and the
path is reduced unless it turns back through `h in A` (resp. `h in B`), which is the base component
when `P` lies in `A` (resp. `B`). So (C1) lists every class of stabilisers of segments of each
length with an endpoint at `K`. Restricted to one direction, the non-cyclic classes at depth `k` are
exactly `Abar_k` of the definition on p. 23, so (C1) computes `sZ(psi)` and gives `sZ(psi) < infinity`.

**Step 3 (vertices).** By the definition on p. 27, the vertex set of the graph of cyclic stabilisers
`G` is the set of classes `[<a>]_A` (resp. `[<b>]_B`) of maximal cyclic subgroups with
`A cap Stab(S) <= <a>` for some `S in S`, where `S` is the set of segments with an endpoint at `K`.
By Lemma 6.13 (p. 29), `G = G_(sZ(psi))`, so segments of length at most `sZ(psi)` suffice. For `S`
of that length, `A cap Stab(S)` ranges over the intersections of Step 2. When it is nontrivial
cyclic, the maximal cyclic subgroup of `A` containing it is unique. So `V` of (C2) contains every
vertex of `G`. The prose reading on p. 27 (maximal cyclic subgroups containing a cyclic stabiliser)
gives a subset of the same set. The extra depth in (C2) adds nothing, which is a consistency check on
this step.

**Step 4 (edges).** For `h in K`, `<nu(v)> cap <nu(w)>^h != 1` holds for some `h` exactly when
`nu(v)` and `nu(w)` have `K`-conjugate nontrivial powers, and for `v = w` with `h notin <nu(v)>`
exactly when `nu(v)` is a proper power in the free group `K`. For `h = a t^(-1) b` with `a in A`,
`b in B`: `h^(-1) nu(w)^k h = b^(-1) t (a^(-1) nu(w)^k a) t^(-1) b` lies in `K` only if
`nu(w)^k in A`, and then equals `b^(-1) psi(a)^(-1) psi(nu(w)^k) psi(a) b`, a `B`-conjugate of
`psi(nu(w)^k)`. So a t-edge of this type needs a nontrivial power of `nu(w)` in `A` whose image is
`B`-conjugate to a nontrivial power of `nu(v)`. In a free group this is the equality of the
`B`-classes of the maximal cyclic subgroups computed in (C3). The case `h in B t A` is symmetric
through `psi^(-1)`. So the graph of (C3) contains every edge of `G` of every type, with the same type,
and possibly more H-edges.

**Step 5 (no alternating words).** A cyclically alternating, cyclically reduced word of `pi_1(G)`
(p. 28) runs along a closed edge path in the underlying graph of `G` whose edge types alternate
cyclically, or along a single loop when it has length 1. Such a path is also a path of the graph in
(C3), with the same types. By (C3) there is none. So `pi_1(G)` admits no cyclically alternating,
cyclically reduced word.

**Step 6 (conclusion).** By Theorem 6.14, (3) implies (2): `G` contains no Baumslag–Solitar
subgroup. With `sZ(psi) < infinity`, the length-one hierarchy is Z-stable, so by Theorem 7.1, (3)
implies (1): the hierarchy is quasi-convex and `G` is hyperbolic, and by the Moreover clause `G` is
virtually special. QED

**Calibration** (artifact §3). The generator reproduces the landed row 29 graph (`X_A, U_A, U_B, Y_B`,
one H-edge, four t-edges), finds the Baumslag–Solitar subgroup of Linton's Example 6.12 as an
alternating 2-cycle, and computes `sZ(psi) = 3` for Example 1.2, as stated on p. 4.

_Orphan sweep (2026-09-14): this node cited `research/artifacts/one-relator-linton-graph-certificates-2026-09-13.md`, which its lane never wrote to the repository and which could not be recovered from the lane transcript._
