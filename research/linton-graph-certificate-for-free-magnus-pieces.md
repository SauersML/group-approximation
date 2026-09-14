---
rg: 2
id: linton-graph-certificate-for-free-magnus-pieces
kind: claim
title: A finite graph-of-cyclic-stabilisers certificate proves a two-generator one-relator group with a free rank-two Magnus piece hyperbolic and virtually special
distinct_from:
  linton-z-stable-one-relator-hierarchy-theorem: that imports Linton's criterion as stated; this is a checkable sufficient condition for it, built from Stallings pullbacks over a superset of the graph of cyclic stabilisers.
  row29-one-relator-group-is-hyperbolic-and-virtually-special: that settles one group by a hand-built graph; this is the general certificate that reproduces it and runs on whole census families.
- research/artifacts/one-relator-linton-graph-certificates-scripts/lintongraph.py
---

**ESTABLISHED** through `linton-graph-certificate-soundness-proof` (not independently reviewed).

**Setting.** `G = <a, t | w>`, with the exponent sum of `t` in `w` equal to 0. Write the Magnus
rewriting with `a_h = t^h a t^(-h)` as a cyclic word `W` in `a_0, ..., a_m` that uses `a_0` and
`a_m`, with the levels of `W` having gcd 1. Suppose `m = 2` and the interior letter `a_1` occurs in
`W` exactly once, with exponent `+-1`. Solve `W = 1` for `a_1 = u(a_0, a_2)`. Then

    G = K *_psi,  K = F(a_0, a_2),  A = <a_0, u>,  B = <u, a_2>,  psi(a_0) = u,  psi(u) = a_2.

**Certificate** (as computed by `lintongraph.py certify`):
- (C0) `A` and `B` are free on the displayed generators (their folded Stallings graphs have rank 2).
- (C1) Enumerate, depth by depth, the `K`-conjugacy classes of stabilisers of geodesic segments of
  the Bass–Serre tree with an endpoint at `K`: from a class `[P]` of depth `n`, the classes
  `[psi(A cap P^h)]` and `[psi^(-1)(B cap P^h)]` over all components of the Stallings pullbacks, with
  the base component removed at a back-turn. The non-cyclic classes reached by one direction only
  vanish from some depth on. The last depth with such a class, plus one, is `sZ(psi)` (resp.
  `sZ(psi^(-1))`), and the enumeration runs to depth `max sZ + 1`.
- (C2) `V` is the set of `A`-conjugacy classes of maximal cyclic subgroups of `A` containing a
  nontrivial cyclic `A cap Stab(S)^h`, and likewise for `B`, over all classes of depth at most
  `max sZ + 1`. No class first appears at depth `max sZ + 1`.
- (C3) On `V` put an H-edge between distinct `v, w` whenever their generators have `K`-conjugate
  nontrivial powers, an H-loop at `v` whenever its generator is a proper power in `K`, and a t-edge
  (possibly a loop) between `v` and `w` whenever some nontrivial power of `nu(w)` lies in `A` and its
  `psi`-image is `B`-conjugate to a nontrivial power of `nu(v)`, or the same through `B` and
  `psi^(-1)`. This graph has no loop of either kind and no closed path of length at least 2 whose
  edge types alternate cyclically.

**Claim.** If the certificate holds, then `G` contains no Baumslag–Solitar subgroup, its length-one
one-relator hierarchy is a quasi-convex hierarchy, and `G` is hyperbolic and virtually special.

_Orphan sweep (2026-09-14): this node cited `research/artifacts/one-relator-linton-graph-certificates-2026-09-13.md`, which its lane never wrote to the repository and which could not be recovered from the lane transcript._
