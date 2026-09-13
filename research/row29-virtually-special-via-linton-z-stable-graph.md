---
rg: 2
id: row29-virtually-special-via-linton-z-stable-graph
kind: route
title: Z-stable number two and a graph of cyclic stabilisers with no alternating cycle put row 29 in Linton's Theorem 7.1
target: row29-one-relator-group-is-hyperbolic-and-virtually-special
requires:
  - linton-z-stable-one-relator-hierarchy-theorem
  - rank-two-free-subgroups-are-strongly-inert
artifacts:
  - research/artifacts/one-relator-magnus-row29-2026-09-13.md
  - research/artifacts/one-relator-magnus-row29-scripts/lintonstab.py
  - research/artifacts/one-relator-magnus-row29-scripts/monocycles.py
  - research/artifacts/one-relator-magnus-row29-scripts/algext.py
  - research/artifacts/one-relator-magnus-row29-scripts/pb_AB.out
  - research/artifacts/one-relator-magnus-row29-scripts/pb_AA.out
  - research/artifacts/one-relator-magnus-row29-scripts/pb_BB.out
  - research/artifacts/one-relator-magnus-row29-scripts/monocycles.out
---

Notation as in the claim: `H = F(x,y)`, `A = <x,u>`, `B = <u,y>`, `u = y x^2 y^(-2) x`,
`psi(x) = u`, `psi(u) = y`, `G = H *_psi`, and `T` is the Bass–Serre tree.

**Step 0 (computed inputs, MSI outputs in the artifact).**
- (C1) Folded Stallings graphs. `Gamma_A` has 4 vertices and 5 edges, and `Gamma_B` has 5 and 6,
  so both have rank 2. The only monochromatic cycle of `Gamma_A` is the `x`-loop at the base, and
  the only one of `Gamma_B` is the `y`-loop at the base (`monocycles.out`). Reading words from the
  base: `x, u in A`, `y notin A`, `u, y in B`, `x notin B`. So the conjugates of powers of `y`
  lying in `A` are trivial, those of powers of `x` in `B` are trivial, and every conjugate of a
  power of `x` in `A` (resp. of `y` in `B`) is `A`-conjugate (resp. `B`-conjugate) into `<x>`
  (resp. `<y>`).
- (C2) Pullback `A x B`. The core has exactly one component of positive rank. It contains the base
  pair and has rank 1 (`pb_AB.out`). Since `u in A cap B` and `u` is not a proper power in `F`,
  `A cap B = <u>` and `A cap B^g = 1` for `g notin AB`.
- (C3) Pullbacks `A x A` and `B x B` have only the diagonal component (`pb_AA.out`, `pb_BB.out`),
  so `A` and `B` are malnormal in `H`.
- (C4) The script was fixed at the base vertex (`algext.py` keeps the root at 0). It reproduces the
  landed overgroup output, and on Linton's Example 6.15 it gives the expected rank 2 for `A cap B`.

**Step 1 (hypotheses).** `H` is free, hence hyperbolic. `A` and `B` are finitely generated, hence
quasi-convex in `H`: the universal cover of a core graph is a convex subtree of the Cayley tree,
within bounded distance of the orbit of its base vertex. By
`rank-two-free-subgroups-are-strongly-inert` both are strongly inert. By Linton's Remark 6.2,
`G = H *_psi` is an inertial one-relator extension, and the splitting is a one-relator hierarchy of
length one ending in a free group.

**Step 2 (Z-stable number).** `Abar_0 = {[H]}` and `Abar_1 = {[psi(A)]} = {[B]}`. `Abar_2` consists
of the non-cyclic classes `psi(A cap B^g)`. By (C2) every `A cap B^g` is cyclic or trivial, so
`Abar_2` is empty and `sZ(psi) = 2`.

**Step 3 (graph of cyclic stabilisers).** By Lemma 6.13, `G = G_2`, so only segments of length at
most 2 with an endpoint at `H` matter. Their stabilisers are:
- length 1: `c A c^(-1)` and `c B c^(-1)`, with `c in H`. Their intersections with `A` and `B` that
  are cyclic and nontrivial are `A cap B = <u>`, by (C2) and (C3).
- length 2, same direction: up to `H`-conjugacy, `psi(A cap B^g)` or `psi^(-1)(B cap A^g)`. By (C2)
  these are nontrivial only for `g in AB`, giving `psi(<u>) = <y>` and `psi^(-1)(<u>) = <x>`.
- length 2, opposite directions (reduced, so `g notin A`, resp. `g notin B`): `psi(A cap A^g)` or
  `psi^(-1)(B cap B^g)`. These are trivial by (C3).

By (C1), the vertex set is `X = [<x>]_A`, `U_A = [<u>]_A` (A-part) and `U_B = [<u>]_B`,
`Y = [<y>]_B` (B-part). Each generator is a basis element of its edge group, so none is a proper
power.

Edges, read literally from p. 27. There is an edge `v - w` for each double coset
`<nu(v)> h <nu(w)>` with `h in H` or `h in A t^-1 B u B t A` and `<nu(v)> cap <nu(w)>^h != 1`,
where `g^h = h^-1 g h`. When `v, w` lie in the same part, `h notin <nu(v)><nu(w)>` is also required.
- H-edges (`h in H`). The word `u` is cyclically reduced and uses both letters. So no nontrivial
  power of one of `x`, `u`, `y` is `H`-conjugate to a nontrivial power of another. If
  `nu(v) = nu(w) = c`, then `<c> cap <c>^h != 1` forces `h in <c>`. That is excluded when `v, w`
  lie in the same part, and gives the single double coset of `h = 1` for `{U_A, U_B}`. So the only
  H-edge is `U_A - U_B`, and there are no H-loops.
- t-edges. Take `h = a t^-1 b` with `a in A`, `b in B`. Then `<c>^h = b^-1 t a^-1 <c> a t^-1 b`.
  By Britton's lemma it meets `H` nontrivially only if some `c^k`, `k != 0`, lies in `A`, and then
  `(c^k)^h = b^-1 psi(a^-1 c^k a) b`. This is `B`-conjugate to `u^k` when `c = x` and to `y^k` when
  `c = u`, and `y` has no nonzero power in `A`. So `<nu(v)> cap <nu(w)>^h != 1` gives
  `w = X, v in {U_A, U_B}` or `w in {U_A, U_B}, v = Y`. The case `h in B t A` is symmetric through
  `psi^-1` and gives the same unordered pairs. So every t-edge joins `{X, Y}` to `{U_A, U_B}`.
  There are no t-loops, no t-edge `X - Y` and no t-edge `U_A - U_B`.

Linton's Figure 6 (p. 31) draws t-edges only between the A-part and the B-part, matched by `psi`.
Under that reading the t-edges are `X - U_B` and `U_A - Y`, and `Gamma(G)` is the path
`X -t- U_B -H- U_A -t- Y`. The literal reading adds `X - U_A` and `U_B - Y`, which create cycles.
Step 4 uses only the two bulleted facts, so it holds under either reading.

**Step 4 (no alternating cycles).** Let `e_1 ... e_n` be a cyclically alternating closed path.
- If `n = 1`, then `e_1` is a loop, and `Gamma(G)` has none.
- If `n >= 2`, the path never uses two t-edges in a row, so it contains an H-edge, namely
  `U_A - U_B`. The next edge is a t-edge and ends at `X` or `Y`. The edge after that must be an
  H-edge at `X` or `Y`, and there is none.

So `pi_1(G)` admits no cyclically alternating and cyclically reduced word.

**Step 5 (conclusion).**
- By Theorem 6.14, (3) implies (2), so `G` contains no Baumslag–Solitar subgroup.
- With `sZ(psi) = 2 < infinity`, the length-one hierarchy is Z-stable.
- By Theorem 7.1, (3) implies (1): `G` is hyperbolic, and by the "Moreover" clause virtually
  special.
