---
rg: 2
id: asymmetric-twist-descent-proof
kind: route
title: Empty reverser transporter plus overlap at most two against translation four closes the ping-pong
target: asymmetric-twist-descends-to-congruence-hnn-enemy
requires:
  - swap-twist-centralizer-is-the-congruence-core
  - hnn-hyperlinearity-is-amalgamated-free-haar-unitary
---

Notation: `T` the Bass--Serre tree of `E`, `v_0 = Gamma`,
`u_0 = Lambda x <s>`, `s_g = g s g^(-1)`.  The congruence description of
`C_0(g)` is the entry computation with `(a_1,a_2,a_3) = (2,-1,-1)`:
below-diagonal costs are `p^3 | x_21, p^3 | x_31, p^0 | x_32`, so
`C_0(g) supseteq Lambda(p^3)` and co-density follows from strong
approximation at levels coprime to `p`.

**Step 1 (imported).**  Exactly as in
`swap-twist-centralizer-proof` with `g` for `h`: `Fix(s) = {u_0}`,
`Fix(s_g) = {g u_0}`, distance `2` through `v_0`; `z_g` is hyperbolic of
translation length `4` with axis `l` through `u_0, v_0, g u_0`;
`C_Gamma(z_g) = C_0(g)`; `s` reflects `l` about `u_0` and `s_g` about
`g u_0`; the type-2 vertices of `l` are `Omega = <z_g>{u_0, g u_0}`.

**Step 2 (no reverser, and no shifted transports).**  For `x in Gamma`
and `a, b` integers, `x z_g^a lambda z_g^(-b) in Gamma` with
`lambda in Lambda`-type letters forces, by amalgam length reduction, the
cancellation of every `s`-letter; the only cancellations available pass
through `s lambda' s = lambda'` (`lambda' in Lambda`) and terminate, and
a `z_g`-power in `Gamma` forces the power zero (`z_g^k` has reduced
length `4|k| >= 4`).  Concretely: the transporter of `u_0` to `g u_0`
inside `Gamma` is `g Lambda`, of `g u_0` to `u_0` is `Lambda g^(-1)`,
and a reverser of the adjacent pair `{u_0, g u_0}` would lie in
`g Lambda cap Lambda g^(-1)`.  If `g lambda = mu g^(-1)` then
`g lambda g = mu in Lambda`, so the Cartan cells of `g` and `g^(-1)`
coincide; but they are `(2,-1,-1)` and `(1,1,-2)`.  Empty.  Likewise any
transport involving a nonzero `z_g`-shift lies in `z_g^k (Lambda x <s>)`
cosets with `k != 0`, disjoint from `Gamma`.

**Step 3 (overlap bound).**  Let `x in Gamma - C_0(g)`.  The overlap
`l cap x l` is a segment through `v_0` (trees: intersections of
geodesics are connected; `x` fixes `v_0`).  Its type-2 vertices are
vertices `q in Omega` with `x^(-1) q in Omega`; by Step 2 only the
unshifted transports survive, so the candidates are: `x` fixes `u_0`
(`x in Lambda`), fixes `g u_0` (`x in g Lambda g^(-1)`), maps
`u_0 -> g u_0` (`x in g Lambda`), or `g u_0 -> u_0`
(`x in Lambda g^(-1)`).  Fixing both is `C_0(g)`, excluded; swapping
both needs the empty reverser transporter.  In each surviving case the
overlap extends exactly one step past the surviving type-2 vertex (by
the reflection identities: for `x in Lambda`, `x` fixes
`s v_0` since `x` commutes with `s`; the next vertex `s g u_0` requires
`x in g Lambda g^(-1)`, excluded), so

```text
diam(l cap x l) <= 2  for every x in Gamma - C_0(g).      (AT1)
```

**Step 4 (ping-pong).**  Let `W = x_0 z^(k_1) x_1 ... z^(k_j) x_j` be
Britton-reduced (`k_i != 0`, interior `x_i in Gamma - C_0(g)`).  Claim,
by downward induction on the suffix: after applying a suffix ending in
`z^(k_i)`, the image of `v_0` is at distance `>= 2` from `v_0` and the
geodesic back to `v_0` leaves `v_0` along `l` in the direction of
`sign(k_i)` for at least `4 - 2 = 2` edges.  Prepending `x_(i-1)`
preserves the distance and rotates the departure direction to a
direction whose maximal initial run along `l` is at most `2` by
`(AT1)`.  Prepending `z^(k_(i-1))` adds `4|k_(i-1)| >= 4` of travel
along `l` against a backtrack of at most `2`, so the distance stays
`>= 2` and the departure direction resets to `sign(k_(i-1))`, restoring
the invariant.  Hence `W v_0 != v_0`, so `W notin Gamma`; in particular
`W != e` and `W notin C_0(g)`.  This is Britton injectivity for the
marked map, and words beginning or ending with `z`-powers are the same
computation with one fewer rotation.

**Step 5 (von Neumann consequence).**  The subgroup
`<Gamma, z_g> <= E` is now the marked amalgam
`Gamma *_(C_0(g)) (C_0(g) x Z)`, and the canonical trace of `E`
restricts on a subgroup to its regular trace.  By the group-amalgam
freeness mechanism of `hnn-amalgamated-free-haar-unitary-proof`
(Britton normal form is amalgamated freeness), in every canonical
tracial model of `E` the pair `(W*(pi(Gamma)), W*(L(C_0(g)), z_g))` is
free with amalgamation over `L(C_0(g))` and `z_g` is a Haar unitary
there.  Restricting a canonical model of `E` to this subgroup is a
canonical model of `G'_g`.
