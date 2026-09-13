---
rg: 2
id: thompson-t-orbits-carry-no-invariant-means
kind: claim
title: Finite point sets of the circle are uniformly non-invariant under Thompson's T
distinct_from:
  thompson-v-cantor-orbits-have-no-folner-sets: that is the same uniform isoperimetric bound for Thompson's V on the Cantor set, proved with prefix transpositions; this is the circle bound for T, which has no transpositions and uses a rotation instead.
  thompson-v-covariant-cantor-representations-are-not-amenable: that excludes Bekka-amenable covariant Cantor representations of V; this proves the analogous exclusion for covariant circle representations of T.
  no-proper-character-groups-avoid-amenable-orbit-full-groups: that shows T acts trivially inside measure-preserving amenable orbit full groups, through characters; this is a counting statement about T's own circle action and uses no characters.
---

**ESTABLISHED.** Write `S^1 = R/Z` and let `T` act by its piecewise-linear dyadic
homeomorphisms. Three elements of `T` are used:
- the rotations `r_(1/4)(x) = x + 1/4` and `r_(1/2)(x) = x + 1/2`;
- the element `x_0`, with `x_0(x) = x/2` on `[0,1/2)`, `x_0(x) = x - 1/4` on `[1/2,3/4)`,
  and `x_0(x) = 2x - 1` on `[3/4,1)`. It is increasing on `[0,1)`, fixes `0` and maps
  `[0,1/2)` onto `[0,1/4)`.

Let `X` be a finite symmetric subset of `T` generating a subgroup that contains these
three elements, and let `L` be the largest word length of the three in `X`.

1. **Uniform boundary.** Every finite nonempty `F ⊆ S^1` satisfies
   ```text
   max_(s in X) |sF symmetric-difference F|  >=  |F| / (7L).          (TC1)
   ```
   So no union of orbital Schreier graphs of `T` on the circle is amenable, and truncating
   the circle action of `T` to finite point sets, then correcting a vanishing fraction of
   points, never gives a sofic approximation of `T`.
2. **No invariant measure, no amenable covariant representation.** There is no
   `x_0`- and rotation-invariant Borel probability measure on `S^1`. Consequently, if
   `pi` is a unitary representation of `T` on `H` and `rho : C(S^1) -> B(H)` is a unital
   `*`-homomorphism with `pi(g) rho(f) pi(g)^* = rho(f o g^(-1))`, then there are no
   nonzero finite-rank projections `P` with
   `||pi(g) P pi(g)^* - P||_HS / ||P||_HS -> 0` for all `g` in `X`. No normalized-HS model
   of `T` is a compression of a covariant circle representation.

This is the circle counterpart of `thompson-v-cantor-orbits-have-no-folner-sets` and
`thompson-v-covariant-cantor-representations-are-not-amenable`. It kills, for `T`, the
spatial truncation and covariant compression routes recorded dead for `V`. Any sofic or
hyperlinear model of `T` has to be non-spatial.

No novelty is claimed: the argument is the standard halving computation behind the
non-amenability of the circle action.

Proof: `thompson-t-orbit-invariant-mean-halving-proof`.
