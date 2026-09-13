# Obstructions for subgroups of F, part 2: Z ≀ Z^2 is not a subgroup of F

Lane z2-15b-biorderable, 2026-09-13. Uses Lemma A, Lemma B and the slope conventions of
`research/artifacts/zp-pl-interval-subgroup-obstructions-2026-09-13-part1.md`.

## Statement

**Theorem N4.** The wreath product `G = Z ≀ Z^2` is isomorphic to no subgroup of
Thompson's group `F`. More generally, it is isomorphic to no subgroup of `PL_+(I)` in which
every right derivative at a fixed point lies in a fixed cyclic subgroup `<μ>` of
`R_{>0}`.

`Z ≀ Z^2` is bi-orderable. Order `Z^2` lexicographically. This order is invariant under
translation. Order the base `⊕_{v in Z^2} Z` by the sign of the coordinate at the largest
index where two elements differ. Translations preserve that order, so the lexicographic
order on `base ⋊ Z^2`, with the top coordinate first, is a bi-order. `G` is metabelian,
so it has no non-abelian free subgroup.

## Proof

Write `Q = Z^2 = <s, t>` and `M = ⊕_{v in Q} Z e_v`, a free `Z[Q]`-module of rank one on
`a = e_0`, with `Q` acting by conjugation. Suppose `G ≤ PL_+(I)` with slopes at fixed points
in `<μ>`. For `v` in `Q`, write `a_v = v a v^{-1}`, which is the element `x^v · a` in
module notation. All `a_v` commute.

**Step 1 (the bump family).** By Lemma A, a bump of `a_v` and a bump of `a_w` are equal
or disjoint. Let `𝓑` be the set of all bumps of all `a_v`. `Q` permutes `𝓑`, because
`v` maps the bumps of `a_w` onto the bumps of `a_{v+w}`. Every element of `M` is a
product of lamps `a_w`. Each lamp either has `B` in `𝓑` as a bump (and preserves it) or
is the identity on `B`, since `B` is disjoint from all its bumps. So every element of `M`
preserves every `B` in `𝓑` and is the identity outside `∪𝓑`.

**Step 2 (stabilizers are nonzero).** Let `E` be the set of bumps of `a`. It is finite
and nonempty since `a ≠ 1`. For `B` in `E` let `S_B ≤ Q` be its stabilizer. We claim
`S_B ≠ 0`. Suppose `S_B = 0`. Then `s(B) ≠ B`. Now `s(B)` is a bump of `a_s`, so it is
disjoint from `B`. So `s` moves every point of `B`, and `B` lies in one bump `K` of `s`.
In the same way `B` lies in a bump `K'` of `t`. Since `s, t` commute, `K = K'` by Lemma A.
Every element of `Q` commutes with `s`, so it preserves `K` and fixes its left endpoint
`k`. The map `v ↦ log_μ v'(k+)` is a homomorphism `Q ≅ Z^2 → Z`, so it has a nonzero
element `c` in its kernel. Then `c` has slope 1 at `k`, so `c` is the identity on some
`(k, k+ε)`. By Lemma B, with `f = s` and bump `K`, `c` is the identity on `K`. So
`c(B) = B` and `c` is in `S_B`, a contradiction.

**Step 3 (orbits).** `E` meets finitely many `Q`-orbits `O_1, ..., O_r` of `𝓑`. `Q` is
abelian, so all intervals in one orbit `O_i` have the same stabilizer `S_i`, and by Step 2
`S_i ≠ 0`. Put `U_i = ∪ O_i`. These sets are pairwise disjoint, and each is preserved
by `Q` and by `M`. Restriction to `U_i` defines a map `ρ_i` from `M` to the homeomorphisms
of `U_i`. It is a homomorphism of `Z[Q]`-modules, because `ρ_i(v m v^{-1}) = v ρ_i(m) v^{-1}`.
Every lamp `a_w` has all its bumps in `Q·E ⊂ U_1 ∪ ... ∪ U_r`, so every element of `M`
is the identity outside `U_1 ∪ ... ∪ U_r`. Hence `m = 1` in `M` iff `ρ_i(m) = id` for
all `i`.

**Step 4 (the stabilizer fixes the lamp on its orbit).** Let `v` in `S_i` and `B = (p,q)`
in `E ∩ O_i`. Then `v(B) = B` and `v(p) = p`, and `B` is a bump of `a_v`, since the bumps
of `a_v` in `O_i` are `v(E ∩ O_i) = E ∩ O_i`. The chain rule at `p` gives
`a_v'(p+) = a'(p+)`. So `a_v^{-1} a` has slope 1 at `p` and commutes with `a`. By
Lemma B, `a_v = a` on `B`. On the rest of `U_i` both `a` and `a_v` are the identity,
because neither has a bump there. So `ρ_i(a_v) = ρ_i(a)`, that is,
`(1 − x^v) · ρ_i(a) = 0`.

**Step 5 (contradiction).** Choose nonzero `v_i` in `S_i` and put
`f = (1 − x^{v_1}) ··· (1 − x^{v_r})` in `Z[Q]`. `Z[Z^2]` is an integral domain, so
`f ≠ 0`. For each `i`, `ρ_i(f·a)` is the product of `(1 − x^{v_i}) · ρ_i(a) = 0`
with the other factors, hence `ρ_i(f · a) = id`. By Step 3, `f · a = 1` in `M`. But
`M` is free on `a`, so `f · a ≠ 1`. Contradiction. ∎

## Where the hypotheses enter

- The cyclic slope group is used only in Step 2. With arbitrary real slopes `Q` could act
  on a common bump with injective slope map, and `S_B = 0` is not excluded by this
  argument.
- Step 2 also shows that no two independent elements of `Q` can move a wandering interval
  freely. So the "dynamically obvious" embeddings of `Z ≀ Z^2` fail already for
  `PL_+(I)`: a lamp supported in an interval whose `Q`-translates are pairwise disjoint.
- The proof uses the linear order of `I` twice: to force commuting maps to fix each
  other's bumps (Lemma A), and to single out a left endpoint `k`. In `V` neither is
  available as such. The analogues are finite sets of attracting periodic points and
  revealing pairs. Whether `Z ≀ Z^2` embeds in `V` is the open test case for
  `biorderable-subgroup-of-v-without-free-subgroups-not-in-f`.
