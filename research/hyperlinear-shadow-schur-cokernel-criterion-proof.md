---
rg: 2
id: hyperlinear-shadow-schur-cokernel-criterion-proof
kind: route
title: Five-term sequence for the residual, radical of the relative coinvariant quotient, then marked closedness along a flag
target: hyperlinear-shadow-schur-cokernel-criterion
requires:
  - mf-nonhyperlinear-collapse-structure
  - local-approximation-properties-are-marked-closed
---

## Why sufficient

All groups are countable. `Res(K)` is the intersection of the kernels of all
homomorphisms from `K` to hyperlinear groups.

**(P0) Formal properties of `Res`.**
- (i) `K/Res(K)` is hyperlinear, and `K` is hyperlinear iff `Res(K) = 1`
  (`mf-nonhyperlinear-collapse-structure`).
- (ii) If `K/C` is hyperlinear then `Res(K) <= C`: the quotient map is one of
  the homomorphisms in the intersection.
- (iii) For every surjection `f : K -> K'`, `f(Res K) <= Res K'`. A homomorphism
  `K' -> H` into a hyperlinear group composes with `f` to a homomorphism
  `K -> H`, which kills `Res K`.
- (iv) Hyperlinearity passes to subgroups. A group is hyperlinear iff all its
  finitely generated subgroups are. Among marked groups on a fixed finite
  generating set, the hyperlinear ones form a closed set
  (`local-approximation-properties-are-marked-closed`).

**(P1) Item 1.** The abelianization `G -> G^ab` has abelian, hence
hyperlinear, image, so by (P0)(ii) `N <= [G,G]`. The Stallings--Stammbach
five-term exact sequence for `1 -> N -> G -> Q -> 1` reads

```text
H_2(G) -> H_2(Q) -> N/[N,G] -> H_1(G) -> H_1(Q) -> 0.
```

The map `N/[N,G] -> H_1(G) = G/[G,G]` is induced by inclusion. Its image is
`N[G,G]/[G,G]`, which is `0` because `N <= [G,G]`. By exactness,
`H_2(Q) -> N/[N,G]` is onto, and its kernel is the image of `H_2(G)`. Hence
`N/[N,G] = coker(H_2 G -> H_2 Q) = D(G)`.

**(P2) Item 2.** In `E = G/[N,G]` the image `N/[N,G]` of `N` is central,
because `[N,G]` has been killed. The quotient of `E` by it is `G/N = Q`. This
gives the central extension `1 -> D -> E -> Q -> 1` with `D = D(G)`.
- Upper bound: `Q` is hyperlinear, so by (P0)(ii) `Res(E) <= D`.
- Lower bound: by (P0)(iii), `Res(E)` contains the image of `N = Res(G)`,
  which is `D`.

So `Res(E) = D`, and by (P0)(i) `E` is non-hyperlinear iff `D != 0`.

**(P3) Item 3.**
- (b) implies (a): if `D(G) != 0`, then `E(G)` is a non-hyperlinear central
  extension of the hyperlinear group `Q` (P2).
- (a) implies (b): let `1 -> C -> E -> H -> 1` be central, with `H`
  hyperlinear and `E` not. By (P0)(ii), `M = Res(E) <= C`, so `M` is
  central and `[M,E] = 1`. By (P0)(i), `M != 0`. By (P1) applied to `G = E`,
  `D(E) = M/[M,E] = M != 0`.

**(P4) Item 4, prime localization.** Suppose `D = D(G) != pD` for a prime
`p`.

*Step 1.* Let `E_p = E(G)/pD`, which is legitimate because `pD` is central,
hence normal. This is a central extension of `Q` by `V = D/pD != 0`.
- Upper bound: `Q` is hyperlinear, so by (P0)(ii) `Res(E_p) <= V`.
- Lower bound: by (P0)(iii), `Res(E_p)` contains the image of
  `Res(E(G)) = D`, which is `V`.

So `Res(E_p) = V != 0`, and `E_p` is not hyperlinear.

*Step 2, finite generation.* By (P0)(iv), some finitely generated subgroup
`L <= E_p` is not hyperlinear. Put `V_L = L intersect V`. It is central in `L`
and elementary abelian, and `L/V_L` embeds in `Q`, so it is hyperlinear.

*Step 3, marked closedness.* `V_L` is a countable `F_p`-vector space. Choose a
basis `(e_j)` indexed by `j` in an initial segment of the naturals, and put
`V_i = span{e_j : j > i}`.
- The `V_i` are central in `L`, decrease, have finite codimension, and
  intersect in `0`.
- Fix a finite generating tuple of `L`, and let `K`, `K_i` be the kernels of
  the markings of `L` and of `L/V_i`. Then `K_i` decreases with intersection
  `K`, so `L/V_i -> L` in the space of marked groups.
- Hyperlinear marked groups form a closed set (P0)(iv), so the
  non-hyperlinear ones form an open set. Since `L` is not hyperlinear, `L/V_i`
  is not hyperlinear for some `i`.

*Step 4, flag.* Fix such an `i` and let `m = dim(V_L/V_i)`, which is finite.
- Choose a flag `V_L/V_i = W_0 > W_1 > ... > W_m = 0` of subspaces of
  codimension `1` in each other. All are central in `L/V_i`.
- Put `H_j = (L/V_i)/W_j`. Then `H_0 = L/V_L` is hyperlinear, and
  `H_m = L/V_i` is not.
- Let `j` be least with `H_{j+1}` not hyperlinear. Then `H_j` is hyperlinear
  and finitely generated, and `1 -> W_j/W_{j+1} = Z/p -> H_{j+1} -> H_j -> 1`
  is a non-hyperlinear central extension.

**(P5) The equivalence in item 4.**
- (b') implies (a') is (P4).
- (a') implies (b'): let `E` be a non-hyperlinear central extension of a
  hyperlinear group by a finitely generated abelian group `C`. This includes
  finite and cyclic `C`. As in (P3), `D(E) = Res(E)` is a nonzero subgroup of
  `C`. A nonzero finitely generated abelian group is not divisible.

**(P6) Item 5.** Under "finite central extensions of hyperlinear groups are
hyperlinear", (a') fails, so by (P5) every `D(G)` is divisible. Under "all
central extensions are hyperlinear", (a) fails, so by (P3) every `D(G) = 0`.
Then (P1) gives `N = [N,G]`, and (P2) gives `G/[N,G] = Q`. Surjectivity of
`H_2(G) -> H_2(Q)` is `D(G) = 0`.

**(P7) The failing step for overgroups.** Let `G <= G'` with
`Res(G') = N'`, the normal closure of `N` in `G'`. Then `N'/[N',G']` is
generated by the images of `N`, and `[N,G] <= [N',G']`. So it is a quotient
of `N/[N,G] = D(G)`, and `D(G) = 0` forces `D(G') = 0`.

**(P8) The divisible gap.** If `D` is divisible, every quotient `D/B` is
divisible, so no finite quotient `D/B != 0` exists, and Step 1 of (P4) has no
analogue.
- The fibre decomposition `L(E) = integral over D^ of L_{chi o delta}(Q)`,
  where `delta : H_2(Q) -> D` is the connecting map, has non-CE fibres on a
  nonempty open set of characters. This is because Connes-embeddable traces
  are weak-* closed and dominated traces of CE traces are CE.
- A character of finite order on a divisible group is trivial, so torsion
  characters are not available.
- A twist `chi o delta` whose image is infinite is not a torsion class.

This is why the claim records the divisible case as open.

**(P9) Finitely presented shadows have no gap.** If `Q` is finitely
presented, its presentation complex is finite, so `H_2(Q)` is a quotient of
the finitely generated group `H_2` of that complex. By (P1), `D(G)` is a
quotient of `H_2(Q)`, so it is finitely generated. A nonzero finitely generated
abelian group has a `Z/p` quotient, and (P4) applies.

**Lifts do not help.** Let `S <= E = E(G)` map onto `Q`, and let `s_i` be
lifts of the generators. Evaluating a relator `r in [F,F]` of `Q` on
`s_i d_i`, with `d_i in D` central, gives `r(s)`, because the exponent sums
vanish. So `S intersect D` contains the image of the transgression
`delta : H_2(Q) = (M intersect [F,F])/[M,F] -> D`, and `delta` is onto by
(P1). Since `E = S.D`, `E` is the quotient of `S x D` by the central subgroup
`{(d,d^{-1}) : d in S intersect D}`. So `E` is hyperlinear iff `S` is:
- if `S` is hyperlinear, so is `S x D`, and a central quotient of a
  hyperlinear group is hyperlinear, by the fibre argument of (P8) at the
  trivial character;
- conversely `S <= E`.
