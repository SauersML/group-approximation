---
rg: 2
id: thompson-f-two-transitive-binary-colourings-regular-closed-proof
kind: route
title: Density of bad orbits in disagreement sets, the two-colour sum rule, and regular-closedness of an interior D_0
target: thompson-f-two-transitive-binary-colourings-force-regular-closed
requires:
  - thompson-f-two-transitive-disagreement-sets-are-self-similar
  - thompson-f-two-transitive-irrational-orbit-colorings
  - thompson-f-two-transitive-rigid-stabilizers-fix-no-point
---

Notation as in the target. "S1.k" is item k of
`thompson-f-two-transitive-disagreement-sets-are-self-similar`, and "S2.k" is
item k of `thompson-f-two-transitive-irrational-orbit-colorings`. One
standard fact is used: `F` is transitive on pairs `p < q` of dyadic
rationals in `(0,1)`. Hence every `F`-orbit in `(0,1)` is dense. Indeed,
given `x` and an open interval `I`, pick dyadics `p < x < q` and
`[p',q'] ⊂ I`, and send `(p,q)` to `(p',q')`.

**Item 1 (density).** Let `D = D(ω_1,ω_2)` with `ω_1 ≠ ω_2`. Let `p ∈ D`,
and let `V` be an open neighbourhood of `p`. By S1.2, `D ⊂ (0,1)`.
- If the component of `p` in `D` is nondegenerate, then `V ∩ D` contains a
  nonempty open interval. That interval meets the dense orbit `O`.
- If the component of `p` is `{p}`, then there are points `a < p < b` in `V`
  with `a, b ∉ D`. Otherwise `D` would contain a one-sided neighbourhood
  `[p,p+ε)` or `(p−ε,p]`, and the component of `p` would be nondegenerate.
  Then `A = D ∩ [a,b] = D ∩ (a,b)` is nonempty and relatively clopen in `D`.
  By S1.3, `A = D(ω_1,β)` for some `β`, and `β ≠ ω_1` because `A ≠ ∅`. By
  S2.3, the bad orbit `O` meets every disagreement set of a distinct pair,
  so `O` meets `A ⊂ V`.

So `O ∩ D` is dense in `D`, and `D` is closed, so `D = cl(O ∩ D)`. By S2.2,
`O ∩ D = { y ∈ O : c_{ω_1}(y) ≠ c_{ω_2}(y) }`.

**Item 2 (unique splicing).** Let `x ∈ D(α,α')`.
- By the two-of-three rule (S1.1) for the triple `ω, α, α'`, `x` lies in
  `D(ω,α)` or in `D(ω,α')`. Both are `C_1`.
- By the same rule for the triple `α, α', ω'`, `x` lies in `D(α,ω')` or in
  `D(α',ω')`. Both are `C_2`.

So `x ∈ C_1 ∩ C_2 = ∅`. Hence `D(α,α') = ∅`, and `α = α'` by S1.1.

**Item 3 (sum rule).** Let `O` be a binary bad irrational orbit. Every
colouring `c_{ω_1}` takes values in `H\O`, which has two elements by
hypothesis. Put `D_1 = D(ω_0,ω')` and `D_2 = D(ω_0,ω'')`. With only two
colours, for `y ∈ O` we have `c_{ω'}(y) ≠ c_{ω''}(y)` iff exactly one of
`c_{ω'}(y)` and `c_{ω''}(y)` differs from `c_{ω_0}(y)`. By S2.2,
`O ∩ D(ω',ω'') = O ∩ (D_1 Δ D_2)`.

If `ω' = ω''`, both sides of the sum rule are empty. Otherwise item 1 gives
`D(ω',ω'') = cl(O ∩ (D_1 Δ D_2))`. The set `D_1 ∖ D_2` is relatively open in
`D_1`. `O ∩ D_1` is dense in `D_1` by item 1, or trivially if `D_1 = ∅`. So
`O ∩ (D_1 ∖ D_2)` is dense in `D_1 ∖ D_2`, and symmetrically for
`D_2 ∖ D_1`. Hence `D(ω',ω'') = cl(D_1 Δ D_2)`.

If `D_1 = D_2`, then `D(ω',ω'') = cl(∅) = ∅`, so `ω' = ω''` by S1.1. This
gives injectivity.

**Item 4, construction.** Assume a binary bad irrational orbit and
`int D_0 ≠ ∅`.
- By S1.2 there are `ω_0 ≠ ω'` and an open interval `J` with
  `J ⊂ D_1 = D(ω_0,ω')`. Let `U ⊂ J` be an open interval.
- By `thompson-f-two-transitive-rigid-stabilizers-fix-no-point`, some
  `f ∈ F_U^c` has `fω_0 ≠ ω_0`. Put `ω_1 = fω_0` and `E = D(ω_0,ω_1)`.
- If `x ∉ supp f`, then `f` is the identity on the open set
  `[0,1] ∖ supp f ∋ x`. So `f ∈ G_x`, and `x ∉ E`. Hence
  `E ⊂ supp f ⊂ U ⊂ J`.
- By S1.2, `E` is a translate of `D_0`.
- Put `D_2 = D(ω_1,ω')`. Since `E ⊂ D_1`, item 3 gives
  `D_2 = cl(D_1 ∖ E)`.

Let `x ∈ J`. Every small neighbourhood of `x` lies in `J ⊂ D_1`, so it meets
`D_1 ∖ E` iff it is not contained in `E`. Hence

(★) `D_2 ∩ J = J ∖ int E`.

**Item 4(c).** The statement is `F`-equivariant, since `F` preserves order
and maps interiors and components to interiors and components. All
translates of `D_0` are translates of `E`, so it suffices to treat `E`
itself. Let `c < d` be interior points of `E` in different components of
`E`. Then `[c,d] ⊂ J`, because `E ⊂ J` and `J` is an interval. Put
`Y = D_2 ∩ [c,d]`. By (★), `Y = [c,d] ∖ int E`.
- `Y` is closed.
- Since `c, d ∈ int E`, (★) gives `c, d ∉ D_2`. So
  `D_2 ∖ Y = D_2 ∩ ([0,c] ∪ [d,1])` is closed as well, and `Y` is relatively
  clopen in `D_2`.
- `c` and `d` lie in different components of `E`, so `[c,d] ⊄ E`. Hence `Y`
  contains a point of `[c,d] ∖ E`, and `Y ≠ ∅`.
- By S1.2, `D_2 = kD_0` for some `k ∈ F`. By S1.4 applied to the clopen piece
  `k^{-1}Y` of `D_0`, we get `Y = hD_0` for some `h ∈ F`.

**Item 4(a).** Such points `c, d` exist. By S1.5, `E` is not connected, so
`E = E_1 ⊔ E_2` with `E_1, E_2` nonempty and clopen in `E`. By S1.4, each
`E_i` is a translate of `D_0`, so `int E_i ≠ ∅`. Pick one point in
`int E_1` and one in `int E_2`, and call them `c < d` in order. They lie in
different components, because `E_1` and `E_2` separate `E`.

Now let `W = int E`, `Y = [c,d] ∖ W`, and `y ∈ Y`. Then `y ∈ (c,d)`, since
`c, d ∈ W`. Let `U ⊂ (c,d)` be an open interval containing `y`, and suppose
`U ∩ int Y = ∅`. The open set `U ∖ cl W` lies in `Y`, hence in `int Y`, so
it is empty. Thus `U ⊂ cl W ⊂ E`, because `E` is closed. Since `U` is open,
`U ⊂ int E = W`, which contradicts `y ∈ U ∖ W`. So every neighbourhood of
every point of `Y` meets `int Y`, that is, `Y = cl(int Y)`. By item 4(c),
`Y = hD_0`, and `h` is a homeomorphism of `[0,1]`. Hence
`D_0 = cl(int D_0)`.

**Item 4(b).** Let `[s,a]` and `[b,t]` be components of `D_0` with
`s < a < b < t`, and suppose `(a,b) ∩ int D_0 = ∅`.
- By (a), `(a,b) ∩ D_0 = ∅`. A point `p` of `D_0` in `(a,b)` would be a limit
  of interior points of `D_0`, and some of them would lie in `(a,b)`.
- Write `E = gD_0`, `[s',a'] = g[s,a]` and `[b',t'] = g[b,t]`. Then
  `(a',b') ∩ E = ∅`.
- Pick `c ∈ (s',a')` and `d ∈ (b',t')`. Both are interior points of `E`, and
  they lie in different components of `E`.
- Then `[c,a') ⊂ int E`, and `(b',d] ⊂ int E`.
- `a' ∉ int E`, since points just to the right of `a'` are not in `E`.
  Likewise `b' ∉ int E`.
- So `Y = [c,d] ∖ int E = [a',b']`.

By item 4(c), `Y` is a translate of `D_0`. But `Y` is an interval, which
contradicts S1.5. Hence `(a,b)` meets `int D_0`. ∎
