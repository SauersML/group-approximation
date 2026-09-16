---
rg: 2
id: thompson-f-two-transitive-dyadic-branching-binary-proof
kind: route
title: The stabilizer of a dyadic point fixes every branch at that point and is transitive on the pairs with that hull endpoint, so there are at most two branches
target: thompson-f-two-transitive-dyadic-branching-is-binary
requires:
  - thompson-f-two-transitive-actions-satisfy-grid-condition
  - thompson-f-two-transitive-hull-endpoints-are-rational
---

Throughout, `F` acts 2-transitively on `Ω`, `|Ω| ≥ 3`, `ω ∈ Ω`, `H = F_ω`, and
`p ∈ (0,1)` is dyadic. Write `η = η(ω,ω')` and `I^- = I^-(ω,ω')` as in
`thompson-f-two-transitive-hull-endpoints-are-rational`. From that claim we use
item 1 (`I^-` is an up-set, `η` is symmetric, and `η(gω,gω') = g(η(ω,ω'))`)
and item 4 (all hull endpoints `η` lie in one `F`-orbit `Θ^-`). From
`thompson-f-two-transitive-actions-satisfy-grid-condition` we use item 2: an
`F_x^-`-orbit and an `F_x^+`-orbit meet in at most one point.

**Step 1 (the slope map).** An element `a ∈ F_p^-` fixes `p` and is affine on
some interval `[y,p]`, `y < p`, with slope `2^{λ_p(a)}`. By the chain rule
`λ_p` is a homomorphism. It is onto `Z`: `F_p^-` is a copy of `F` on `[0,p]`,
and elements of `F` realize every slope `2^k` at the endpoint `1`. Its kernel is
`M_p`: slope `1` on `[y,p]` with `p` fixed means the identity on `[y,p]`, so the
element lies in `F_y^-`; and elements of `M_p` have slope `1` at `p`. So `M_p`
is normal in `F_p^-` with `F_p^-/M_p ≅ Z`.

Since the `F_y^-` increase with `y`, `M_p ω = ∪_{y<p} F_y^- ω`.

**Step 2 (branches).** Let `Br` be the set of `M_p`-orbits contained in
`F_p^- ω`. As `M_p` is normal in `F_p^-`, the group `F_p^-` permutes `Br`
transitively, and `M_p` acts trivially, so `Z = F_p^-/M_p` acts transitively on
`Br`. The stabilizer in `F_p^-` of the branch `[ω] = M_p ω` is
`M_p (H ∩ F_p^-)`: if `aω = mω` with `m ∈ M_p`, then `m^{-1}a ∈ H ∩ F_p^-`.
Let `λ_p(H ∩ F_p^-) = dZ` with `d ≥ 0`. Then `[aω] ↦ λ_p(a) mod d` is a
well-defined bijection `Br → Z/dZ`, and `a ∈ F_p^-` acts on `Br` by adding
`λ_p(a)`. So `|Br| = d` if `d > 0`, and `Br` is infinite if `d = 0`.

**Step 3 (the stabilizer of `p` fixes every branch).** Let
`H_p = {h ∈ H : h(p) = p}`. For `h ∈ H_p`, `h F_p^- h^{-1} = F_p^-` and
`h M_p h^{-1} = M_p`, because `h` maps `[0,p]` to itself and `[y,1]` onto
`[h(y),1]` with `h(y) < p`. Also `h F_p^- ω = F_p^- hω = F_p^- ω`. So `h`
permutes `Br`, by `h[aω] = [h a ω] = [(hah^{-1}) hω] = [(hah^{-1}) ω]`.
Since `h` and `a` fix `p`, the chain rule gives
`(hah^{-1})'_-(p) = h'_-(p) · a'_-(p) · (h^{-1})'_-(p) = a'_-(p)`, so
`λ_p(hah^{-1}) = λ_p(a)`. By Step 2, `h[aω] = [aω]`. Every element of `H_p`
maps each branch onto itself.

**Step 4 (the pairs with endpoint `p`).** Let
`T_p = {ω' ≠ ω : η(ω,ω') = p}`. We show `T_p ∩ F_p^- ω = F_p^- ω \ M_p ω`.
If `ω' ∈ F_p^- ω \ M_p ω`, then `ω' ≠ ω` (as `ω ∈ M_p ω`), `p ∈ I^-`, and since
`M_p ω = ∪_{y<p} F_y^- ω` no `y < p` lies in `I^-`. So `η = p`. Conversely, if `η(ω,ω') = p` and `ω' ∈ M_p ω`, then
`ω' ∈ F_y^- ω` for some `y < p`, so `η ≤ y < p`, a contradiction.

The group `H_p` preserves `T_p`, since `η(ω,hω') = η(hω,hω') = h(p) = p` for
`h ∈ H_p` and `ω' ∈ T_p`. It is transitive on `T_p`: if `ω',ω'' ∈ T_p`, choose
`g ∈ F` with `gω = ω` and `gω' = ω''`. Then `g ∈ H` and
`g(p) = g(η(ω,ω')) = η(ω,ω'') = p`, so `g ∈ H_p`.

**Step 5 (items 1–3).** Suppose `Br` has two branches `B_1, B_2` different from
`[ω]`. By Step 4 both lie in `T_p`. Pick `ω_i ∈ B_i`. By Step 4 some `h ∈ H_p`
has `hω_1 = ω_2`, but by Step 3 `h B_1 = B_1`, and `B_1 ∩ B_2 = ∅`. This is a
contradiction, so `|Br| ≤ 2`. In particular `d ∈ {1,2}` by Step 2, which gives
item 1.

If `|Br| = 1` then `d = 1`, which is item 2. If `|Br| = 2` then `d = 2`, and an
element of odd slope adds `1 mod 2`, so it exchanges the two branches. The
non-`[ω]` branch is `F_p^- ω \ M_p ω = T_p ∩ F_p^- ω`, which is nonempty. Since
`H_p` is transitive on `T_p` and preserves `F_p^- ω`, all of `T_p` lies in
`F_p^- ω`. So `F_p^- ω \ M_p ω = T_p`, which is item 3.

**Step 6 (item 4).** Call a pair *attaining* if `ω' ∈ F^-_{η(ω,ω')} ω`. This
relation is symmetric (`ω' = aω` iff `ω = a^{-1}ω'`, and `η` is symmetric) and
`F`-invariant (`g F^-_x g^{-1} = F^-_{g(x)}` and `η(gω,gω') = g(η(ω,ω'))`). As
`F` is transitive on ordered pairs of distinct points, it holds for all pairs or
for none.

Suppose `(ω,p)` has two branches. By item 3, `T_p ≠ ∅`, so some
`ω' ∈ F_p^- ω` has `η(ω,ω') = p`. This pair is attaining, so all pairs are.
Also `p ∈ Θ^-` is dyadic, and `F` is transitive on the dyadic points of
`(0,1)`, so `Θ^-` is the orbit of dyadic points.

Conversely, suppose `Θ^-` is the dyadic orbit and all pairs are attaining. For
any `ω' ≠ ω`, the point `p = η(ω,ω')` is dyadic and `ω' ∈ F_p^- ω`, while
`ω' ∉ M_p ω` by Step 4. So `(ω,p)` has two branches.

In that case, for fixed `ω`: if `p = η(ω,ω') ∈ P_ω`, the last paragraph shows
`(ω,p)` has two branches; if `(ω,p)` has two branches, then `T_p ≠ ∅`, so
`p ∈ P_ω`. Finally `P_ω` is one `H`-orbit: `H` is transitive on `Ω \ {ω}`, and
`η(ω,hω') = h(η(ω,ω'))` for `h ∈ H`.

**Step 7 (item 5).** Assume the two-branch case, let `p ∈ P_ω`, and let `h ∈ H`
fix `p`. Let `h_-` equal `h` on `[0,p]` and the identity on `[p,1]`, and
`h_+` the identity on `[0,p]` and `h` on `[p,1]`. As `p` is dyadic and fixed by
`h`, both lie in `F`, with `h_- ∈ F_p^-`, `h_+ ∈ F_p^+`, `h = h_- h_+`, and
`λ_p(h_-)` equal to the log of the left slope of `h` at `p`. From `hω = ω` we get
`h_+ ω = h_-^{-1} ω`, a point in the `F_p^+`-orbit and in the `F_p^-`-orbit of
`ω`. These meet only in `ω`, so `h_- ω = ω`. So `h_- ∈ H ∩ F_p^-`. By Step 6
`(ω,p)` has two branches, so `λ_p(h_-) ∈ 2Z` by item 3.

**Step 8 (mirror statements).** Exchange left and right throughout: use
`F_p^+`, `M_p^+ = ∪_{x>p} F_x^+`, the right slope at `p`, the down-set `I^+`,
its supremum `ξ` and the orbit `Θ^+`. Every step uses only the properties of
`η` listed at the start, which item 1 and item 4 of
`thompson-f-two-transitive-hull-endpoints-are-rational` give for `ξ` as well,
together with the grid fact, which is symmetric in left and right.

**A consequence for swaps.** In the two-branch case, let `s` swap `ω` and
`ω'`, with `p = η(ω,ω')`. By item 2 of
`thompson-f-two-transitive-hull-endpoints-are-rational`, `s(p) = p`. Split
`s = s_- s_+` at `p` as in Step 7, and choose `a ∈ F_p^-` with `aω = ω'`. By
item 3 of the grid claim, `(aω, ω)` and `(s_- ω, s_+ ω)` have the same image
`ω'`, so `s_- ω = ω'` and `s_+ ω = ω`. Since `s_+` commutes with `a`,
`s_+ ω' = ω'`, so `s_-` is again a swap. By item 3, `λ_p(s_-)` is odd. This
remark is not used above. ∎
