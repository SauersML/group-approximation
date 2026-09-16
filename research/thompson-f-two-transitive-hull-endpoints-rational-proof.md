---
rg: 2
id: thompson-f-two-transitive-hull-endpoints-rational-proof
kind: route
title: A swap fixes the hull endpoints, and a swap that is the identity near an endpoint splits there, so the grid moves the endpoint past itself
target: thompson-f-two-transitive-hull-endpoints-are-rational
requires:
  - thompson-f-two-transitive-actions-are-faithful
  - thompson-f-two-transitive-actions-satisfy-grid-condition
---

Throughout, `F` acts 2-transitively on `Ω`, `|Ω| ≥ 3`. By
`thompson-f-two-transitive-actions-are-faithful` the action is faithful. Put
`N_1 = ∪_{x<1} F_x^-` (elements that are the identity near `1`) and
`N_0 = ∪_{x>0} F_x^+`. Both are normal subgroups of `F` containing `[F,F]`.

We use two facts from `thompson-f-two-transitive-actions-satisfy-grid-condition`,
at every `x ∈ (0,1)`:

- (G2) an `F_x^-`-orbit and an `F_x^+`-orbit meet in at most one point;
- (G3) for every `ω`, the map `(aω, cω) ↦ acω`, for `a ∈ F_x^-`, `c ∈ F_x^+`,
  is a bijection from `F_x^-ω × F_x^+ω` onto the `(F_x^- × F_x^+)`-orbit of `ω`.

**Step 0 (invariant relations).** An `F`-invariant relation on ordered pairs of
distinct points is empty or everything, since `F` is transitive on such pairs.
In particular, if `R` is invariant and symmetric and some pair is not in `R`,
then no pair is in `R`.

**Step 1 (item 1).** *Monotonicity.* If `x < x'` then `F_x^- ≤ F_{x'}^-` and
`F_{x'}^+ ≤ F_x^+`. So `I^-` is an up-set and `I^+` a down-set.

*Symmetry.* `ω' = aω` iff `ω = a^{-1}ω'`, so `I^±(ω,ω') = I^±(ω',ω)`.

*Equivariance.* For `g ∈ F`, `g F_x^- g^{-1} = F_{g(x)}^-` and
`g F_x^+ g^{-1} = F_{g(x)}^+`, because `g` is an increasing homeomorphism of
`[0,1]`. Hence `ω' = aω` with `a ∈ F_x^-` iff `gω' = (gag^{-1})(gω)` with
`gag^{-1} ∈ F_{g(x)}^-`. So `I^-(gω,gω') = g(I^-(ω,ω'))`, and likewise for `I^+`.
Since `g` is increasing, `η(gω,gω') = g(η(ω,ω'))` and `ξ(gω,gω') = g(ξ(ω,ω'))`.

*Nonempty.* A 2-transitive action is primitive. The orbits of the normal
subgroup `N_1` form an `F`-invariant partition, so they are all singletons or
there is one orbit. `N_1 ⊇ [F,F] ≠ 1` and the action is faithful, so `N_1` is
transitive. Every element of `N_1` lies in some `F_x^-` with `x < 1`, so
`I^-(ω,ω') ≠ ∅` and `η(ω,ω') < 1`. The same argument with `N_0` gives
`I^+(ω,ω') ≠ ∅` and `ξ(ω,ω') > 0`.

*Proper.* The relation `R = {(ω,ω') : I^-(ω,ω') = (0,1)}` is invariant (as
`g((0,1)) = (0,1)`) and symmetric. If every pair were in `R`, then for every
`x ∈ (0,1)` the group `F_x^-` would be transitive on `Ω`. By (G2) each
`F_x^+`-orbit then has at most one point, so `F_x^+` acts trivially. But
`F_x^+ ≠ 1`, contradicting faithfulness. So some pair is not in `R`, and by
Step 0 no pair is. As `I^-` is an up-set, `η = inf I^- > 0`. Symmetrically,
`I^+ ≠ (0,1)` for every pair, so `ξ < 1`.

*Order.* If `x ∈ I^- ∩ I^+` then `ω'` lies in the `F_x^-`-orbit and in the
`F_x^+`-orbit of `ω`, which by (G2) meet only in `ω`. So `I^- ∩ I^+ = ∅`, and
`ξ(ω,ω') ≤ η(ω,ω')`. (This is not used below.)

**Step 2 (swaps fix the endpoints).** By 2-transitivity there is `s ∈ F` with
`sω = ω'` and `sω' = ω`. By Step 1,
`s(I^-(ω,ω')) = I^-(ω',ω) = I^-(ω,ω')`. So `s` maps the up-set `I^-` onto
itself and fixes its infimum `η = η(ω,ω')`. Likewise `s(ξ) = ξ`.

**Step 3 (no swap is the identity near `η`).** Suppose `s` swaps `ω,ω'` and is
the identity on an open interval containing `η`. Dyadic rationals are dense, so
choose dyadic `y < η < x` with `s` the identity on `[y,x]`. Then `x ∈ I^-`
(since `I^-` is an up-set with infimum `η < x`) and `y ∉ I^-` (since `y < η`).

*Splitting `s`.* Let `s_-` equal `s` on `[0,y]` and the identity on `[y,1]`, and
let `s_+` equal the identity on `[0,x]` and `s` on `[x,1]`. Since `s` fixes `y`
and `x`, both are homeomorphisms of `[0,1]`. They are piecewise linear with
breakpoints among those of `s` together with the dyadic points `y, x`, and with
slopes among those of `s` and `1`. So `s_-, s_+ ∈ F`, with
`s_- ∈ F_y^- ≤ F_x^-` and `s_+ ∈ F_x^+`. As `s` is the identity on `[y,x]`,
`s = s_- s_+`.

*Applying the grid at `x`.* Since `x ∈ I^-`, pick `a ∈ F_x^-` with `aω = ω'`.
With the map of (G3) at `x`,

- the pair `(aω, ω) = (aω, 1·ω)` is sent to `aω = ω'`;
- the pair `(s_-ω, s_+ω)` is sent to `s_- s_+ ω = sω = ω'`.

By injectivity in (G3), `s_-ω = aω = ω'` (and `s_+ω = ω`). So `ω' ∈ F_y^- ω`,
i.e. `y ∈ I^-(ω,ω')`, contradicting `y < η`. This proves item 2 for `η`.

*The endpoint `ξ`.* Suppose `s` is the identity on `[y,x]` with dyadic
`y < ξ < x`. Now `y ∈ I^+` and `x ∉ I^+`. Define `s_-, s_+` as above, so
`s_- ∈ F_y^-` and `s_+ ∈ F_x^+ ≤ F_y^+`. Pick `c ∈ F_y^+` with `cω = ω'`. The
map of (G3) at `y` sends `(ω, cω)` and `(s_-ω, s_+ω)` to `ω'`, so `s_+ω = ω'`.
Hence `x ∈ I^+`, a contradiction. This proves item 2 for `ξ`.

**Step 4 (item 3).** Let `p` be `η(ω,ω')` or `ξ(ω,ω')`, and `s` a swap, so
`s(p) = p` by Step 2. Suppose `p` is not dyadic. Breakpoints of `s` are dyadic,
so `s` is affine on an open interval around `p`: `s(t) = 2^k t + b` there, with
`k ∈ Z` and `b` dyadic. If `k = 0` then `p + b = p` forces `b = 0`, so `s` is
the identity near `p`, contradicting Step 3. So `k ≠ 0`, and
`p = b/(1 − 2^k)` is rational. Dyadic points are rational too. This proves
item 3.

**Step 5 (item 4).** For an `F`-orbit `O ⊆ (0,1)`, the relation
`R_O = {(ω,ω') : η(ω,ω') ∈ O}` is `F`-invariant, because
`η(gω,gω') = g(η(ω,ω'))` and `g(O) = O`, and it is symmetric. By Step 0 each
`R_O` is empty or everything. The sets `R_O` partition the ordered pairs of
distinct points, so exactly one of them is everything. Its orbit `Θ^-`
consists of rational points by Step 4. The same argument for `ξ` gives `Θ^+`.

**Step 6 (item 5).** Every element of the setwise stabilizer of `{ω,ω'}` maps
the pair `(ω,ω')` to itself or to `(ω',ω)`, so by Step 1 it preserves `I^-` and
`I^+` and fixes `p`. So `ρ` is defined, and it is a homomorphism. An element of
`F` fixing `p` is the identity near `p` exactly when its germ at `p` is
trivial: at dyadic `p` it is affine on each side of `p`, and slope `1` on a side
with `p` fixed means the identity on that side; at non-dyadic `p` use Step 4.
If `s` is a swap and `r ∈ F_ω ∩ F_{ω'}`, then `sr` is a swap, so by Step 3
`ρ(s)ρ(r) ≠ 1`. As `L` is a subgroup, this says `ρ(s) ∉ L`. Finally
`s^2 ∈ F_ω ∩ F_{ω'}`, so `ρ(s)^2 ∈ L`. Then `ρ(s)L` has order 2 in `Γ_p/L`,
and `L ≠ 1` because `ρ(s)^2 ∈ L` is nontrivial (`Γ_p` is torsion-free and
`ρ(s) ≠ 1`).

The germ groups: an element fixing a dyadic `p` has left and right slopes
`2^i, 2^j`, and every pair `(i,j)` occurs, giving `Γ_p ≅ Z^2`. At a non-dyadic
rational `p` the element is affine near `p`, so its germ is its slope, and the
slopes that occur form a subgroup of `2^Z`; it is nontrivial (by Step 4 a swap
has slope `2^k ≠ 1`), so it is infinite cyclic. Only `L ≠ 1` and the order-2
statement are used later.

**The formula for `η(ω,gω)`.** Let `H = F_ω` and `g ∉ H`. For `y ∈ (0,1)`,
`gω ∈ F_y^- ω` iff `g ∈ F_y^- H` iff some `h ∈ H` has `gh^{-1}` equal to the
identity on `[y,1]`, i.e. `g = h` on `[h^{-1}(y),1]`. Writing `z = h^{-1}(y)`,
this gives `y = h(z) = g(z)`. Conversely, if `g = h` on `[z,1]` with `h ∈ H`,
then `gh^{-1}` is the identity on `[g(z),1]`, so `g(z) ∈ I^-(ω,gω)`. Hence
`I^-(ω,gω) = g(Z)` with `Z = {z ∈ (0,1) : g agrees on [z,1] with some h ∈ H}`,
and `η(ω,gω) = g(inf Z)`. ∎
