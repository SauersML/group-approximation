---
rg: 2
id: thompson-f-two-transitive-disagreement-sets-self-similar-proof
kind: route
title: Local agreement is an equivalence relation at each point, splicing at a gap cuts a disagreement set, and a rigid-stabilizer element beside the set forces a disconnected union
target: thompson-f-two-transitive-disagreement-sets-are-self-similar
requires:
  - thompson-f-two-transitive-rigid-stabilizers-fix-no-point
  - thompson-f-two-transitive-stabilizers-are-piecewise-closed
---

Notation as in the target. Write `ω ≈_x ω'` for `ω' ∈ G_x ω`, so that
`D(ω,ω') = {x : not ω ≈_x ω'}`. Fix a 2-transitive action of `F` on `Ω`,
`|Ω| ≥ 3`. Every step below is used later, and nothing else is imported.

**Step 1 (local agreement).** For each `x ∈ [0,1]`, `≈_x` is the orbit relation
of the group `G_x`, so it is an equivalence relation. It is `F`-equivariant:
`g G_x g^{-1} = G_{gx}`, so `ω ≈_x ω'` iff `gω ≈_{gx} gω'`. If `k ∈ G_x` is
the identity on a neighbourhood `N` of `x`, then `k ∈ G_y` for every `y ∈ N`.
So `{x : ω ≈_x ω'}` is open in `[0,1]`, and `D(ω,ω')` is closed. Symmetry and
`D(gω,gω') = gD(ω,ω')` follow. `D(ω,ω) = ∅` because `1 ∈ G_x`.

**Step 2 (triangle and the two-of-three rule).** Transitivity of `≈_x` gives
`D(ω_1,ω_3) ⊆ D(ω_1,ω_2) ∪ D(ω_2,ω_3)`, and the same with the indices
permuted. If a point `x` lay in exactly one of the three sets, say only in
`D(ω_1,ω_2)`, then `ω_1 ≈_x ω_3 ≈_x ω_2`, so `x ∉ D(ω_1,ω_2)`, a
contradiction. So every point of the union lies in at least two of the sets.
Two consequences:

- (2a) If `D(ω_1,ω_2) ∩ D(ω_1,ω_3) = ∅`, then
  `D(ω_2,ω_3) = D(ω_1,ω_2) ⊔ D(ω_1,ω_3)`. The inclusion `⊆` is the triangle
  rule. A point of `D(ω_1,ω_2)` is not in `D(ω_1,ω_3)`, so by the two-of-three
  rule it is in `D(ω_2,ω_3)`, and the same holds for the other set.
- (2b) If `ω_2 ≈_y ω_3` for all `y` in a set `Y`, then
  `D(ω_1,ω_2) ∩ Y = D(ω_1,ω_3) ∩ Y`.

**Step 3 (nonempty for distinct points).** This is the one place closedness is
used. Suppose `D(ω,ω') = ∅`, and pick `g ∈ F` with `gω = ω'`. For every
`x ∈ [0,1]` there is `k_x ∈ G_x` with `k_x ω = ω' = gω`. So
`h_x := g^{-1}k_x ∈ H := F_ω`. Since `k_x^{-1}` is the identity near `x`, the
element `g^{-1} = h_x k_x^{-1}` agrees with `h_x ∈ H` on a neighbourhood of `x`.
This holds for every `x ∈ [0,1]`. By the equivalent form of
`thompson-f-two-transitive-stabilizers-are-piecewise-closed`, verbatim "`g ∈ H`
as soon as every `t ∈ [0,1]` has a neighborhood (one-sided at dyadic points is
enough) on which `g` agrees with some element of `H`", applied to `g^{-1}`, we
get `g^{-1} ∈ H`. So `ω' = gω = ω`. With Step 1, this proves item 1 of the
target.

**Step 4 (one orbit, compact in `(0,1)`).** Fix `ω` and the open interval
`U = (1/4, 1/2)`. By `thompson-f-two-transitive-rigid-stabilizers-fix-no-point`
(verbatim: "`F_U^c` fixes no point of `Ω`"), there is `f ∈ F_U^c` with
`fω ≠ ω`. For `y ∉ supp f` the element `f` is the identity near `y`, so
`f ∈ G_y` and `y ∉ D(ω,fω)`. So `∅ ≠ D(ω,fω) ⊆ supp f`, a compact subset of
`(0,1)`; nonemptiness is Step 3. Every ordered pair of distinct points is
`(gω, gfω)` for some `g ∈ F`, by 2-transitivity. So every disagreement set of a
distinct pair is `g D(ω,fω)`, and `g` fixes `0` and `1`. This proves item 2.

**Step 5 (splicing at one point).** Let `x ∈ (0,1)`, `x ∉ D_1 := D(ω,ω')`. Take
`k ∈ G_x` with `kω = ω'`, the identity on `N = (x-ε, x+ε) ⊂ (0,1)`, and a dyadic
`c ∈ N`. Let `k^-` be `k` on `[0,c]` and the identity on `[c,1]`, and let `k^+`
be the identity on `[0,c]` and `k` on `[c,1]`. Since `k` fixes `c` and is the
identity near `c`, both are in `F`: their breakpoints are breakpoints of `k`.
They commute and `k = k^+ k^-`. Also `k^-` is the identity on `(x-ε, 1]` and
`k^+` on `[0, x+ε)`. Put `α = k^- ω`. Then `α ≈_y ω` for `y ∈ (x-ε,1]`, and
`α = (k^+)^{-1} ω'`, so `α ≈_y ω'` for `y ∈ [0,x+ε)`. So:

- `D(ω,α)` misses `(x-ε,1]`;
- by (2b), `D(ω,α) ∩ [0,x+ε) = D_1 ∩ [0,x+ε)`.

Hence `D(ω,α) = D_1 ∩ [0,x)`, and likewise `D(α,ω') = D_1 ∩ (x,1]`.

**Step 6 (splicing along finitely many points; item 3).** Let `A ⊆ D_1` be
relatively clopen. `A` and `B = D_1 \ A` are disjoint compact sets. Cover `A`
by finitely many open intervals whose closures miss `B`, and let `V` be their
union intersected with `(0,1)`. Then `V ∩ D_1 = A`, and every boundary point of
`V` in `(0,1)` lies outside `D_1`. It is not in `V ⊇ A`, and it is in the
closure of an interval whose closure misses `B`. Let `c_1 < … < c_m` be these
boundary points. They cut `[0,1]` into cells `Q_0, …, Q_m`, with `Q_j` between
`c_j` and `c_{j+1}`, each lying in `V` or in its complement. Put `σ_j = ω'` if
`Q_j ⊆ V`, and `σ_j = ω` otherwise.

Build `β_0, …, β_m` so that `β_k ≈_y σ_j` for `y ∈ Q_j`, `j < k`, and
`β_k ≈_y σ_k` for all `y > c_k`:

- Start with `β_0 = σ_0`.
- Given `β_k`, put `x = c_{k+1} ∉ D_1`. Near `x`, `β_k ≈_x σ_k`. Also
  `σ_k ≈_x σ_{k+1}`, since `σ_k, σ_{k+1} ∈ {ω,ω'}` and `x ∉ D_1`. So
  `x ∉ D(σ_{k+1}, β_k)`.
- Step 5, applied to the pair `(σ_{k+1}, β_k)` at `x`, gives `β_{k+1}` with
  `β_{k+1} ≈_y β_k` for `y < x + ε` and `β_{k+1} ≈_y σ_{k+1}` for `y > x - ε`.

This has the required form. For `β = β_m`, at every point `y` either `y ∉ D_1`,
or `y ∈ Q_j ∩ D_1` and `β ≈_y σ_j`. So `D(ω,β) = D_1 ∩ V = A` and
`D(β,ω') = D_1 \ A`. For `A = D_1 ∩ [0,x)` this is Step 5 again.

**Step 7 (self-similarity; item 4).** Let `A ⊆ D_0 = D(ω,ω')` be nonempty and
relatively clopen, and take `β` from Step 6 with `D(ω,β) = A`. Since `A ≠ ∅`,
`β ≠ ω`. By 2-transitivity `(ω,β) = g(ω,ω')` for some `g ∈ F`, so
`A = g D_0`.

**Step 8 (not connected; item 5).** Let `ω ≠ ω'` and `D_1 = D(ω,ω')`. By Step
4, `D_1` is a compact subset of `(0,1)`, so `m = min D_1 > 0`. Let `U = (m/3,
2m/3)`. By `thompson-f-two-transitive-rigid-stabilizers-fix-no-point`
(verbatim: "For a nonempty open interval `U ⊂ (0,1)`, let `F_U^c` be the
elements of `F` whose support is a compact subset of `U`. Then `F_U^c` fixes no
point of `Ω`."), there is `f ∈ F_U^c` with `fω ≠ ω`. As in Step 4,
`D_2 = D(ω,fω)` is nonempty (Step 3) and contained in `supp f ⊂ U`. So `D_1`
and `D_2` are disjoint nonempty compact sets. By (2a),
`D(ω',fω) = D_1 ⊔ D_2`, which is not connected. In particular `ω' ≠ fω`, so by
Step 4 `D(ω',fω) = g D_0` for some `g ∈ F`. Since `g` is a homeomorphism of
`[0,1]`, `D_0` is not connected.

**Step 9 (shape; item 6).** Every connected component of `D_0` is closed in
`D_0`. By Step 7 and Step 8, no nonempty relatively clopen subset of `D_0` is
connected, because it is `gD_0`.

- If `D_0` had finitely many components, each would be the complement of a
  finite union of closed sets, hence relatively clopen, and connected. This is
  impossible. So `D_0` has infinitely many components.
- An isolated point `p` of `D_0` would give the relatively clopen connected
  set `{p}`. So `D_0` has no isolated points. It is nonempty and compact, hence
  perfect.
- A component that is relatively open is relatively clopen and connected. So no
  component of `D_0`, degenerate or not, is relatively open.

This completes the proof of the target.

**Remark (extreme points are the hull endpoints).** With `η` and `ξ` defined as
in `thompson-f-two-transitive-hull-endpoints-are-rational`, from the sets
`I^-(ω,ω') = {x ∈ (0,1) : ω' ∈ F_x^- ω}` and `I^+`, where `F_x^-` is the set of
elements supported in `[0,x]`, we have `max D(ω,ω') = η(ω,ω')` and
`min D(ω,ω') = ξ(ω,ω')`. Only the definitions are used.

- If `x ∈ I^-`, say `ω' = fω` with `f` supported in `[0,x]`, then `f ∈ G_y`
  for every `y > x`. So `D(ω,ω') ⊆ [0,x]`, and `max D ≤ η`.
- Conversely, let `x ∈ (max D, 1)` and `x' ∈ (max D, x)`. Apply Step 5 at `x'`,
  with `ε` small enough that the dyadic point `c` is below `x`. It gives
  `α = k^- ω` with `D(α,ω') = D ∩ (x',1] = ∅`, so `α = ω'` by Step 3. Since
  `k^-` is supported in `[0,c] ⊂ [0,x]`, `x ∈ I^-`. So `η ≤ max D`.

The statement for `ξ` is the mirror image. So the hull endpoints are the two
extreme points of a closed set that has no interval shape. Their separation
`ξ < η` (`thompson-f-two-transitive-hull-endpoints-are-separated`) is the
statement that `D_0` is not a point, which here also follows from Step 9.
