---
rg: 2
id: thompson-t-centralizers-of-orbit-free-subgroups-act-freely-proof
kind: route
title: The support of a commuting element is an A-invariant union of intervals, and each interval costs a breakpoint
target: thompson-t-centralizers-of-orbit-free-subgroups-act-freely
requires: []
---

**Setting.** `T` is the group of orientation-preserving homeomorphisms of
`S^1 = R/Z` that are piecewise linear with finitely many breakpoints, dyadic
breakpoints and slopes powers of 2. The only property used here is that each
`c ∈ T` has a finite set `Br(c)` of breakpoints. Away from `Br(c)`, `c` is
locally a translation composed with multiplication by a constant slope.

**Proof.** Let `A ≤ T` have no finite orbit, let `c ∈ T` commute with `A`, and
suppose `Fix(c) ≠ ∅`. Assume `c ≠ 1` for a contradiction.

1. *The support is invariant.* For `a ∈ A` and `x ∈ Fix(c)` we have
   `c(a x) = a c x = a x`, so `a(Fix(c)) ⊆ Fix(c)`. Applying this to `a^{-1}`
   gives equality. So the open set `U = S^1 \ Fix(c)` is `A`-invariant. It is
   nonempty because `c ≠ 1` and proper because `Fix(c) ≠ ∅`. Its connected
   components are open arcs `J = (u, v)` with endpoints in `Fix(c)`, where
   `u = v` is allowed when `U = S^1 \ {u}`. Each `a ∈ A` is a homeomorphism
   preserving `U`, so it permutes the components of `U` and maps endpoints of
   components to endpoints of components.

2. *There are infinitely many components.* Suppose `U` has finitely many
   components. Then the set `E` of their endpoints is finite, nonempty (a proper
   nonempty open subset of `S^1` has at least one component with an endpoint),
   and `A`-invariant. Any point of `E` then has a finite `A`-orbit. This
   contradicts the hypothesis on `A`.

3. *Each component carries a breakpoint.* Let `J = (u, v)` be a component and
   `J̄` its closure, the closed arc from `u` to `v`. Suppose
   `Br(c) ∩ J̄ = ∅`. Lift to `R`: choose a lift `ũ` of `u` and the lift
   `C : R → R` of `c` with `C(ũ) = ũ`, and let `ṽ > ũ` be the first lift of
   `v` after `ũ`, with `ṽ = ũ + 1` when `u = v`. Then `C` has no breakpoint
   on the compact interval `[ũ, ṽ]`. A map that is locally affine at every
   point of a connected interval is affine on it, so `C(y) = s(y − ũ) + ũ` for
   `y ∈ [ũ, ṽ]`. Since `c` preserves orientation and fixes `u` and `v`, it
   maps the arc `J` from `u` counterclockwise to `v` onto itself. So `C` maps
   `(ũ, ṽ)` onto the lift of `J` starting at `ũ`, which is `(ũ, ṽ)`, and
   `C(ṽ) = ṽ`. Hence `s = 1`, so `C`
   is the identity on `[ũ, ṽ]` and `c` fixes every point of `J`. This
   contradicts `J ⊆ U`. Hence `J̄` contains a breakpoint of `c`.

4. *Counting.* A point of `S^1` lies in the closures of at most two components
   of `U`: it is either inside one component, or an endpoint shared by at most
   two of them. By steps 2 and 3, the finite set `Br(c)` meets the closures of
   infinitely many components. Each breakpoint accounts for at most two of them,
   which is impossible.

So `c = 1`. ∎

**Where the argument lives.** Steps 1 and 2 are pure topological dynamics.
Step 3 is the one place where the finiteness of `Br(c)` enters. For a general
homeomorphism, the Denjoy blow-up in the claim shows the statement is false.
