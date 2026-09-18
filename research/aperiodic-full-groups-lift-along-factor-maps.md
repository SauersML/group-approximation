---
rg: 2
id: aperiodic-full-groups-lift-along-factor-maps
kind: claim
title: The topological full group of an aperiodic Cantor system embeds in the full group of every extension, by lifting cocycles along the factor map
distinct_from:
  fg-full-group-subgroups-factor-onto-subshift-full-groups: that pushes a finitely generated subgroup of a full group DOWN to a subshift factor; this pulls the whole full group of a factor UP to any extension, injectively, with no finiteness hypothesis.
  full-shift-topological-full-group-embeds-in-2v: that embeds the full group of the (non-minimal) full shift in 2V by a conjugacy; this is the general mechanism that moves a full group from a factor into an extension.
---

**ESTABLISHED** (lane proof below, elementary; not independently reviewed; no novelty claimed).

## Statement

Let `S : Y -> Y` and `T : X -> X` be homeomorphisms of Cantor spaces, with `T` **aperiodic**
(no periodic points). Let `pi : Y -> X` be a continuous surjection with `pi ∘ S = T ∘ pi`.
For `g ∈ [[T]]` let `n_g : X -> Z` be its continuous cocycle, `g(x) = T^(n_g(x))(x)`, and put

    g~(y) = S^(n_g(pi(y)))(y).

Then `g -> g~` is an injective homomorphism `[[T]] -> [[S]]`, and `pi ∘ g~ = g ∘ pi`.

## Proof

1. **Cocycles are unique and satisfy the cocycle identity.** Since `T` is aperiodic, `T^m x = T^n x`
   forces `m = n`, so `n_g` is determined by `g`, and `n_(gh)(x) = n_g(h x) + n_h(x)`.
2. **`S` is aperiodic too.** If `S^p y = y` with `p ≠ 0`, then `T^p(pi y) = pi y`, which is impossible.
3. **Equivariance.** `pi(g~ y) = T^(n_g(pi y))(pi y) = g(pi y)`.
4. **Homomorphism.** Using 3 for `h`,
   `g~(h~ y) = S^(n_g(pi h~ y)) S^(n_h(pi y)) y = S^(n_g(h pi y) + n_h(pi y)) y = (gh)~(y)`,
   by 1. Also `e~ = id`.
5. **Bijective and continuous.** `g~` is continuous because `n_g ∘ pi` is locally constant, and
   `(g^-1)~` is a two-sided inverse by 4. So `g~ ∈ [[S]]`, with cocycle `n_g ∘ pi`.
6. **Injective.** If `g ≠ e`, pick `x` with `n := n_g(x) ≠ 0` and `y ∈ pi^-1(x)`. Then
   `g~ y = S^n y ≠ y` by 2.

## Remarks

- No minimality, expansivity or finite generation is used, and `S` need not be minimal.
- The same proof works for a free action of any countable group `Λ` on `X`: cocycles are unique
  when the action is free, and a factor of a free action pulls back to a free action.
- Used in `smart-trace-full-group-embeds-in-brin-thompson-2v` to put the full group of a minimal
  subshift into Brin's `2V`, through a minimal element of `2V` that factors onto it.
