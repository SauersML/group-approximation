---
rg: 2
id: class-finite-normal-subgroups-are-invisible-to-standard-hosts
kind: claim
title: A normal subgroup with finitely many ambient conjugacy classes is invisible to residual finiteness, stable length and Thompson-type dynamics, so fiber-product data never lives in a residually finite, Cantor-V or interval-F host
distinct_from:
  some-infinite-fp-torsion-free-group-has-finitely-many-classes: that records stable-length and FA screens for a group with finitely many conjugacy classes of its own, the case N = T; this treats a normal subgroup N whose classes are counted in a larger T, where N may have infinitely many classes of its own, and adds the residual-depth and double-commutator obstructions, which constrain T rather than N and have no counterpart there.
  thompson-v-embeds-in-no-conjugacy-finite-group: that uses element orders to exclude V from conjugacy-finite overgroups, the N = T case; this shows V cannot even act nontrivially on N in any action of T, and T cannot be residually finite, with N proper.
  wreath-base-conjugacy-classes-are-finite-multisets: that computes one invariant, support size, in one family of envelopes; this proves that every conjugation-invariant function on N takes finitely many values and names three further invariants that are unbounded on every residually finite, undistorted, or Thompson-type candidate.
  fiber-product-conjugation-action-lemma: that computes the orbit data of the translation action and lists screens on N alone (trivial centre, finitely many orders, infinite); this lists obstructions on the host T (not residually finite, no Cantor-V or interval-F action seeing N, N distorted or torsion in T).
  confined-subgroup-commutator-lemma: that is the Le Boudec--Matte Bon lemma for confined subgroups; this uses only the classical double-commutator trick for a nontrivial normal subgroup, and its content is the invariant read off afterwards.
---

**OPEN.** A route is drafted in `class-finite-normal-subgroups-invisibility-proof`
(elementary; the double-commutator trick and the stable length are classical,
and no novelty is claimed for them. What is new is using them as obstructions
for the fiber-product premise). It is not yet refereed; see Attempts.

## Statement

Let `T` be a group and `N <| T` a normal subgroup with finitely many
`T`-conjugacy classes. Call a function `f` on `N` *`T`-invariant* if
`f(t x t^-1) = f(x)` for all `t in T`, `x in N`. **Master principle:** every
`T`-invariant function on `N` takes finitely many values. Four instances:

1. **Residual depth.** If `N` is finitely generated and `M <= N` is normal in
   `T` with `N/M` residually finite, then `N/M` is finite. In particular the
   finite residual `R(N)` (the intersection of all finite-index subgroups of
   `N`) has finite index in `N`, and `N` has image of order at most
   `[N : R(N)]` in every finite quotient of `T`.
2. **Stable length.** For every action of `T` by isometries on a metric space
   `(Y,d)` and every `x in N`, the stable translation length
   `tau(x) = lim_m d(x^m y, y)/m` is `0`. Every homogeneous quasimorphism
   `T -> R` vanishes on `N`. If `T` is finitely generated, every element of `N`
   is torsion or has `|x^m|_T = o(m)`, that is, it is distorted in `T`.
3. **Cantor cone permutations.** Let `rho: T -> Homeo(X)` be an action on a
   Hausdorff space such that **(CP)**: for every nonempty open `U <= X` and
   every `k >= 2` there are pairwise disjoint nonempty sets
   `D_1, ..., D_2k <= U` and elements `a, s in rho(T)`, each the identity off
   `D_1 ∪ ... ∪ D_2k`, with `a` mapping `D_i` onto `D_(i+1)` for `i < k` and
   `D_k` onto `D_1`, `a` the identity on `D_(k+1) ∪ ... ∪ D_2k`, `a^k = 1`, and
   `s` an involution exchanging `D_i` and `D_(k+i)` for `i <= k`. Then
   `rho(N) = 1`.
4. **Interval bumps.** Let `rho: T -> Homeo((0,1))` be an action whose image
   contains Thompson's group `F` in its standard piecewise-linear dyadic
   action. Then `rho(N) = 1`.

(CP) holds whenever `rho(T)` contains Thompson's group `V` in its standard
action on `{0,1}^N`: take `D_i` to be cones `C_(w u_i)` inside a cone
`C_w <= U`, with `u_1, ..., u_2k` distinct words of one length, and `a`, `s` the
corresponding prefix replacements.

## Consequences for the fiber-product premise

Suppose `(T, N)` is fiber-product data for an infinite group `G`
(`universal-fiber-product-data-for-word-problem-groups`: `G <= T`, `T` finitely
presented, `N` finitely generated, `T/N` of type `F_3`, `C_T(N) = 1`, finitely
many `T`-classes in `N`). Then `T` is infinite, and `N` is infinite because a
finite `N` with trivial centralizer forces `T <= Aut(N)` finite. Hence:

- **(no residually finite host)** `T` is not residually finite. Otherwise `N`
  would be residually finite, so `R(N) = 1`, so `N` finite by item 1. The same
  argument shows `N` has uniformly bounded image in every finite quotient of `T`.
- **(no Cantor-V host)** `T` is not a group of homeomorphisms of a Hausdorff
  space satisfying (CP): item 3 would give `N = 1`. In particular `T` is not a
  subgroup of `Homeo({0,1}^N)` containing the standard `V`, and more generally
  every action of `T` satisfying (CP) has `N` in its kernel.
- **(no interval-F host)** `T` is not a group of homeomorphisms of `(0,1)`
  containing the standard `F`, and every action of `T` on `(0,1)` whose image
  contains standard `F` kills `N`.
- **(N is geometrically invisible)** every element of `N` is torsion or
  distorted in `T`, has zero stable length in every isometric action of `T`, and
  lies in the kernel of every homogeneous quasimorphism of `T`.

So the premise can only be met by a host in which a finitely generated,
centreless, infinite normal subgroup is invisible to finite quotients, to
isometric actions and to Thompson-type dynamics at once.

## What this kills, and the step where each member dies

Every member dies at clause 6 (finitely many `T`-classes in `N`), each through a
named `T`-invariant with infinitely many values on `N`:

| host class for `T` | invariant | where it is unbounded |
|---|---|---|
| residually finite `T` (includes every finitely generated linear group, by Malcev's theorem, cited from memory) | residual depth `min{k : x not in M_k}` | on `N`, because `R(N) = 1` |
| `T` containing standard `V`, or satisfying (CP) | element order of `rho(x)` | on `[Rist(U), Rist(U)] <= rho(N)` |
| `T` containing standard `F` on `(0,1)` | number of components of the open support | same |
| `T` in which some element of `N` is undistorted | `tau` | on powers `x^m` |
| permutational wreath envelopes (already recorded) | support size | on the base |
| `N = T` with `V <= T` (already recorded) | element order | on `V` |

The residually finite row is the first-line host of every "host geometry"
attempt (linear groups, residually finite hyperbolic groups, mapping class
groups, `Out(F_n)`, right-angled Artin groups). The (CP) row is the host class
of every other Boone--Higman route in this graph: Thompson's `V`, the
Brin--Thompson groups `nV`, finitely presented full Cantor groups containing `V`
(`fp-full-binary-cantor-groups-have-type-a-actions`), and the twisted
Brin--Thompson groups `SV_G`, which contain prefix replacements in a single
coordinate supported in any basic cylinder (definition not re-read for this
node, so this instance is recorded as a remark and is not part of the
established statement). So the fiber-product premise cannot recycle the output
or the hosts of any other route as its `T`.

## Calibration: which hypotheses are sharp

- **Finite generation in item 1 is necessary.** In
  `C(C, F_2) ⋊ V` (`cantor-module-thompson-v-product-is-finitely-presented`) the
  normal subgroup `S = C(C, F_2)` has at most three ambient classes (conjugation
  by `(t, w)` sends `(s,1)` to `(w(s), 1)`, and `V` has three orbits on `S`), and
  `S` is infinite and residually finite. It is not finitely generated, so item 1
  does not apply, and it is centralized by itself, so it is not fiber-product
  data. Items 2 and 3 are consistent with it: `S` is the kernel of the action on
  the Cantor space.
- **Faithfulness is not assumed anywhere in items 1--4**; the conclusions are
  about the kernel of an arbitrary action. So passing to a quotient of `T` or to a
  non-faithful Cantor action does not evade them.

## Remarks (imports not pinned verbatim, not part of the established statement)

- If `T` acts on a simplicial tree with a hyperbolic element, item 2 makes every
  element of `N` elliptic. As `N` is finitely generated, Serre's fixed-point
  theorem (Trees, I.6.5) gives a fixed point of `N`, and the fixed tree of `N` is
  `T`-invariant, hence contains the minimal `T`-subtree, on which `N` then acts
  trivially. So no action of `T` on a tree is faithful on its minimal subtree.
  This kills Clapham-type HNN and amalgam envelopes as `T` whenever their Bass--Serre
  action is faithful on the minimal subtree.
- If `T` is a non-elementary hyperbolic group, infinite normal subgroups contain
  elements of infinite order, and these are undistorted, so item 2 forces
  `N` finite. The same holds for acylindrically hyperbolic `T` by Osin's theorem
  that infinite normal subgroups contain loxodromics.

## Attempts

1. **Read off ambient class functions, and put rigid-stabilizer commutators
   inside `N` (2026-09-18).** See `class-finite-normal-subgroups-invisibility-proof`.
   The worker recorded this claim as established with an elementary, complete
   route, but no referee votes were returned for it: all votes were lost, so
   the result is recorded as an attempt and the claim stays OPEN. The route is
   kept. *Pending referee.*
