---
rg: 2
id: deligne-eventually-similar-circularity-proof
kind: route
title: Margulis's theorem plus Deligne's residual computation verify the normal subgroup dichotomy, and the transfer theorem does the rest
target: deligne-lattice-eventually-similar-hosts-are-circular
requires:
  - fw-nst-inputs-virtually-embed-in-one-vertex-group
  - higher-rank-lattice-normal-subgroups-central-or-finite-index
  - deligne-universal-cover-lattice-is-non-rf-kazhdan
  - deligne-covers-of-sp2g-z-have-finite-residual-2z
  - type-a-actors-have-no-infinite-virtually-central-subgroup
---

Notation as in the target. Put `Z = ker p = <z>`.

## 1. Hypotheses 1 and 2 of the transfer theorem

`Gamma~` has property (T) (`deligne-universal-cover-lattice-is-non-rf-kazhdan`,
item 3), so it has property FW by step 3 of the route of
`fw-subgroups-of-eventually-similar-groups-virtually-embed`. `Z` is central and
infinite cyclic (item 1).

## 2. Two elementary facts on residual finiteness

- **`Sp_2n(Z)` is residually finite.** For `g != 1` choose `m` larger than every
  entry of `g - 1` in absolute value. The reduction `Sp_2n(Z) -> Sp_2n(Z/m)`
  does not send `g` to 1. Subgroups of residually finite groups are residually
  finite.
- **Residual finiteness ascends along finite index, and products preserve it.**
  If `M <= L` has finite index and `M` is residually finite, then `L` is: separate
  elements outside `M` through the finite quotient `L / core(M)`, and elements of
  `M` through the core of a finite-index subgroup of `M` avoiding them. A direct
  product of two residually finite groups is residually finite.

## 3. Hypothesis (D): the normal subgroup dichotomy

Let `L <= Gamma~` have finite index and `N` be normal in `L`. Then `p(L)` has
finite index in `Sp_2n(Z)` and `p(N)` is normal in `p(L)`. By
`higher-rank-lattice-normal-subgroups-central-or-finite-index`, either
`p(N) <= {+1, -1}` or `p(N)` has finite index in `p(L)`.

- **Case A: `p(N) <= {+1,-1}`.** The restriction of `p` to `N` has kernel
  `N cap Z` and image of order at most 2, so `[N : N cap Z] <= 2`.
- **Case B: `p(N)` has finite index in `p(L)`.** Suppose `N cap Z = 1`. Choose
  `a >= 1` with `L cap Z = <z^a>` (possible because `L` has finite index).
  - `M = N <z^a>` is a subgroup because `z` is central. It is the direct product
    `N x <z^a>`, because `N cap <z^a> = 1`.
  - `N` is isomorphic to `p(N)`, since `ker p = Z` meets `N` trivially. So `N` is
    residually finite (section 2).
  - `M` is residually finite, and `p(M) = p(N)`. Since `M` contains
    `L cap ker p`, `[L : M] = [p(L) : p(N)]`, which is finite.
  - So `L`, and then `Gamma~`, would be residually finite (section 2),
    contradicting item 4 of `deligne-universal-cover-lattice-is-non-rf-kazhdan`.

  Hence `N cap Z = <z^b>` with `b >= 1`, and
  `[L : N] <= [p(L) : p(N)] [L cap Z : N cap Z] < infinity`.

So (D) holds with this `Z`.

## 4. The transfer

By `fw-nst-inputs-virtually-embed-in-one-vertex-group` there are `L`, `F`, `s`
and an injective homomorphism `Q = L / F -> H_s`, with `F` finite normal in `L`,
`F cap Z = 1`, and the image of `L cap Z` central and infinite cyclic. That gives
item 2 of the target.

## 5. `Q` is not residually finite

By `deligne-covers-of-sp2g-z-have-finite-residual-2z`, the finite residual
`Res(Gamma~)` contains `<z^2>`.
- `Res(Gamma~)` is contained in every finite-index subgroup of `Gamma~`, in
  particular in `L`, so `z^2` lies in `L`.
- Every finite-index subgroup of `Q` pulls back to a finite-index subgroup of `L`,
  hence of `Gamma~`, and so contains the image of `z^2`. So the image of `z^2`
  lies in the finite residual of `Q`.
- The image is nontrivial because `F cap Z = 1`.

So `Q` is not residually finite. That is item 1.

## 6. No type (A) action

The center of `Q` contains an infinite cyclic subgroup. By corollary 3 of
`type-a-actors-have-no-infinite-virtually-central-subgroup`, `Q` has no action of
type (A). That is item 3.

## 7. The recovered special case

In the synchronous case every vertex group is residually finite (part 3 of
`fw-subgroups-of-eventually-similar-groups-virtually-embed`). By section 5 it
cannot contain `Q`, so `Gamma~` embeds in no such host. This includes the
Rover--Nekrashevych groups.
