---
rg: 2
id: stw82-complemented-support-multiplier-proof
kind: route
title: Split off the residual ideal and apply fullness only on the supported summand
target: stw82-complemented-support-preserves-dimension
requires:
  - stw82-split-af-is-one-multiplier-projection-problem
artifacts:
  - research/artifacts/stw82-complemented-multiplier-support-audit-2026-08-30.md
---

Write `A=L direct_sum B` as in `(CS1)`.

## Step 1: identify complementation with central multiplier support

If `A=L direct_sum B`, the coordinate map

```text
z(l+b)=l
```

is implemented on both sides by a central projection `z in M(A)`, and
`L=zA`, `B=(1-z)A`.  Conversely, any central multiplier projection `z`
gives the orthogonal ideal decomposition

```text
A=zA direct_sum (1-z)A.
```

This proves the equivalence of the two formulations in the claim.

## Step 2: the multiplier projection annihilates the complement

Fix `b in B`.  Since `p` is a multiplier, `bp in A`, and

```text
(bp)(bp)^*=bpb^*.
```

The right side belongs to `L=closure(ApA)`.  It also belongs to `B`, because
`B` is an ideal and `pb^* in A`.  Hence `bpb^*=0`, as `L intersect B=0`,
and therefore `bp=0`.  Applying this to `b^*` and taking adjoints also gives
`pb=0`.  Thus

```text
pB=Bp=0.                                                   (CP1)
```

Expanding `ApA` with `A=L direct_sum B` and using `(CP1)` now gives

```text
L=closure(LpL).                                           (CP2)
```

Multiplication by `p` preserves `L` on both sides (this also follows
directly by approximating elements of `L` by sums from `ApA`), so
`p in M(L)`.  Equation `(CP2)` says exactly that `p` is full on `L`.

## Step 3: split the adjoined algebra exactly

Equation `(CP1)` makes `L+C p` and `B` orthogonal C*-subalgebras of
`A+C p`, and every element has a unique decomposition

```text
(l+lambda p)+b.
```

Hence `(CS3)` is a C*-algebra direct sum.  Notice that no commutation
between `p` and `L` was used.

Because `A` is sigma-unital and `L=zA` is a direct summand, `L` is
sigma-unital: if `(e_n)` is a countable approximate unit for `A`, then
`(ze_n)` is one for `L`.  Apply the full-multiplier-projection part of
`stw82-split-af-is-one-multiplier-projection-problem` to `(CP2)`:

```text
dim_nuc(L+C p)=dim_nuc(L).                               (CP3)
```

Nuclear dimension of a finite direct sum is the maximum, so `(CS3)` and
`(CP3)` give

```text
dim_nuc(A+C p)
 =max(dim_nuc(L+C p),dim_nuc(B))
 =max(dim_nuc(L),dim_nuc(B))
 =dim_nuc(A).
```

This proves `(CS2)`.

## Step 4: verify that the class is strictly nonfull and noncentral

In the example from the claim, multiplication by
`1_(B(H)) tensor e_11` generates all of `K(H) tensor M_2`, so

```text
closure(ApA)=(K(H) tensor M_2) direct_sum 0.
```

The nonzero second summand makes `p` nonfull in `A`.  On the other hand,
`e_11` fails to commute with `e_12`, so `p` is noncentral in `M(A)`.  The
support ideal is nevertheless complemented, and the theorem is not a
restatement of either earlier special case.
