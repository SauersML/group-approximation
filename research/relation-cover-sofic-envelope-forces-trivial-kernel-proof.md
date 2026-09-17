---
rg: 2
id: relation-cover-sofic-envelope-forces-trivial-kernel-proof
kind: route
title: Push the abelian kernel into the lamps and let the Kazhdan lamp lemma annihilate it
target: relation-cover-sofic-envelope-forces-trivial-kernel
requires:
  - kazhdan-subgroups-of-lamp-wreaths-meet-base-in-torsion
  - kazhdan-rational-relation-cover-reduction
artifacts:
  - research/relation-cover-sofic-envelope-forces-trivial-kernel.md
---

Notation as in the claim. Standard facts used:

- property (T) passes to quotients;
- a Kazhdan group has finite abelianization (Bekka--de la Harpe--Valette,
  *Kazhdan's Property (T)*, Corollary 1.3.6).

From `kazhdan-rational-relation-cover-reduction` we use:

- item 1, the torsion criterion (RLT);
- item 3, `K` is Kazhdan;
- item 4, the injective homomorphism `K -> V semidirect Q`,
  `p R_sat -> (1 (x) (p - 1), pi(p))`.

From `kazhdan-subgroups-of-lamp-wreaths-meet-base-in-torsion` we use the main
statement: a Kazhdan subgroup of `W wr_X Q` meets `(+)_X W` only in torsion.

## Item 1

Let `iota : V -> (+)_X W` be injective and `Q`-equivariant. Then
`(v, c) -> (iota v, c)` is an injective homomorphism
`V semidirect Q -> W wr_X Q`. Composing with the item-4 embedding gives an
injective homomorphism `j : K -> W wr_X Q`.

For `r in R`, `pi(r) = 1`, so `j(r R_sat) = (iota(1 (x) (r - 1)), 1)` lies in
the base `B = (+)_X W`. Hence `j(A) <= j(K) cap B`.

`K` is Kazhdan (item 3 of the reduction), so `j(K)` is a Kazhdan subgroup of
`W wr_X Q`. By the lamp lemma, `j(K) cap B` is torsion, so `j(A)` is torsion.
But `j` is injective and `A` is torsion-free (it is `R^ab / tors(R^ab)`), so
`A = 0`. That means `R_sat = R`, so `R^ab = tors(R^ab)` and `K = P/R = Q`.

## Item 2

Assume item 1's hypothesis, so `R_sat = R`.

- If `Q` has an element `pi(f)` of prime order `l`, then `f^l in R = R_sat`,
  and (RLT) fails at `f`.
- If `Q` is torsion-free, (RLT) is vacuous.

`EL_3(T)` for a ring `T` of characteristic `p` contains
`e_12(1)`, of order `p`.

## Item 3

(a) => (b). Take `Q, P, pi` witnessing (a). By item 1, `K = Q`. By item 1 of
the reduction, (RLT) makes `K` torsion-free, so `Q` is torsion-free. `Q` is
sofic, Kazhdan and nontrivial with no nontrivial finite quotient.

(b) => (a). Let `Q` be as in (b) and take `P = Q` with `pi = id`, so `R = 1`.

- Clause 1 is vacuous, since `Q` has no elements of prime order.
- `ZQ (x)_{ZQ} I_Q = I_Q`, so `V = QQ (x)_Z I_Q`. That is the augmentation
  ideal of `QQ[Q]`, which is a `Q`-submodule of `QQ[Q] = (+)_Q QQ`. So clause 2
  holds with `W = QQ`.
- `Q` is finitely generated, being Kazhdan.

## Item 4

Let `N <= R` be normal in `P`, with `N^ab` torsion.

The image `T` of `N` in `R^ab = R/[R,R]` is `N[R,R]/[R,R]`, which is
isomorphic to `N/(N cap [R,R])`. This is abelian, and `[N,N] <= N cap [R,R]`.
So `T` is a quotient of `N^ab`, hence torsion. Therefore `N <= R_sat`.

The kernel of `pi-bar : P/N ->> Q` is `R/N`, and

```text
(R/N)^ab = R / N[R,R] = R^ab / T.
```

Since `T` is torsion, a class `x in R^ab` is torsion if and only if its image
in `R^ab / T` is torsion. Indeed, if `n x in T`, then `m n x = 0` for some
`m >= 1`. So the preimage in `R` of `tors((R/N)^ab)` equals the preimage of
`tors(R^ab)`, which is `R_sat`. Hence `(R/N)_sat = R_sat / N`, and

```text
K(pi-bar) = (P/N)/(R_sat/N) = P/R_sat = K(pi),     A(pi-bar) = A(pi).
```

For `f in P` with `pi(f)` of prime order `l`, `f^l in R_sat` if and only if
`(fN)^l in R_sat/N`, because `N <= R_sat`. So (RLT) for `pi` and for `pi-bar`
are the same condition.

If `N` is a quotient of a Kazhdan group, it is Kazhdan, so `N^ab` is finite.

## Item 5

`belegradek-osin-rips-construction` gives `1 -> N -> G -> Q' -> 1` with `N` a
quotient of `H`. So `N^ab` is finite. `N` is contained in the kernel of
`G ->> Q' ->> Q`. Apply item 4.

## Reading of clause 2

The reduction proof (Section 4, "Soficity") calls `iota` "`QQ`-linear" and
uses `(v,c) -> (iota v, c)` as a homomorphism. That is a homomorphism exactly
when `iota` is `Q`-equivariant, which is the reading used here. If `iota` were
only `QQ`-linear, clause 2 would hold for every countable `V` and give no
soficity. So under either reading, the soficity mechanism of clause 2 gives
nothing when `A != 0`.

## Scope

- Nothing above uses soficity of `Q`, finite presentation, or the specific
  shape of `(+)_X W` beyond its being a permutation module of an abelian group.
- Item 1 does not exclude soficity of `K` with `A != 0` by other means. It
  excludes only embeddings of `K` into lamp wreath products that carry `A` into
  the lamps. By the lamp lemma applied to `K` directly, that covers every
  embedding of `K` into any `W wr_X L`, for any group `L`, in which `A` lands in
  the base.
