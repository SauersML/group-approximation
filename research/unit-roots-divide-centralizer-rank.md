---
rg: 2
id: unit-roots-divide-centralizer-rank
kind: claim
title: If a transcendental unit of an algebra over a field has a k-th root, then k divides its centralizer rank, so a unit with roots of unbounded order has infinite centralizer rank
distinct_from:
  leavitt-heisenberg-centers-have-infinite-centralizer-rank: that forces infinite rank from a Heisenberg pair or from a power conjugacy t x t^-1 = x^k; this forces divisibility of the rank by k from a k-th root, and infinite rank from roots of unbounded order, in any algebra over any field.
  leavitt-thompson-units-have-finite-centralizer-rank: that bounds the rank of conjugates of Thompson units in L_(F_2)(1,2); this is a general divisibility lemma, which that bound turns into a bound on roots.
  leavitt-unit-centralizers-have-finite-rank: that conjectures finite rank for every infinite-order Leavitt unit; this shows that conjecture would exclude every unit with roots of unbounded order.
---

**ESTABLISHED** (proof: `unit-roots-divide-centralizer-rank-proof`). Not independently reviewed.

## Statement

Let `K` be a field, `R` a unital `K`-algebra, and `x` a unit of `R` that is transcendental over `K`
(no nonzero polynomial `p in K[s]` has `p(x) = 0`). Put `C_x = C_R(x)` and

```text
rho(x) = dim_(K(x)) K(x) ⊗_(K[x]) C_x   in {1, 2, ..., ∞},
```

the centralizer rank of `leavitt-heisenberg-centers-have-infinite-centralizer-rank` (there with `K = F_2`).

1. If `x = y^k` for some `y in R` and `k >= 1`, then `rho(x)` is a multiple of `k` (or infinite). In
   particular `rho(x) >= k`.
2. If `x` has `k`-th roots in `R` for infinitely many `k`, then `rho(x) = ∞`.
3. Over a finite field `K = F_q` every unit of infinite order is transcendental. So if a group `D` with a
   nontrivial divisible element (for instance `(Q,+)`, or `Z[1/p]` with its `p^m`-th roots) embeds in `R^x`,
   the image of every element of `D` of infinite order that has roots in `D` of unbounded order has infinite
   centralizer rank. In `(Q,+)` that is every nonzero element.

## Use

- For the binary Leavitt algebra it turns the finite-rank bound of
  `leavitt-thompson-units-have-finite-centralizer-rank` into a bound on roots
  (`thompson-units-have-few-roots-in-leavitt-unit-group`).
- It shows the open conjecture `leavitt-unit-centralizers-have-finite-rank` would exclude `(Q,+)`, and with it
  `GL_n(Q)` for every `n >= 2`, from `L_(F_2)(1,2)^x`
  (`no-rationals-in-leavitt-units-from-finite-centralizer-rank`).
