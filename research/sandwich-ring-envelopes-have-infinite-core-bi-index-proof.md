---
rg: 2
id: sandwich-ring-envelopes-have-infinite-core-bi-index-proof
kind: route
title: Congruence kernels over prime multiples give an infinite chain of proper normal subgroups, which the normal-height bound forbids
target: sandwich-ring-envelopes-have-infinite-core-bi-index
requires:
  - normally-generating-core-bi-index-bounds-normal-height
  - ck-steinberg-marked-cover
---

**(B).** For a two-sided ideal `I` of `R`, let

    C(I) = ker( EL_n(R) -> GL_n(R/I) ) ,

a normal subgroup of `EL_n(R)`. If `I ⊆ J` then `C(I) ⊆ C(J)`.

- *Proper.* If `I != R` then `e_12(1)` reduces to `e_12(1) != 1` in
  `GL_n(R/I)`, so `C(I) != EL_n(R)`.
- *Strict.* If `I ⊊ J`, pick `a in J \ I`. Then `e_12(a) in EL_n(R)` reduces
  to `1` modulo `J`, and to `e_12(a mod I) != 1` modulo `I`. So
  `e_12(a) in C(J) \ C(I)`.

An infinite strictly monotone chain of proper two-sided ideals, which exists
by dropping `R` from the hypothesized chain, gives an infinite strictly
monotone chain of proper normal subgroups `C(I_k)` of `EL_n(R)`. Their
preimages `pi^{-1}(C(I_k))` are proper normal subgroups of `Gamma`, and they
stay strictly monotone because `pi` is surjective. If `|S \ Gamma / S|` were
finite, `normally-generating-core-bi-index-bounds-normal-height` would bound
every such chain. So the bi-index is infinite.

**(U), `U/lU != 0`.** Fix a prime `l`. Let `lambda = max(dim_{F_l} F_l[T], aleph_0)`
and let `W = F_l[T]^{(lambda)}`, a direct sum of `lambda` copies of the group
algebra, so `dim_{F_l} W = lambda`. `Z[T]` acts on `W` coordinatewise by left
multiplication, through `F_l[T]`. Let `A in End(W)` be the action of `1-g`.
Because `g != 1` in `T`, `1-g != 0` in `F_l[T]`. So the vectors
`(1-g) e_i`, meaning `1-g` placed in coordinate `i`, for `i < lambda`, are
linearly independent vectors in `im A`. Hence `dim im A = lambda`. Choose a
complement `C` of `ker A`. Then `A|_C : C -> im A` is an isomorphism, so
`dim C = lambda = dim W`.

Choose a linear isomorphism `Q : W -> C`. Then `AQ : W -> im A` is bijective.
Let `P` be `(AQ)^{-1}` on `im A`, extended by `0` on a complement of `im A`.
Then `P A Q = 1_W`. By the universal property of `U`, `p |-> P`, `q |-> Q`
together with the `Z[T]`-action define a unital ring homomorphism
`U -> End_{F_l}(W)`. It sends `l` to `0` and `1` to `1 != 0`, since
`W != 0`. Hence `1 notin lU`.

**(U), the chain.** `m_k U` is a two-sided ideal because `m_k` is central.
`m_{k+1} U ⊆ m_k U`. Suppose `m_k in m_{k+1} U = m_k l_{k+1} U ⊆ l_{k+1} U`.
Since `m_k` is coprime to `l_{k+1}`, there are integers `c, d` with
`c m_k + d l_{k+1} = 1`, so `1 in l_{k+1} U`. That contradicts the previous
paragraph. So the inclusions are strict, and every `m_k U ⊆ l_1 U` is proper.

**Consequence.** `ck-steinberg-marked-cover` supplies, for every marking,
`Gamma ->> EL_4(U)` with `g != 1` in `T`. Apply (B) with `R = U`, `n = 4`.
The hypothesis `N ∩ S = 1` is part of the conclusion being tested, so the
statement is: whichever core has it, the bi-index is infinite.

∎

## Remark on what is actually used

Only three things are used: a unital ring map `U -> End(W)` factoring through
characteristic `l` for infinitely many `l`, the reduction maps on `EL_n`, and
the modular-law bound. No property (T), finite presentation, or root-subgroup
double-coset combinatorics are needed. That is why the obstruction is
insensitive to the marking, the corner and the core.
