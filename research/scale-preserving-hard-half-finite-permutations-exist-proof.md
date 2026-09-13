---
rg: 2
id: scale-preserving-hard-half-finite-permutations-exist-proof
kind: route
title: Diagonalize one transposition per dyadic block against clocked transducers
target: scale-preserving-hard-half-finite-permutations-exist
requires: []
---

Fix a recursive non-decreasing `R`. Fix a recursive enumeration `e -> M_e` of
all transducers (Turing machines with output tape) in which **every** transducer
appears as `M_e` for infinitely many `e`; this is standard (append ignored
padding to the index). All logarithms are base 2.

**Blocks.** For `j >= 0` put `B_j = { x in N : 2^j <= x < 2^(j+1) }`, of size
`2^j`. For `e >= 0` set `j(e) = e + 4`, so the `B_(j(e))` are pairwise disjoint
and each has at least `2^(e+3) >= 8` odd elements. Let `a_e` be the least odd
element of `B_(j(e))`.

**The clock.** For an input `x`, call a transducer `M` **`e`-fast at `x`** if
`M` on input `x` (written in unary) halts within `e*R(e*x) + e*x + e` steps.
This bound is computable from `e` and `x` because `R` is recursive.

**Definition of `gamma`.** `gamma` is the product of disjoint transpositions,
one contributed by each `e`:

- Run `M_e` on `a_e` for `e*R(e*a_e) + e*a_e + e` steps. If it halts with a
  natural-number output, call that output `v_e`; otherwise `v_e` is undefined.
- Let `b_e` be the **least** odd element of `B_(j(e))` with `b_e != a_e` and
  `b_e != v_e` (when `v_e` is undefined, only `a_e` is excluded). It exists:
  `B_(j(e))` has at least `8` odd elements, and at most two are excluded. The
  rule is deterministic, so `b_e` is a computable function of `e`.
- `gamma` swaps `a_e` and `b_e`.

On every point lying in no pair `{a_e, b_e}`, `gamma` is the identity. The pairs
are disjoint (distinct `e` use distinct blocks), so `gamma` is a well-defined
involution of `N`, hence a bijection with `gamma = gamma^-1`.

**Clause 1 (half-finite involution).** Every moved point `a_e, b_e` is odd, so
`gamma` fixes every even number. An involution fixing all even numbers fixes all
sufficiently large even numbers, so `gamma` has half-finite support in the sense
of `half-finite-generators-with-e2-are-strongly-shift-similar`.

**Clause 2 (scale-preserving, sub-double).** Each transposition `(a_e b_e)` has
both points in the one block `B_(j(e))`, so `gamma` maps each `B_j` onto itself.
For `x in B_j` with `j >= 1`, both `x` and `gamma(x)` lie in `[2^j, 2^(j+1))`,
so `2^j <= gamma(x) < 2^(j+1) <= 2x`, giving `x/2 < gamma(x) < 2x <= 4x`.
For `x = 1` (the block `B_0`), `gamma(1) = 1`.

**`gamma` is computable.** To evaluate `gamma(x)`: read `x`, compute
`j = floor(log x)`. If `j < 4`, output `x`. Otherwise `j = j(e)` for the unique
`e = j - 4`; compute `a_e`, run `M_e` on `a_e` for the clock to obtain `v_e` or
its absence, choose `b_e` by the rule above, and output `b_e` if `x = a_e`,
`a_e` if `x = b_e`, else `x`. Every step is recursive (the clock length is
computable because `R` is), so `gamma` is a total computable permutation. It is
not asserted to be fast.

**Clause 3 (`n -> gamma(n)` is not in `F(R)`).** Suppose it were: some
transducer `M` computes `x -> gamma(x)` in time `C*R(C*x) + C*x + C` for a fixed
`C`. Pick `e >= C` with `M_e = M` (possible, as `M` recurs infinitely often).
Since `R` is non-decreasing and `e >= C`,

```text
C*R(C*a_e) + C*a_e + C  <=  e*R(e*a_e) + e*a_e + e ,
```

so `M = M_e` halts on `a_e` within the `e`-clock and outputs `gamma(a_e)`. Hence
`v_e` is defined and `v_e = gamma(a_e)`. But by construction `gamma(a_e) = b_e`
and `b_e != v_e`, a contradiction. So no such `M` exists and
`n -> gamma(n) not in F(R)`. `∎`

**Remark (why this does not also settle the target).** The blocks are
diagonalized independently, with no finite rule linking `B_(j(e))` to
`B_(j(e'))`. Clause 1 of `fp-alt-fin-envelopes-are-unique-solutions-of-their-relators`
says a finite presentation of `< gamma, sl, flip, (1 2) >` would make `gamma`
the unique tuple satisfying finitely many relators; an independently
diagonalized `gamma` carries no such finite certificate, and this construction
provides none. The open content of
`hard-half-finite-permutations-have-fp-shift-envelopes` is exactly to replace
this block-by-block diagonalization by a single finite cross-scale rule whose
iterated evaluation still beats `R`.
