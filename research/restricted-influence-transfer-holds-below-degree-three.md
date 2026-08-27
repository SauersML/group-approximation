---
rg: 2
id: restricted-influence-transfer-holds-below-degree-three
kind: claim
title: Restricted influence is bounded by ambient influence exactly when no full coset can be absorbed, i.e. up to ambient degree two
distinct_from:
  linear-pairing-memorizer-restricts-to-a-dictator: that exhibits the degree-(2r+1) counterexample; this is the positive inequality below degree three together with the exact combinatorial reason the two meet at three.
artifacts:
  - research/artifacts/unique-games-affine-orientation-2026-08-24.md
---

**ESTABLISHED.**  Keep the notation of `affine-orientation-glue-lemma`:
`Omega = F_2^k`, `b != 0`, `D_b` the affine-pair subcube, `C = {q, q+b}` a
coset, `g` a function on `{-1,1}^Omega`.

**The transfer inequality.**  If `deg g <= 2` then for every `d >= 1`

```text
Inf^{<=d}_C ( g|_{D_b} )  <=  2^d * ( Inf^{<=d}_q(g) + Inf^{<=d}_{q+b}(g) ).   (T1)
```

**Why 2, and why not 3.**  Restriction to `D_b` sends the character
`chi_S` to the quotient character `chi_{pi_b(S)}`, where `pi_b(S)` is the
set of `b`-cosets meeting `S` in an odd number of points.  Since a coset has
exactly two elements, `|S intersect [c]|` is `1` on each coset of
`T = pi_b(S)` and `0` or `2` on the others, so

```text
|S| = |T| + 2m,     m = number of cosets S contains entirely.               (T2)
```

`(T1)` is Cauchy--Schwarz over the fibre `{S : pi_b(S) = T}`, and it is
useful only when that fibre is small.  By `(T2)` the fibre has exactly
`2^{|T|}` elements when `m = 0` is forced, and `m = 0` is forced for every
`|T| >= 1` precisely when `deg g <= 2`.

At `deg g = 3` the fibre over a **singleton** `T = {C}` already contains
`Theta(N)` sets, one for each absorbed coset, and by
`linear-pairing-memorizer-restricts-to-a-dictator` the sum over that fibre
really can be coherent: the memorizer with `r = 1` has
`Inf_C(B|_{D_b}) = 1` while both ambient influences on the right of `(T1)`
are `Theta(1/N)`.  So `(T1)` is not merely unproved above degree two -- it
is **false**, with an explicit witness, at the first degree where coset
absorption is possible.

**Consequence.**  The obstruction to `affine-orientation-glue-lemma` is not
the low-degree truncation parameter `d` and not the noise parameter `rho`.
It is the **ambient** degree, and the transition is exactly at 3.  The whole
difficulty of the lemma lives in the tail

```text
hat{g|_{D_b}}({C}) = [ hat g(q) + hat g(q+b) ]
                     + sum_{m >= 1} sum_{R a union of m cosets, R disjoint from C}
                         [ hat g({q} union R) + hat g({q+b} union R) ],       (T3)
```

whose leading bracket is controlled by ambient influences and whose tail is
not.  Boundedness and noise have to act on the tail of `(T3)`; nothing else
in the problem does.

The proof is `restricted-influence-transfer-degree-two-proof`.
