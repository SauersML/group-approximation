---
rg: 2
id: iterated-wreath-products-of-z-have-tower-folner-functions
kind: claim
title: The k-fold iterated wreath product of Z has Følner function at least a tower of height k-1
distinct_from:
  thompson-f-folner-function-exceeds-every-tower: that is Moore's tower lower bound for the one group F, vacuous unless F is amenable; this is an unconditional tower lower bound for a family of elementary amenable groups, one height per group.
  folner-functions-of-fp-amenable-groups-have-no-recursive-bound: that is the open claim that no recursive function bounds all finitely presented amenable groups; this gives only towers of fixed height, all below one primitive recursive bound.
  permutational-boone-higman-closed-under-wreath-products: that puts the iterated wreath products in the Boone--Higman class B_A; this bounds their Følner functions from below.
---

**ESTABLISHED (literature import plus a short induction)** by
`iterated-wreath-products-of-z-tower-folner-citation`.
The primary source was not opened. See the route for the verbatim secondary
statement.

## Statement

Conventions:
- `L wr A = L^(A) ⋊ A` is the restricted regular wreath product, with lamp group
  `L` and acting group `A`.
- `W_1 = Z` and `W_(k+1) = Z wr W_k`. So `W_2 = Z wr Z` and
  `W_3 = Z wr (Z wr Z)`.
- `exp_0(n) = n` and `exp_(j+1)(n) = 2^(exp_j(n))`.
- `f ≼ g` means that `f(n) <= C g(Cn)` for some `C` and all `n`, and `≃` means
  `≼` both ways.
- `F_W` is the Følner function for any finite generating set; its `≃`-class does
  not depend on the choice.

**Theorem.** For every `k >= 1` there are `c_k >= 1` and `n_k` with

```text
F_(W_(k+1))(n)  >=  exp_k(n / c_k)      for all n >= n_k.          (T)
```

Consequently `F_(W_(k+2))` is not `≼ exp_k` for any `k`. That is, for every
`C` the inequality `F_(W_(k+2))(n) <= C exp_k(Cn)` fails for all large `n`.

The groups `W_k` are elementary amenable and finitely generated. By
`permutational-boone-higman-closed-under-wreath-products` they lie in `B_A`, so
each embeds in a finitely presented simple group.
