---
rg: 2
id: properly-infinite-corner-non-mf-proof
kind: route
title: Make the corner full in itself and push the rank-two theorem through the corner embedding
target: properly-infinite-corner-forces-non-mf-from-rank-two
requires:
  - corner-unitization-embeds-elementary-groups
  - full-defect-ring-non-mf-at-rank-two
  - full-idempotent-ring-has-properly-infinite-unit
artifacts:
  - research/artifacts/fullness-corner-and-order-two-reduction-2026-09-08.md
---

## Why sufficient

Work in `B = pRp`, a countable unital ring with unit `p`, nonzero because
`p != 0`.  Put

```text
s = x_0,     t = y_0,     f = p - x_0 y_0.                        (1)
```

`(PIC1)` gives `ts = y_0x_0 = p`, so `s` has the proper one-sided inverse
`t` in `B` and `f = p - st` is its complementary idempotent there.  The
third prerequisite, in its `(2) => (1)` direction applied to `B` rather
than to `R`, says a properly infinite unit produces a full defect; here
the witness is a **single** element,

```text
y_1 f x_1 = y_1x_1 - (y_1x_0)(y_0x_1) = p - 0 = p,                (2)
```

using `y_1x_1 = p` and `y_1x_0 = 0`.  Hence `B f B = B`.  In particular
`f != 0`.

`B` is countable and nonzero and satisfies the hypothesis of
`full-defect-ring-non-mf-at-rank-two`.  So for every `n >= 2` and every MF
group `H`, every homomorphism `EL_n(B) -> H` is trivial.

By the first prerequisite, `iota_p : EL_n(B) -> EL_n(R)` is injective and
carries the corner elementary matrices to ambient ones.  Let
`phi : EL_n(R) -> H` with `H` MF.  Then `phi . iota_p` is an MF-target
homomorphism out of `EL_n(B)`, hence trivial, so `phi` kills
`iota_p(EL_n(B))`.  By `(CU2)` that subgroup contains `e_12(p)`, and
`e_12(p) != 1` since `p != 0`.  So no such `phi` is injective, and
`EL_n(R)` is not MF.

## The rank-three ideal refinement

For `n >= 3` the kernel `N` of `phi` contains `e_ij(p)` for all `i != j`.
Fix distinct `i,j,k`.  Direct multiplication of elementary matrices gives
the two identities `(PIC2)`.  The first, with `e_kj(p) in N` and `N`
normal, puts `e_ij(ap)` in `N` for every `a in R`; the second then puts
`e_ij(apb)` in `N` for all `a,b in R`.  Root subgroups are additive, so
`e_ij(c) in N` for every finite sum `c = sum a_l p b_l`, i.e. for every
`c in RpR`.

## What this route does not do

It does not reprove `full-defect-ring-non-mf-at-rank-two`, and it inherits
that theorem's property-(T) dependency through
`full-complementary-idempotent-elementary-full-mf-radical`.  It is
therefore not a property-(T)-free argument.
