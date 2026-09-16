---
rg: 2
id: amenable-fp-pi2-complete-from-coset-cover-hardness
kind: route
title: Feed a hard double-coset cover family into the commuting-conjugate switch
target: amenability-of-finite-presentations-is-pi2-complete
requires:
  - amenable-fp-double-coset-cover-is-pi2-hard
  - commuting-conjugate-switch-amenability-criterion
  - amenability-of-finite-presentations-arithmetical-position
artifacts:
  - research/artifacts/commuting-conjugate-coset-switch-2026-09-16.md
---

## Why sufficient

Let `e -> (K_e = <X_e | R_e>, S_e, U_e)` be the computable family given by
`amenable-fp-double-coset-cover-is-pi2-hard`. Put `C_e = <S_e>` and
`D_e = C_e cup C_e U_e C_e cup C_e U_e^-1 C_e`.

**The map.** Let

```text
Q_e = < X_e, b | R_e, [b,s] (s in S_e), [b, u b u^-1] (u in U_e) >.
```

This is a finite presentation, and its code is computed uniformly from `e`.

**Correctness.** Item 2 of `commuting-conjugate-switch-amenability-criterion`
says that `Q_e` is amenable iff `K_e` is amenable and `K_e = D_e`. Every `K_e` is
amenable, so `Q_e` is amenable iff `K_e = D_e`, iff `e in TOT`.

**Hardness.** So `e -> Q_e` is a many-one reduction of `TOT` to `AMENABLE_fp`.
`TOT = {e : phi_e total}` is `Pi^0_2`-complete, so `AMENABLE_fp` is
`Pi^0_2`-hard.

**Membership.** `AMENABLE_fp in Pi^0_2` is the complement form of (AF1),
`NONAMENABLE_fp in Sigma^0_2`, of
`amenability-of-finite-presentations-arithmetical-position`.

Together these give `Pi^0_2`-completeness. On the positive branch the witness
is `Q_e = Z wr_(K_e/C_e) K_e`, a finitely presented permutational wreath
product. On the negative branch `b` and `k b k^-1` generate `F_2` for any
`k notin D_e`. `QED`

## Where this route can die

The whole content is in `amenable-fp-double-coset-cover-is-pi2-hard`. The hole
needs finitely presented amenable ambients with a finitely generated subgroup of
infinite index and finite bi-index, outside the virtually polycyclic and
abelian-by-virtually-abelian classes
(`finite-bi-index-forces-finite-index-in-metabelian-groups`). Its rank must be
controlled by a computation.
