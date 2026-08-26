---
rg: 2
id: one-depth-two-monomial-does-not-return-cross-whitehead
kind: claim
title: One depth-two monomial or matched partial Whitehead does not return an individual cross Whitehead
artifacts:
  - experiments/individual_cross_whitehead_depth_two_return_search.py
  - research/one-depth-two-cross-whitehead-return-enumeration.md
distinct_from:
  one-depth-one-occurrence-does-not-return-cross-whitehead: that permits arbitrary forward and reverse coefficients in a three-factor depth-one opposite word; this extends every elementary coefficient through depth two and extends the genuine partial-inverse Whiteheads using the uniquely matched reverse matrix unit.
  dyadic-cross-whitehead-fusion-has-finite-product-gauge: that factors each coarse cross Whitehead into same-address suffix-private factors and studies their fused gauge; this searches one new depth-two occurrence at every actor root position against both full signed-Hecke targets.
  two-depth-one-leavitt-roots-return-only-constantly: that searches two elementary depth-one exits without the fixed nonlinear `K_i`; this retains `K_i`, allows one depth-two root or genuine partial Whitehead, and tests the native `J_1` target as well as the source.
---

**ESTABLISHED DEPTH-TWO RETURN FENCE.**  Retain `K_0,K_1`, the signed
Hecke pair `(L_0,lambda_0)`, its projection `Q`, and `J_1` from
`one-depth-one-occurrence-does-not-return-cross-whitehead`.

Let

```text
W_2={empty,0,1,00,01,10,11},
D_2={s_mu t_nu: mu,nu in W_2,
                   (mu,nu)!=(empty,empty)}.            (DTM1)
```

Thus `D_2` is the complete set of `48` nonidentity exact prefix monomials
whose source and range prefixes each have length at most two.  At each of
the `42` oriented actor root positions, test the two types

```text
L=x_ab(s_mu t_nu),                                    (DTM2)

L=x_ab(s_mu t_nu)x_ba(s_nu t_mu)x_ab(s_mu t_nu).     (DTM3)
```

The second word is the genuine matched partial Whitehead: its two
coefficients have reverse products `e_mu` and `e_nu`.  The menu contains
`2016` elementary roots and `2016` matched Whiteheads, or `4032` candidates
for each branch and target.

For the source target, the exact test is

```text
LK_i in Norm(L_0,lambda_0).                            (DTM4)
```

For each `i`, exactly two candidates pass.  They are again only the two
partial-Whitehead braid spellings

```text
K_0=x_78(p)x_87(r)x_78(p)=x_87(r)x_78(p)x_87(r),
K_1=x_78(r)x_87(p)x_78(r)=x_87(p)x_78(r)x_87(p).       (DTM5)
```

Every hit therefore has `L=K_i` and `LK_i=1`.

For the native target, none of the `4032` candidates satisfies

```text
J_1^(-1)LK_i in Norm(L_0,lambda_0).                   (DTM6)
```

In fact the single signed generator `h=x_28(1)` is already a complete
prefilter for this menu.  Across the four branch/target cases, the numbers
passing its constant-matrix membership and character test are respectively

```text
K_0 -> Q: 2,       K_0 -> J_1Q: 0,
K_1 -> Q: 2,       K_1 -> J_1Q: 0.                   (DTM7)
```

The four source survivors then pass all other nine signed-generator tests
and are asserted to equal `K_i`; there are no other survivors.  The exact
audit performs

```text
2 branches * 2 targets * 4032 candidates = 16128      (DTM8)
```

candidate tests under a hard cap of `18000`.

This closes only the smallest requested boundary.  It does not treat an
unmatched/asymmetric depth-two three-factor word, a coefficient sum, a
depth-three monomial, or two additional nonnormal occurrences.  Any genuine
return must use at least one of those features; one exact depth-two monomial
or its matched partial Whitehead merely reproduces the old cancellation.

No Property T, Kazhdan input, trace hypothesis, local computation,
literature theorem, or Lean compilation is used.

DERIVATION
one-depth-two-cross-whitehead-return-enumeration
