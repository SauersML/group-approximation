---
rg: 2
id: two-depth-one-nonnormal-roots-do-not-return-cross-whitehead
kind: claim
title: Two nonnormal depth-one roots in different channels do not return an individual cross Whitehead
artifacts:
  - experiments/individual_cross_whitehead_two_depth_one_roots_return_search.py
  - research/two-depth-one-cross-whitehead-return-enumeration.md
distinct_from:
  two-depth-one-leavitt-roots-return-only-constantly: that asks whether two depth-one elementary exits alone return to the signed normalizer; this fixes one nonlinear `K_i` after the two roots and tests both its source coset and the native `J_1` coset.
  one-depth-one-occurrence-does-not-return-cross-whitehead: that permits only one added occurrence, though it may be a three-factor Whitehead; this permits two separately nonnormal elementary occurrences in genuinely different actor root channels.
  one-depth-two-monomial-does-not-return-cross-whitehead: that increases coefficient depth for one root or one matched partial Whitehead; this keeps depth one but crosses the two-additional-occurrence boundary exhaustively.
---

**ESTABLISHED TWO-EXIT RETURN FENCE.**  Retain the individual cross-branch
Whiteheads `K_i`, the signed pair `(L_0,lambda_0)`, `Q`, and `J_1`.  Let
`D_1` be the eight nonconstant depth-one prefix matrix units from `(DOR2)`.

Among all roots

```text
x_ab(c),                  a!=b, c in D_1,              (TDR1)
```

exactly `304` fail to normalize `(L_0,lambda_0)`.  They occupy `38` of the
`42` oriented actor root positions.  Choose an ordered pair

```text
L=x_ab(c)x_de(f)                                      (TDR2)
```

of these individually nonnormal roots and require `(a,b)!=(d,e)`.  Thus
the two added occurrences lie in genuinely different root channels.  There
are exactly

```text
38*37*8*8=89984                                      (TDR3)
```

ordered candidates for each branch and target.

For the source target, the exposed signed generator `h=x_28(1)` leaves
exactly one candidate in each branch:

```text
i=0: L=x_87(r)x_78(p),
i=1: L=x_87(p)x_78(r).                               (TDR4)
```

Neither is a full signed return.  Indeed elementary involutivity and the
definition of `K_i` give

```text
x_87(r)x_78(p)K_0=x_78(p),
x_87(p)x_78(r)K_1=x_78(r).                           (TDR5)
```

The remaining root is itself nonnormal and fails another generator of the
full signed signature.  Consequently there are no solutions to

```text
LK_i in Norm(L_0,lambda_0).                          (TDR6)
```

For the native target there is not even an exposed-row survivor:

```text
J_1^(-1)LK_i notin Norm(L_0,lambda_0)                 (TDR7)
```

for every candidate `(TDR2)` and both `i=0,1`.

The deterministic exact audit checks the `h` image first and then all other
nine generators, including membership in the complete `8192`-element
constant group and preservation of `lambda_0`.  It performs

```text
2 branches * 2 targets * 89984 = 359936              (TDR8)
```

candidate tests under a hard cap of `400000`.  The full hit count is zero
in all four cases.

This is a complete no-go only for two individually nonnormal depth-one
**elementary** occurrences in distinct channels.  An asymmetric/unmatched
three-factor Whitehead, a depth-two coefficient in a two-occurrence word,
or three additional channels remains outside the enumerated menu.  Those
families were not appended to the same run: the complete two-root frontier
already uses the bounded fast-job window, and multiplying it by a
three-factor menu would be a Cartesian explosion.

No Property T, Kazhdan input, trace hypothesis, local computation,
literature theorem, or Lean compilation is used.

DERIVATION
two-depth-one-cross-whitehead-return-enumeration
