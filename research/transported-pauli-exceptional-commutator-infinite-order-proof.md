---
rg: 2
id: transported-pauli-exceptional-commutator-infinite-order-proof
kind: route
title: The unique lowest Leavitt grade survives in every power
target: transported-pauli-exceptional-commutator-infinite-order
requires: []
artifacts:
  - experiments/atlas_double_pauli_comb_blocks.py
---

The exact prefix-algebra calculation behind `(POF10)` gives `h` as a sum of
21 reduced Leavitt monomials.  Give a prefix monomial `alpha beta^*` its
standard degree

```text
|alpha|-|beta|.
```

The degrees occurring in `h`, with multiplicities, are

```text
-8 (1), -7 (1), -5 (4), -4 (1), -3 (1), -2 (2), 0 (11).
```

The unique degree `-8` term is

```text
m = 00 (0010101010)^*.
```

Write

```text
a=00,   q=10101010,
```

so `m=a(aq)^*`.  The binary Leavitt prefix multiplication rule is

```text
(alpha beta^*)(gamma delta^*)
 = alpha epsilon delta^*       if gamma=beta epsilon,
 = alpha (delta epsilon)^*     if beta=gamma epsilon,
 = 0                           otherwise.
```

Since `aq` has prefix `a`, repeated reduction gives inductively

```text
m^n = a (a q^n)^*.
```

This is a reduced nonzero monomial for every `n>=1`.

The grading is multiplicative.  Every homogeneous summand of `h` has degree
at least `-8`, so a product of `n` summands has degree at least `-8n`.
Equality can occur only if every chosen summand has degree `-8`; because that
summand is unique, the entire degree `-8n` component of `h^n` is exactly
`m^n`.  In particular it cannot cancel against any other product term.

The identity has only degree `0`.  Therefore the nonzero degree `-8n`
component forces

```text
h^n != 1
```

for every `n>=1`, proving that `h` has infinite order.
