---
rg: 2
id: length-ten-external-return-centralizer-enumeration
kind: route
title: Enumerate bounded external-return words and test full Singer commutation
target: length-ten-external-returns-have-no-active-singer-centralizer
requires:
  - signed-hecke-normalizer-has-eight-external-root-returns
  - eight-external-returns-have-no-whitehead-gauge-lock
  - native-whitehead-hecke-head-has-order-seven-anchor
---

Represent a binary `7`-by-`7` matrix by its seven bit rows in coordinate
order `(2,4,5,6,7,8,9)`.  The artifact inserts the ten generators of `L_0`,
the eight external transvections, and the two complete Singer heads

```text
t_1=(7 8)x_84(1)x_47(1),
t_2=(8 9)x_95(1)x_58(1).                              (1)
```

First close `L_0` together with the two row-specific fixed external roots;
both closures contain exactly `32768` matrices.  Then perform breadth-first
search from the identity using all eight involutive external generators.
Consecutive repetitions are omitted because they cancel.  A matrix is
queued only on its first occurrence, so after depth `d` the visited set is
exactly the set of matrices with external word length at most `d`.

For every newly visited matrix `g`, test the literal binary matrix equality

```text
g t_i = t_i g                                             (2)
```

and, if `(2)` holds, exact membership in the already closed spectator
subgroup.  Through depth ten no matrix passes `(2)` outside that subgroup.
The state counts are `(LTC3)`, below the artifact's explicit `500000`-state
cap, so the cap never truncates either enumeration.  This proves `(LTC2)`.
