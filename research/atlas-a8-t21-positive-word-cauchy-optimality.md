---
rg: 2
id: atlas-a8-t21-positive-word-cauchy-optimality
kind: claim
title: No positive four-cycle word can improve the symmetric t21 Cauchy constant below 24
artifacts:
  - experiments/atlas_a8_t21_word_optimum.py
distinct_from:
  atlas-a8-t21-diagonal-energy-envelope: that optimizes diagonal weights for the audited length-eight word; this claim rules out changing to any other positive word in the same four directed generators as a source of a better symmetric constant.
---

Among all positive words in

```text
T={t01,t12,t23,t30}
```

representing `t21` in `GL_4(F2)`, the smallest possible coefficient

```text
sum_(t in T) count_t(w)^2
```

is `24`.  It is attained by the audited length-eight word, whose count vector is

```text
(2,0,2,4).
```

Consequently the established symmetric estimate

```text
||[U,lambda(t21)]||_2^2
 <=24 sum_(t in T)||[U,lambda(t)]||_2^2
```

cannot be improved merely by finding a different positive word for `t21` and
repeating commutator telescoping followed by ordinary Cauchy--Schwarz.

Any smaller symmetric transfer constant must exploit signed/non-positive group
identities, several identities simultaneously, cancellations visible before
the triangle inequality, or non-diagonal quadratic correlations.