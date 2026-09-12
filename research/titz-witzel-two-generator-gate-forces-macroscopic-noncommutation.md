---
rg: 2
id: titz-witzel-two-generator-gate-forces-macroscopic-noncommutation
kind: claim
title: The first square in the two-generator Titz gate forces macroscopic noncommutation
distinct_from:
  titz-witzel-trivial-second-matching-collapses-mark: That sets one of the old matching variables equal to the identity and uses several old relators; this gives a quantitative obstruction in the final two-generator gate and uses only its derived square.
  titz-witzel-sofic-gate-two-generators-four-approximate-relators: That reduces soficity to a two-permutation finite problem; this proves a new necessary condition on every solution of that problem.
artifacts:
  - research/artifacts/titz-witzel-involution-sandwich-check.py
---

**THEOREM.**  Use the words in `(TW2G1)`, and suppose `e^2=1` in a
group with a bi-invariant metric `d`.  Put

```text
kappa = d(u e u^(-1),e),        delta = d(c^2,1).
```

Then

```text
d(u^8,1) <= delta + 6 kappa.                          (TWNC1)
d(u^8,1) <= delta + 2 d(e,1).                         (TWNC1')
```

Consequently, if `(e_n,u_n)` is any sequence of finite-permutation models
for the two-generator gate with

```text
d_H(c(e_n,u_n)^2,1) -> 0
```

and

```text
limsup_n d_H(u_n^8,1) = epsilon > 0,
```

then

```text
limsup_n d_H([u_n,e_n],1) >= epsilon/6.               (TWNC2)
limsup_n d_H(e_n,1) >= epsilon/2.                     (TWNC2')
```

In particular no asymptotically commuting, block-diagonal, or direct-product
ansatz for the two variables can solve the Titz--Witzel soficity gate with a
separated mark.  This conclusion already follows from the exact square
`e^2=1` and the first of the four approximate relators; the other three
approximate equations are not used.

---

### Proof

Write

```text
h = u e u^(-1),       a = e h e,       c = u^2 a u^2.
```

Since `e^2=1`, bi-invariance gives

```text
d(a,e) = d(e h e,e e e) = d(h,e) = kappa.             (1)
```

The usual telescoping estimate for conjugation gives

```text
d(u^m e u^(-m),e) <= m kappa                            (2)
```

for every positive integer `m`.  Cancel the common outer `u^2` terms in
`c^2` and `u^8`, and compare the two occurrences of `a` with `e`.  Using
(1) and (2) gives

```text
d(c^2,u^8)
 = d(a u^4 a,u^4)
 <= 2 d(a,e) + d(e u^4 e,u^4)
 <= 2 kappa + 4 kappa
 = 6 kappa.                                            (3)
```

The triangle inequality with `d(c^2,1)=delta` proves `(TWNC1)`.  There is a
sharper direct support estimate.  Because `e^(-1)=e`, the word

```text
a = e h e
```

is a conjugate of `h`, which is in turn a conjugate of `e`.  Therefore

```text
d(a,1) = d(h,1) = d(e,1).
```

Directly comparing `c=u^2 a u^2` with `u^4` now gives

```text
d(c,u^4) = d(a,1) = d(e,1),
d(c^2,u^8) <= 2 d(e,1),
```

and proves `(TWNC1')`.  In a bi-invariant metric
`d(u e u^(-1),e)=d([u,e],1)`, so taking limsups proves `(TWNC2)` and
`(TWNC2')`.

The attached dependency-free checker also evaluates `(TWNC1)--(TWNC1')`
on random finite permutation pairs.
