---
rg: 2
id: stw99-lxxvi-compact-counterexample
kind: claim
title: A pure C*-algebra fails Cuntz semigroup regularity on compact classes
root: true
---

There is a separable pure C*-algebra `A` for which

```text
Cu(A) -> Cu(A tensor_min Z)
```

is not injective on compact elements.  Such an algebra is a counterexample to
STW Problem LXXVI.

## Attempts

The live route is `stw99-lxxvi-compact-counterexample-via-local-collapse`.
Its genuinely open input is an ideal-local collapse witness.  Toeplitz index
data fail the necessary local K0 equality in the stably finite corridor,
while the established zero-dimensional locally subhomogeneous class is
already Z-stable.  A second live route allows the images to become infinite,
where Cu equality need not preserve K0.
