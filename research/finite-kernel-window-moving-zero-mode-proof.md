---
rg: 2
id: finite-kernel-window-moving-zero-mode-proof
kind: route
title: Separate the quotient word from the finite kernel subgroup by Hall's theorem
target: finite-kernel-window-has-maximally-moving-zero-mode
requires: []
---

Let `H=<R>`. It is a finitely generated subgroup of the finitely generated
free group `F`. Because `H<=K` and `f_0 notin K`, one has `f_0 notin H`.
Hall's subgroup-separability theorem supplies a finite-index subgroup `L` of
`F` containing `H` but not `f_0`.

On `ell^2(F/L)` use the left coset permutation representation and set
`xi_R=delta_L`. For `k in R<=H<=L`,

```text
pi_R(k)delta_L=delta_(kL)=delta_L.
```

On the other hand `f_0L!=L`, so the two basis vectors `delta_(f_0L)` and
`delta_L` are orthogonal. This proves `(FKW1)`, `(FKW2)` and `(FKW4)`.
Every summand in `(FKW3)` annihilates `xi_R`, proving the zero-energy claim.

Notice why finite normal generation of `K` does not affect the example. The
vector is fixed by the chosen normal generators only at the base coset. It is
not fixed by all their `F`-conjugates, and its cyclic span is not a quotient
representation. Exactly this propagation is what `(IR1)` would have to
provide in the open retention claim.
