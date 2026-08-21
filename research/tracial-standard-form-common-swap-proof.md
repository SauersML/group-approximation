---
rg: 2
id: tracial-standard-form-common-swap-proof
kind: route
title: Compose conjugation maps to obtain one linear left-right swap
target: perfect-tracial-bcs-has-one-common-module-swap
requires: []
---

Let `H=L^2(M,tau)` for a finite tracial von Neumann algebra.  Denote by
`C:H->bar(H)` the canonical antiunitary and by

```text
J_tau(hat(x))=hat(x^*)
```

the tracial modular conjugation.  Their composite

```text
S=J_tau C^(-1):bar(H)->H
```

is a linear unitary.  Standard-form left-right duality gives

```text
J_tau R_a J_tau=L_(a^*).
```

Consequently, for every self-adjoint `a in M`,

```text
L_a S=S overline(R_a).                                (TSW1)
```

The construction depends only on `(M,tau)`, so the same `S` works
simultaneously for every context and every shared BCS variable.

For self-adjoint unitaries `a`, put on `H direct_sum bar(H)`

```text
J_S=[[0,S],[S^*,0]],
D_a=diag(L_a,overline(R_a)).
```

Both are self-adjoint unitaries, and `(TSW1)` is exactly
`[D_a,J_S]=I`.  If `F_c` is the forbidden projection of a perfect context,
then `F_c=0`, so the predicate reflection row also commutes with `J_S`.
Thus one common swap makes every required exact BCS Gram row vanish.
