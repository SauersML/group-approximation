---
rg: 2
id: sl3-regular-double-collapse-from-projective-transfer
kind: route
title: Apply projective transfer to the block swap of the two regular double vertices
target: sl3-regular-arithmetic-double-fold-mark-collapse
requires:
  - projective-trace-square-transfer-for-sl3-pair
---

Let `sigma_n` be canonical-character microstates of `D=A*_C A`, with
vertex assignments `pi_(n,0),pi_(n,1)`.  On the doubled matrix space put

```text
rho_n(a)=diag(pi_(n,0)(a),pi_(n,1)(a)),
V_n(x,y)=(y,x).
```

The amalgamating relators make `[V_n,rho_n(c)]` tend to `1` for every
generator `c` of `C`, and the two vertex defects make `rho_n` an approximate
assignment of `A`.  Apply projective trace-square transfer at `h`.  It gives

```text
|tr([V_n,rho_n(h)])| -> 1.                                (RDP1)
```

The two diagonal blocks of this commutator are `pi_(n,1)(h)
pi_(n,0)(h)^*` and its inverse counterpart.  Hence `(RDP1)` says the
fold-kernel word has trace of modulus tending to one.  Canonical character
would make that trace tend to zero because the word is nontrivial.  Thus no
canonical-character microstate sequence exists; equivalently the asserted
fold-mark collapse holds (after passing to the contradiction formulation
used in the target).

This route is intentionally one-way.  The target sees only full regular
double microstates, while projective transfer quantifies over arbitrary
approximate `A`-assignments and arbitrary auxiliary unitaries.

