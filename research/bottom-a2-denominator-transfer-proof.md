---
rg: 2
id: bottom-a2-denominator-transfer-proof
kind: route
title: Feed two Steinberg long-root bounds into the opposite-root denominator estimate
target: bottom-a2-dyadic-face-obeys-denominator-transfer
requires:
  - involutory-steinberg-simple-root-forces-long-root-involution
  - involutory-opposite-root-face-obeys-projective-transfer
---

Apply `involutory-steinberg-simple-root-forces-long-root-involution` to
`(p,q,a)` and `(r,s,b)`. It gives

```text
||a^2-I||_2<=D_a,       ||b^2-I||_2<=D_b.                (BAD1)
```

Next telescope the commutator words. Since `c_a=[p,q]` contains two
occurrences each of `p` and `q`, moving `U` through that fixed word gives

```text
||Uc_a-c_aU||_2<=2 epsilon_p+2 epsilon_q.
```

Replacing `a` by `c_a` at the two ends costs `2 gamma_a`; hence

```text
||Ua-aU||_2<=E_a.                                       (BAD2)
```

The identical argument gives `||Ub-bU||_2<=E_b`.

Finally apply `involutory-opposite-root-face-obeys-projective-transfer` with
the denominator residual `(BA3)`, square defects bounded by `(BAD1)`, and
centrality defects bounded by `(BAD2)`. Its estimate is exactly

```text
2(eta+D_a+D_b)+2E_a+E_b,
```

which is `(BA4)`.

