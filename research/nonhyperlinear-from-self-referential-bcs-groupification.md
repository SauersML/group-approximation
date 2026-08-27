---
rg: 2
id: nonhyperlinear-from-self-referential-bcs-groupification
kind: route
title: A groupified self-referential BCS signal contradicts finite-dimensional microstates
target: non-hyperlinear-group
requires:
  - self-referential-bcs-nonzero-signal-collapse
  - hs-groupify-self-referential-bcs-signal
---

Let `Gamma,w,K,c` be supplied by `(SGB1)--(SGB2)`. By `(SBS1)` and `(SGB1)`,
`w!=1` in `Gamma`.

If `Gamma` were hyperlinear, its canonical trace would give finite-dimensional
tuples `U_n` with `Def_R(U_n)->0` and

```text
||w(U_n)-I||_2^2 -> 2.
```

Apply `(SGB2)` to obtain BCS strategies `S_n`. Their errors tend to zero, while

```text
liminf phi_(S_n)(D) >= 2c>0.
```

But `(SBS2)` gives

```text
phi_(S_n)(D)<=C_* epsilon(S_n)->0,
```

a contradiction. Therefore `Gamma` is nonhyperlinear.
