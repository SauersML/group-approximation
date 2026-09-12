---
rg: 2
id: compressors-conjugate-leak-free-root-pairs
kind: claim
title: Two explicit Leavitt compressors simultaneously conjugate every leak-free root pair of EL_3 to a compressed root pair
distinct_from:
  shifted-root-pair-conjugates-to-idempotent-root-pair: that conjugates the single shifted pair (x_12(t_0), x_23(s_0)) to the idempotent pair; this gives two families of simultaneous conjugacies, parametrized by all coefficients in R t_1 t_1 on the 23 root or in s_1 R on the 12 root.
artifacts:
  - research/artifacts/el3-compressor-root-pair-calculus-2026-09-12.md
---

Let `R = L_(F_2)(1,2)` and `EL_3(R) = GL_3(R)`. There are units `c`, `c'` in `GL_3(R)`
(artifact Section 1, explicit formulas) such that for all `a, a', b, b'` in `R`:

```text
c  (x_12(a), x_23(b' t_1 t_1)) c^-1   = (x_12(s_0 a t_0),  x_23(s_0 b')) ,
c' (x_12(s_1 a'), x_23(b)) c'^-1      = (x_12(t_1 a' t_0), x_23(s_0 b t_0)) .
```

Conjugation by `c` sends `x_23(b)` to a root element exactly when `b` lies in `R t_1 t_1`;
otherwise it leaks into `x_21` and a diagonal unipotent. Conjugation by `c'` sends `x_12(a)` to a
root element exactly when `a` lies in `s_1 R`.

Consequently, in every characteristic-two rank model, with `delta(a,b) = rk(n_23(b) n_12(a))`,

```text
delta(a, b' t_1 t_1) = delta(s_0 a t_0, s_0 b') ,     delta(s_1 a', b) = delta(t_1 a' t_0, s_0 b t_0) .
```

**ESTABLISHED** by `compressors-conjugate-leak-free-root-pairs-proof`: explicit computation on
column vectors, with a commutator consistency check.
