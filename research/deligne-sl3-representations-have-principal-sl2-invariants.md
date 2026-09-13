---
rg: 2
id: deligne-sl3-representations-have-principal-sl2-invariants
kind: claim
title: Deligne's representations of SL_3(F_q) have a 2-dimensional principal-SL_2 fixed space, so they do not converge strongly
artifacts:
  - research/artifacts/sl3z-invariant-vector-witnesses-2026-09-12.md
---

ESTABLISHED (unreviewed).  Let `q` be an odd prime and `pi` a representation of
`SL_3(F_q)` of degree `(q-1)(q^2-1)` from Magee--de la Salle, arXiv:2312.03220v2,
Example 2.2 (restriction of a cuspidal representation of `GL_3(F_q)`; it has no
fixed vector for the block `SL_2(F_q)`).  Let
`Omega_q = Sym^2(SL_2(F_q)) = PSL_2(F_q)`, the principal `SL_2` acting on
binary quadratic forms.  Then

```text
dim pi^(Omega_q) = 2.
```

Consequently, with `S, T` the standard generators of `SL_2(Z)` and
`x = Sym^2(S) + Sym^2(S)^(-1) + Sym^2(T) + Sym^2(T)^(-1)` in `C[SL_3(Z)]`,
every such `pi` (pulled back to `SL_3(Z)`) has `||pi(x)|| = 4`, while
`||lambda_(SL_3(Z))(x)|| < 4` because `Sym^2(SL_2(Z)) = PSL_2(Z)` is
nonamenable.  So no sequence of these representations, the candidates that
escape the `SL_4(Z)` obstruction, converges strongly to the regular
representation.
