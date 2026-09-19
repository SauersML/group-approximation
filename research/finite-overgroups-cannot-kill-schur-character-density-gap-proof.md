---
rg: 2
id: finite-overgroups-cannot-kill-schur-character-density-gap-proof
kind: route
title: Induce one active Schur simple to the proposed finite overgroup
target: finite-overgroups-cannot-kill-schur-character-density-gap
requires:
  - schur-predicate-is-character-density-difference
---

Choose `x` with `f(x)=1` and an irreducible negative-sector `B_f`-module
`T_x` above that selector character. Form the finite-dimensional induced
module

```text
V=Ind_(B_f)^K T_x.
```

Because `J` is central in `K` and acts as `-I` on `T_x`, it acts as `-I` on
all of `V`. Frobenius reciprocity, or the copy supported on the identity
coset, shows that `T_x` occurs in `V` restricted to `B_f`. Hence the selector
projection `P_f` acts nontrivially on `V`.

Apply `(CDF2)`:

```text
rho_V(Z_(C_f)-Z_(B_f))=rho_V(P_f)/(2D) != 0.
```

This is `(FOG1)`. Since the argument applies to every finite `K` containing
the packet, no collection of additional finite group relations implemented
solely by passing to such an overgroup can force the density gap to vanish.
