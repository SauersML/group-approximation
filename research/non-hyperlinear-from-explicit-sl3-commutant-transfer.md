---
rg: 2
id: non-hyperlinear-from-explicit-sl3-commutant-transfer
kind: route
title: The explicit two-generator SL_3(Z) commutant modulus makes a literal finitely presented HNN group non-hyperlinear
target: non-hyperlinear-group
requires:
  - explicit-sl3-hnn-mark-is-fd-invisible
  - thin-sln-robust-relative-commutant-transfer
---

Use the matrices `a,b,r` of `explicit-sl3-thin-codense-tau-pair` and form

```text
G_exp = < SL_3(Z), t | [t,a]=1, [t,b]=1 >,
w_exp = [t,r].                                          (EXH1)
```

The unconditional exact conclusions, including `w_exp != 1` and its collapse
in every finite-dimensional unitary representation, are recorded in
`explicit-sl3-hnn-mark-is-fd-invisible`.

If `G_exp` were hyperlinear, canonical-trace matrix microstates restricted
to `SL_3(Z)` would have vanishing presentation defect, while the matrix `v`
assigned to `t` would satisfy

```text
||[v,a(U)]-1||_2 + ||[v,b(U)]-1||_2 -> 0.              (EXH2)
```

The explicit `n=3`, `C=<a,b>`, `r` specialization of
`thin-sln-robust-relative-commutant-transfer` would imply

```text
||[v,r(U)]-1||_2 -> 0.                                 (EXH3)
```

But `w_exp` is nonidentity, so canonical-trace microstates require the same
quantity to tend to `sqrt(2)`.  This contradiction proves `G_exp`
non-hyperlinear once the one-unitary transfer modulus is established.

This is stronger than the previous existential endpoint: the base group,
two HNN relators, outsider, and marked word are all displayed explicitly.
