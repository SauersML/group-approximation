---
rg: 2
id: julia-asynchronous-mirror-neutrality-proof
kind: route
title: Compare the one-sided infinite defect pair with the balanced finite Julia defect pair
target: julia-colligation-is-neutral-to-the-asynchronous-mirror-exit
requires:
  - inside-corner-hecke-tests-miss-the-asynchronous-mirror-exit
---

For every contraction `A`, functional calculus gives

```text
A(E-A^*A)^(1/2)=(E-AA^*)^(1/2)A.                      (JMP1)
```

Block multiplication using `(JMP1)` proves `J_A^*=J_A` and `J_A^2=1`.

If `T` sends `EH` isometrically into itself with range `FH`, then `A=TE` on
`EH`, so `A^*A=E` and `AA^*=F`; this is `(JCM3)`.

For the finite counterpacket, decompose the space as

```text
FH direct-sum HH direct-sum CH direct-sum R
```

and transpose `H` with `C`.  Compression by `E` deletes the `H -> C` block,
leaving `A=F`.  Since `F` is a projection,

```text
E-A^*A=E-AA^*=H,
```

and square roots do nothing.  Hence the Julia matrix is an exact reflection
while its initial defect has trace `tr(H)`.  Substitution proves the failure
of `(JCM6)`.
