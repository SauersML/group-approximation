---
rg: 2
id: binary-jacobson-elementary-mark-is-finite-quotient-invisible
kind: claim
title: Every finite quotient of the binary Jacobson elementary group kills the head root
artifacts:
  - research/binary-jacobson-finitary-kernel-proof.md
distinct_from:
  leavitt-el20-two-compressor-fd-representations-kill-mark: that uses two diagonal self-compressions to kill the whole diagonal group in every finite-dimensional representation; this uses the infinite simple finitary-linear kernel of a one-prefix Toeplitz quotient.
  leavitt-two-compressor-core-is-lef-and-marked-operator-mf: that shows finite-quotient invisibility does not prevent finite partial embeddings from retaining a mark; the same distinction remains open here.
  agent-free-compressor-toeplitz-cell-shift-window-is-lef: that periodizes an independent restricted wreath of finite Heisenberg cells; this includes all transverse elementary matrix units and proves only a finite-quotient obstruction.
  leavitt-first-offdiagonal-core-is-marked-non-lef: that uses a finitely presented Steinberg cover to promote exact finite-quotient collapse to a fixed LEF-table obstruction; this identifies the finitary kernel and residual quotient directly.
---

Let `J=F_2<S,T | TS=1>`, `Q=1-ST`, and

```text
E=EL_5(J),                     z_Q=x_13(Q).
```

Then every homomorphism from `E` to a finite group kills `z_Q`.  In
particular `E` is not residually finite.

More precisely, if `F` is the ideal of finite-support matrices on the
standard one-sided basis, the symbol map gives

```text
1 -> GL_fin(N x {1,...,5},F_2)
  -> E
  -> EL_5(F_2[z,z^(-1)])
  -> 1.                                                   (JFQ1)
```

The kernel is an infinite simple locally finite group and contains `z_Q`.
The Laurent elementary quotient is residually finite, but that does not make
the extension LEF by itself.

There is also no marked finite **ring** truncation: in any finite-dimensional
unital ring representation, `TS=1` makes `S` invertible and hence `ST=1`, so
`Q` vanishes.  Finite interval truncations break `TS=1`, while cyclic
truncations restore both inverse relations and kill `Q`.

This route itself is only a residual-finiteness and truncation obstruction:
finite partial group embeddings need not arise from ring representations or
from global finite quotients.  The separate finitely-presented-cover lemma
in `leavitt-first-offdiagonal-core-is-marked-non-lef` does prove that `E`
and the original packet group are non-LEF.  Neither result proves non-MF.

DERIVATION
binary-jacobson-finitary-kernel-proof
