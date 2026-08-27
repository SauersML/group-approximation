---
rg: 2
id: matrix-cyclotomic-lift-obstruction
kind: claim
title: Modular one-sided inverses admit no coefficient-faithful cyclotomic matrix lift
distinct_from:
  modular-one-sided-inverse-has-no-clifford-phase-lift: that treats one scalar phase on each support term; this allows arbitrary noncommuting finite matrix coefficients and every matrix size, provided reduction remembers each modular coefficient as the identity matrix.
  hs-steinberg-root-kernel-is-linear-sofic: that asks for an approximate growing-rank decoder extracted from HS root spectra; this is an exact algebraic obstruction at every finite matrix size.
  leavitt-group-algebra-not-stably-finite: that is the open modular stable-finiteness failure; this says what an exact characteristic-zero matrix lift of such a failure cannot look like.
artifacts:
  - research/artifacts/matrix-cyclotomic-lift-and-rank-decoder-audit-2026-08-21.md
---

Let `O` be a commutative subring of `C`, let `p` be an ideal with
`O/p=F_2`, and let `G` be any group.  Suppose finite-support elements
`a,b in F_2[G]` satisfy `ab=1` and `ba!=1`.  For no `k>=1` are there matrices
`C_g,D_h in M_k(O)`, indexed by the supports of `a,b`, such that

```text
C_g = I_k mod p,         D_h = I_k mod p,
A = sum_g C_g tensor g,  B = sum_h D_h tensor h,
AB = I_k                 in M_k(C[G]).
```

Thus the cyclotomic obstruction is Morita-stable: arbitrary finite
matrix-valued Pauli carriers do not help when their reduction really
represents the coefficient `1 in F_2`.  This includes every two-primary
integral cyclotomic carrier.  Normalized Hadamard carriers evade reduction
only by inverting the prime above two, thereby forgetting the modular
coefficient rather than lifting it.
