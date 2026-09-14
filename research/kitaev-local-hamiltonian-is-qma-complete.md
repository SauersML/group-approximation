---
rg: 2
id: kitaev-local-hamiltonian-is-qma-complete
kind: claim
title: Constant-locality local Hamiltonian is QMA-complete at an inverse-polynomial promise gap
artifacts:
  - research/artifacts/qpcp-positive-shift-audit-2026-09-11.md
distinct_from:
  quantum-pcp-constant-gap-local-hamiltonian: that asks for QMA-hardness at a constant relative promise gap; this is the classical completeness theorem at an inverse-polynomial gap, the starting point of every amplification attack.
---

**ESTABLISHED BY CITATION.** There are a constant `k` (`k=2` suffices) and a
polynomial `p` such that, for `k`-local Hamiltonians on `n` qubits in the
normalized form (QPCP1) of `quantum-pcp-constant-gap-local-hamiltonian`,

```text
H = (1/m) sum_(a=1)^m h_a,   0 <= h_a <= I,   m = poly(n),  poly(n)-bit entries,
```

deciding `lambda_min(H) <= a` versus `lambda_min(H) >= b` with
`b - a >= 1/p(n)` is QMA-complete.

Kitaev proved the 5-local case [Kitaev--Shen--Vyalyi 2002]. Kempe--Kitaev--Regev,
*The complexity of the local Hamiltonian problem*, arXiv:quant-ph/0406180
(SIAM J. Comput. 35(5), 2006), Theorem 1, proves the 2-local case. Their
Definition 3 is unnormalized: `H=sum_(j=1)^r H_j`, `||H_j||<=poly(n)`,
thresholds a constant apart.

The normalization to (QPCP1) is affine. With `M=max_j||H_j||` and
`h_j=(H_j+M I)/(2M)`, the gap becomes `(b-a)/(2Mr)>=1/p(n)`, and locality and
qubit dimension are unchanged. Section 5 of the linked artifact records the
source reading and this computation.
