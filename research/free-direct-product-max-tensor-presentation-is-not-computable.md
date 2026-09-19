---
rg: 2
id: free-direct-product-max-tensor-presentation-is-not-computable
kind: claim
title: The standard maximal-tensor presentation of the direct product of two nonabelian free groups is not computable
distinct_from:
  leavitt-llp-permanence-fence: That uses F_2 times F_2 as an open LLP lower bound for the Leavitt group; this proves a separate effectivity obstruction without deciding LP or LLP.
  llp-implies-weak-ucp-stability: That is a noneffective existence implication from LLP; this shows that a ucp lift for the standard free-direct-product quotient cannot be computable even if it exists.
  hyperlinear-computable-hs-dehn-modulus-solvable-word-problem: That converts a computable normalized-HS Dehn modulus into a group word-problem algorithm; this concerns computability of full C-star operator norms and ucp lifts.
artifacts:
  - research/artifacts/goldbring-sinclair-tensor-definability-audit-2026-08-23.md
---

**ESTABLISHED (Goldbring--Sinclair, arXiv:2509.15086v1).**  For every
`n in {2,3,...,infinity}`, the standard presentation of

```text
C^*(F_n x F_n) = C^*(F_n) tensor_max C^*(F_n)
```

is not computable.  More generally, for a qc-full C-star algebra `C`, there
cannot be computable presentations of both `C` and `C tensor_max C` for
which the two canonical factor embeddings are computable.

Consequently, for any fixed quotient

```text
C^*(F_infinity) -> C^*(F_n x F_n),
```

there is no computable ucp lift in the standard presentations.  This does
not decide whether an abstract ucp lift exists: LP of `C^*(F_n x F_n)`
remains open in the cited source.  It does prove that an LLP/LP-based Kleene
compiler cannot take such a lift as a uniform effective black box.
