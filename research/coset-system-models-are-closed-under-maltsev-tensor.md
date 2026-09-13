---
rg: 2
id: coset-system-models-are-closed-under-maltsev-tensor
kind: claim
title: Models of a coset system over any finite groups are closed under a ternary Mal'tsev tensor product, with additive Hilbert-Schmidt defects
distinct_from:
  central-character-profiles-affine-under-odd-tensor-products: that tensors three group representations in a fixed central sector and gets affine Boolean profiles; this tensors three PVM models of a coset system over arbitrary finite groups through the nonabelian product s t^(-1) u, with additive defects.
  torsor-cfi-port-profiles-are-cosets: that proves exact scalar port profiles are cosets through composition of quantum isomorphisms; this is an operator-level ternary operation on models, including approximate finite-dimensional models.
---

**ESTABLISHED** by `coset-system-models-are-closed-under-maltsev-tensor-proof`.
It has not been reviewed by an ex-verify lane.

**Setting.**  `S` is a coset system: PVMs `(p_q^s)_(s in K_q)`, with
orthogonality `p_q^s p_(q')^(s') = 0` off `c_(qq') D_(qq')`
(`coset-systems-are-torsor-isomorphism-games`).  A *model* is a family of
PVMs in a tracial von Neumann algebra `(M, τ)`.  Its defect is

```text
δ(p) = sum_((q,q') in E) sum_((s,s') notin cD) ||p_q^s p_(q')^(s')||_2^2 .
```

Exact models have `δ = 0`.

**Theorem.**  Let `p, p', p''` be models in `(M,τ)`, `(M',τ')`, `(M'',τ'')`.
In `M (x̄) M'^op (x̄) M''` define

```text
P_q^r = sum_(s t^(-1) u = r) p_q^s (x) (p'_q^t)^op (x) p''_q^u .
```

1. `P` is a model of `S`, and `δ(P) <= δ(p) + δ(p') + δ(p'')`.
2. Unary sectors multiply.  If `τ(p_q^π) >= 1-ε`, `τ'(p'_q^σ) >= 1-ε'` and
   `τ''(p''_q^ρ) >= 1-ε''`, then `τ(P_q^(π σ^(-1) ρ)) >= 1-ε-ε'-ε''`.
3. Each class is preserved: finite-dimensional models,
   `R^U`-embeddable models, and tracial models.

**Consequences.**
- **Exact models.**  If three port sectors `π, σ, ρ` of a coset-system gadget
  have exact models at level `t in {q, qa, qc}`, then so does `π σ^(-1) ρ`.
  Boolean ports read through involutions give affine sectors.
- **Approximate models.**  Suppose a gadget has finite-dimensional models of
  defect `<= ε` on three sectors.  Then it has one of defect `<= 3ε` on their
  Mal'tsev product, and the dimensions multiply.  So no decoder with
  dimension-independent soundness can reject the Mal'tsev sector while
  accepting the other three.
- This covers every compiler that realizes predicates through coset-system
  gadgets complete sector by sector, robustly or exactly, over any finite
  groups.  Compilers whose ports are coupled to the rest of the instance are
  not covered.
