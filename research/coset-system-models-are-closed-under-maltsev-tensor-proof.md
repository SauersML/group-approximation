---
rg: 2
id: coset-system-models-are-closed-under-maltsev-tensor-proof
kind: route
title: The Mal'tsev product of three coset points stays in the coset, and Hilbert-Schmidt orthogonality of product atoms adds defects
target: coset-system-models-are-closed-under-maltsev-tensor
requires: []
---

Write `X = p_q^s p_(q')^(s')`, `Y = p'_q^t p'_(q')^(t')` and
`Z = p''_q^u p''_(q')^(u')`.

**PVM.**  The atoms `p^s (x) (p'^t)^op (x) p''^u` are orthogonal projections
summing to `1`, and each lies in exactly one `P^r`.

**Coset closure.**  In `M'^op`, `(p'^t)^op (p'^(t'))^op = (p'^(t') p'^t)^op`,
which is the adjoint of `Y`.  So

```text
P_q^r P_(q')^(r') = sum X (x) (Y^*)^op (x) Z,
```

over `s t^(-1) u = r` and `s' t'^(-1) u' = r'`.  For elements of `cD`,

```text
(c d_1)(c d_2)^(-1)(c d_3) = c d_1 d_2^(-1) d_3 in cD.
```

So if `(s,s')`, `(t,t')`, `(u,u')` all lie in `cD`, then `(r,r')` does.
Hence for `(r,r') notin cD` every surviving term has at least one factor
indexed off `cD`.

**Atoms are HS-orthogonal.**  `X_(s s')^* X_(σ σ') = p^(s') p^s p^σ p^(σ')`.
- By orthogonality within the PVM this vanishes unless `σ = s`.
- By cyclicity, `τ(p^(s') p^s p^(σ')) = τ(p^(σ') p^(s') p^s)`, which vanishes
  unless `σ' = s'`.

So distinct index tuples give orthogonal terms, and

```text
sum_((r,r') notin cD) ||P^r P^(r')||_2^2
  <= sum_(tuples with some pair notin cD) ||X||^2 ||Y||^2 ||Z||^2 .
```

**Additivity.**  Split according to which pair lies off `cD`, and bound the
other two sums by their totals.  For instance

```text
sum_(all t,t') ||Y||_2^2 = sum τ'(p'^(t') p'^t p'^(t')) = sum τ'(p'^t p'^(t')) = τ'(1) = 1 .
```

This gives `δ(P) <= δ(p) + δ(p') + δ(p'')`, edge by edge.

**Unary sectors.**  `P^(π σ^(-1) ρ) >= p^π (x) (p'^σ)^op (x) p''^ρ`, so its
trace is at least `(1-ε)(1-ε')(1-ε'') >= 1-ε-ε'-ε''`.

**Classes.**
- Tensor products of finite-dimensional algebras are finite-dimensional.
- The opposite of an `R^U`-embeddable algebra is `R^U`-embeddable, through
  the transpose on `R` and ultrapowers.  Tensor products embed through
  `R^U (x̄) R^U ⊂ (R (x̄) R)^U ≅ R^U`.
- Product traces are traces.
