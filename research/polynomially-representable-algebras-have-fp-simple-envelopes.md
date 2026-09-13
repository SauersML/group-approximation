---
rg: 2
id: polynomially-representable-algebras-have-fp-simple-envelopes
kind: claim
title: Every subalgebra of a matrix algebra over a tensor product of a free algebra and a polynomial algebra embeds in a finitely presented simple algebra
distinct_from:
  algebra-boone-higman-conjecture: that asks for finitely presented simple envelopes of every decidable algebra; this proves the statement for one explicit low-complexity class.
  no-fp-simple-algebra-hosts-every-decidable-algebra: that forbids one host class sharing a recursive time bound from covering every decidable algebra; the hosts here, M_n(L_2^{⊗(k+1)}), do share such a bound, consistently with that fence.
---

**ESTABLISHED** through `polynomially-representable-envelopes-via-leavitt-tensors`.

Let `K` be a field and `L_2 = L(1,2)` the Leavitt algebra. For `m, k, n >= 1` let

```text
P_{m,k,n} = M_n( K<x_1..x_m> ⊗_K K[t_1..t_k] ).
```

**Claim.**

1. `M_n(L_2^{⊗(k+1)})` is a finitely presented simple `K`-algebra.
2. `P_{m,k,n}` embeds in `M_n(L_2^{⊗(k+1)})`.
3. Hence every subalgebra of `P_{m,k,n}` embeds in a finitely presented simple
   algebra.

**Covered inputs** include all finitely generated algebras with a faithful
representation in `M_n(K[t_1..t_k])`, among them the algebras of generic
matrices and all f.g. subalgebras of matrix algebras over polynomial rings. Free
algebras and their tensor products with polynomial algebras are covered too.

**Scope.** Every covered input has word problem decidable in time exponential in
the word length, one uniform recursive bound across the class. So this class
does not clear the complexity benchmark of
`no-fp-simple-algebra-hosts-every-decidable-algebra`. Monomial inputs
`K<x,y>/(x y^n x : n in X)` with hard decidable `X` are not covered.

No novelty is claimed. The ingredients are standard: simplicity of Leavitt
algebras, and simplicity of `A ⊗ B` for `A` simple and `B` central simple. The
proof route is self-contained.
