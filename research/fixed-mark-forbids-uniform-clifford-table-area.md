---
rg: 2
id: fixed-mark-forbids-uniform-clifford-table-area
kind: claim
title: A fixed nontrivial finite mark forbids uniformly bounded Clifford multiplication-table area
distinct_from:
  bounded-centralizer-fillings-force-finite-stabilizer: that proves uniform commutator area is impossible along an infinite centralizer; this converts a bounded multiplication table into exactly such a forbidden commutator family and proves that the proposed Clifford-tape target cannot exist.
  uniform-bounded-area-clifford-tables-force-mark-collapse: that derives analytic collapse from the hypothetical table; this shows that its hypothesis is already algebraically impossible in a finitely presented group.
---

**ESTABLISHED.**  Let `Gamma=<S|R>` be finitely presented.  There do not
exist a nonidentity word `j`, maps

```text
sigma_N:E_N -> F(S),              N=1,2,...,
```

from the extraspecial Pauli groups, and one finite constant `A` such that

```text
sigma_N(J)=j,
Area_R(sigma_N(g)sigma_N(h)sigma_N(gh)^(-1))<=A          (UCT1)
```

for every `N` and every `g,h in E_N`.

Indeed `(UCT1)` makes the group elements represented by `sigma_N` an exact
homomorphism `E_N -> Gamma`.  Since the central involution `J` has the fixed
nontrivial image represented by `j`, this homomorphism is injective.  Thus
the union of the images supplies arbitrarily many distinct cosets modulo
`<j>` inside `C_Gamma(j)`.

For any `g in E_N`, apply `(UCT1)` to `(J,g)` and `(g,J)`.  Since `Jg=gJ`
and the same word `sigma_N(Jg)` occurs in both discrepancies, concatenating
the first discrepancy with the inverse of the second gives

```text
Area_R([j,sigma_N(g)])<=2A.                               (UCT2)
```

This is a uniformly bounded commutator filling for an unbounded family of
cosets in the centralizer of the nontrivial order-two element represented by
`j`.  It contradicts
`finite-mark-centralizer-commutator-area-is-proper`, equivalently
`bounded-centralizer-fillings-force-finite-stabilizer`.

The obstruction is purely algebraic and presentation-independent.  No
choice of canonical addresses, self-similar actor, or longer representative
words can make a fixed-mark full Clifford table have uniform filling area.
