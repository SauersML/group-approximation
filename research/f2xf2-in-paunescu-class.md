---
rg: 2
id: f2xf2-in-paunescu-class
kind: claim
title: Every p.m.p. action of F2 x F2 is sofic
distinct_from:
  f2xf2-admits-nonsofic-action: that is the negation
  paunescu-sofic-action-class-permanence: that records the families known to lie in Paunescu's class, none of which contains F2 x F2; this asks for the simplest product of two free groups
---

**OPEN.** `F_2 × F_2` lies in Păunescu's class `𝒮`: every p.m.p. action of
`F_2 × F_2` on a standard probability space is sofic (Păunescu Definition 1.4).
Equivalently, any two commuting p.m.p. actions of `F_2` on the same space combine
into a sofic action of the product.

By `product-tree-lattices-in-paunescu-class-iff-f2xf2` this is equivalent to the
same statement for any cocompact lattice in `Aut(T_p) × Aut(T_q)`, `p, q >= 3`,
and it implies soficity of all of them, including Radu's lattice
(`radu-bmw-lattice-sofic-from-f2xf2-paunescu-class`).

## Attempts

* **Amalgamation over amenable subgroups** (Păunescu Theorem 3.9). The natural
  splitting `F_2 × F_2 = (F_2 × Z) *_(F_2 × 1) (F_2 × Z)` is over a nonamenable
  subgroup. Dies at the amenability hypothesis of Theorem 3.5.
* **Treeable groups** (Alpeev Theorem 5.1). `F_2 × F_2` is not treeable: its
  second `ℓ²`-Betti number is `1`, and treeable groups have vanishing higher
  `ℓ²`-Betti numbers (Gaboriau). Dies.
* **Products of sofic actions** are sofic (Cordeiro Theorem 3.6; Alpeev
  Theorem 4.2). A general action of `F_2 × F_2` is not a product: the actions
  induced from irreducible lattices of products of trees are not. Dies at
  non-product actions.
* **Difficulty.** A proof would settle soficity of every cocompact lattice in a
  product of two regular trees, which Cornulier (arXiv:0906.3374, p. 4) records
  as unknown for the Burger--Mozes groups. Ioana (arXiv:1909.00282) shows
  `F_m × F_n` is not permutation stable, which concerns almost actions and
  decides nothing here.
* **Bounded literature check.** No statement of this question or its answer was
  found in Păunescu (2011), Alpeev (2017), Cordeiro (2016), Bowen--Burton (2021),
  or in four web searches.
