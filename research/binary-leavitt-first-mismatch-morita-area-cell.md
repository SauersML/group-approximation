---
rg: 2
id: binary-leavitt-first-mismatch-morita-area-cell
kind: claim
title: Pay every contextual Morita first mismatch by one bounded Steinberg cell
distinct_from:
  atlas-steinberg-context-absorption: that proves exact vanishing of root elements in arbitrary two-sided ring-relation contexts; this asks for a uniform area comparison from the original cross-branch commutator word to that nested context word.
  binary-leavitt-canonical-morita-tree-reduction: that proves this one estimate yields the full bounded-area complete-graph compiler; this is the remaining quantitative estimate itself.
  bounded-centralizer-fillings-force-finite-stabilizer: that forbids uniformly filling an infinite stabilizer against one fixed finite-order word; the signs here remain the vertex-dependent conjugate words `D_uzD_u^(-1)`, and no bounded filling of `[D_u,z]` is asserted.
artifacts:
  - research/binary-leavitt-bounded-area-chromatic-code.md
---

**OPEN.**  In the fixed finite presentation of the stabilized
binary-Leavitt Steinberg group, use the fixed branch words `D_0,D_1` and the
canonical tail words of `(MTR2)`.  Prove that one constant `A_times` satisfies

```text
Area([D_iD_acD_a^(-1)D_i^(-1),
      D_jD_bhD_b^(-1)D_j^(-1)])<=A_times                 (FMA1)
```

for all binary tails `a,b` and both unequal pairs `i!=j`.

## Exact reduction already available

By `(SMI2)`, the coefficient of `(FMA1)` is

```text
r_a t_i s_j s_b=r_a (t_i s_j) s_b=0.                    (FMA2)
```

The middle factor is one of the two context-free Leavitt zero relations.
Moreover `atlas-steinberg-context-absorption` writes the corresponding root
word as a fixed-depth double commutator

```text
x_(kl)(r_a (t_i s_j) s_b)
 =[x(r_a),[x(t_i s_j),x(s_b)]].                          (FMA3)
```

If the middle root relation has area `A_zero`, the displayed nested word has
area at most `4A_zero`, independently of both tails: a commutator with an
arbitrary word doubles relator area, and the nesting depth is two.

## Remaining comparison

What is not yet proved is a uniform-area conversion of the **original** word
in `(FMA1)` to the nested word `(FMA3)`.  Exact Steinberg calculus identifies
them.  The existing finite-presentation completeness proof obtains that
identification through spare-index and split-independence transfers, but its
induction is qualitative and records no depth-independent area bound.

The decisive positive proof must give a fixed-size Hall--Witt/spare-index
diagram in which the arbitrary tail root words occur only as conjugating
contexts.  Iterating the transfer identity once per tail letter gives area
depending on `|a|+|b|` and is insufficient.  Conversely, a negative result
must lower-bound the area of these particular first-mismatch words; the
general infinite-stabilizer theorem does not apply because `(FMA1)` compares
two moving branch words and never fills a centralizer of the fixed mark.

Establishing `(FMA1)` closes the property-`(T)`-free proof through
`binary-leavitt-canonical-morita-tree-reduction` and
`infinite-chromatic-commutator-code-kills-mf-mark`.

## Attempts

* **Qualitative context absorption.**  The double nesting `(FMA3)` does give
  a constant-area null word, but the published Cairn proof only identifies
  it abstractly with the original Steinberg product.  Replaying
  `atlas-steinberg-transfer-identity` along the canonical monomial compiler
  consumes one shorter commutation diagram per split and therefore gives an
  area bound growing with the tails.  The next attack is a single four-spare
  Hall--Witt diagram treating each entire tail root word as one variable; its
  auxiliary disjoint-root commutators must themselves occur only as
  conjugates of fixed relators, or the same growth returns.
