---
rg: 2
id: relatively-hyperbolic-dehn-filling
kind: claim
title: Group-theoretic Dehn filling for relatively hyperbolic groups
artifacts:
  - research/artifacts/hyperbolic-residual-finiteness-audit-2026-08-17.md
---

Let `G` be hyperbolic relative to a finite collection of finitely generated
peripheral subgroups `{P_1, …, P_m}`.  For every finite subset
`F ⊂ G ∖ {1}` there are finite subsets `B_i ⊂ P_i ∖ {1}` such that: for any
choice of normal subgroups `N_i ⊴ P_i` with `N_i ∩ B_i = ∅`, the quotient

```text
G_bar = G / <<N_1 ∪ … ∪ N_m>>
```

is hyperbolic relative to the images `{P_i / N_i}`, and the quotient map is
injective on `F`.

This is the algebraic counterpart of Thurston's hyperbolic Dehn surgery
theorem: Osin, *Peripheral fillings of relatively hyperbolic groups*,
arXiv:math/0510195, Theorem 1.1 (IMRN 2007), with the independent version of
Groves--Manning, *Dehn filling in relatively hyperbolic groups*, Israel J.
Math. 168 (2008).

Two standard companions are used with it and are not separated out: a group
hyperbolic relative to **finite** subgroups is word-hyperbolic, and relative
hyperbolicity of `G_bar` with respect to the filled peripherals is exactly
what makes the previous sentence applicable when every `N_i` has finite index.

## Trust surface

Imported, not proved here.  The abstract of arXiv:math/0510195 was read from
source on 2026-08-17 and confirms the paper and its subject ("The main result
of the paper is an algebraic counterpart of Thurston's hyperbolic Dehn surgery
theorem"), but the abstract does not carry the finite-set-and-injectivity
clause, and the body was **not** re-read.  The statement above is the
published Theorem 1.1 in the form in which the literature universally quotes
it.  Anything downstream of this node inherits that dependency, which is why
it is a node rather than a sentence inside a route.
