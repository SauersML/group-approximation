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

is hyperbolic relative to the images `{P_i / N_i}`, each natural map
`P_i / N_i -> G_bar` is injective, and the quotient map is injective on `F`.

This is the algebraic counterpart of Thurston's hyperbolic Dehn surgery
theorem: Osin, *Peripheral fillings of relatively hyperbolic groups*,
arXiv:math/0510195, Theorem 1.1, published in Inventiones mathematicae (2007),
DOI `10.1007/s00222-006-0012-3`, with the independent version of
Groves--Manning, *Dehn filling in relatively hyperbolic groups*, Israel J.
Math. 168 (2008).  (An earlier version of this node gave the venue as IMRN;
the DOI prefix `s00222` is Inventiones.)

Two standard companions are used with it and are not separated out: a group
hyperbolic relative to **finite** subgroups is word-hyperbolic, and relative
hyperbolicity of `G_bar` with respect to the filled peripherals is exactly
what makes the previous sentence applicable when every `N_i` has finite index.
The first companion is Osin's Corollary 1.2 in the same paper: under the
assumptions of Theorem 1.1, if `G` is finitely generated and every
`P_i / N_i` is hyperbolic, then `G_bar` is hyperbolic.

## Trust surface

Imported, not proved here.  On 2026-09-11 Theorem 1.1 and Corollary 1.2 were
read verbatim from the arXiv PDF (math/0510195v3, pp. 2--3); the quotation is
in `relatively-hyperbolic-dehn-filling-citation`.  Osin's form produces one
finite set `F` of nontrivial elements controlling relative hyperbolicity and
injectivity of `P_i/N_i`, and for each finite `S subset G` a finite set `F(S)`
controlling injectivity on `S`; the sets `B_i` above are
`(F union F(S)) intersect P_i` with `S` the given finite set.  The proofs in the
body were not re-derived.  Anything downstream of this node inherits that
dependency, which is why it is a node rather than a sentence inside a route.
