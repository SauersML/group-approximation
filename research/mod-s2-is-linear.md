---
rg: 2
id: mod-s2-is-linear
kind: claim
title: The genus-two mapping class group has a faithful finite-dimensional complex representation
distinct_from:
  mod-s2-jones-torelli-closure-is-su5: that computes the closure of the Torelli image under one Jones representation, which is not faithful; this is faithfulness of the Bigelow-Budney representation, used only as the linearity hypothesis of a general theorem.
  genus-two-mapping-class-group-homology-and-symplectic-quotient: that records the presentation, low-degree homology and the symplectic quotient, whose kernel (Torelli) is infinite; this is a faithful linear embedding of the whole group.
---

**ESTABLISHED** (route `mod-s2-is-linear-citation`).

`M = Mod(S_2)`, the mapping class group of the closed oriented genus-two surface, has a faithful homomorphism
`M -> GL_64(C)`. So `M` is a finitely generated linear group over the field `C`. Finite generation is item 1 of
`genus-two-mapping-class-group-homology-and-symplectic-quotient`, which gives a finite presentation.

**Use.** This is the linearity hypothesis of `weak-matricial-stability-kills-centralizer-even-cohomology`, taken with
`K = C`, in route `mod-s2-instability-via-bielliptic-delocalized-dadarlat`.
