---
rg: 2
id: thompson-f-qi-to-f-times-z-resolved
kind: claim
title: "Bridson's question resolved: decide whether Thompson's group F is quasi-isometric to F x Z"
---

Part (a) of `zaremsky-2-04-f-quasi-isometric-to-f-times-z`. Decide whether
Thompson's group F, with a word metric, is quasi-isometric to F × Z with the
product word metric.

This claim is the question. It is established only by a yes-route (requiring an
established claim that F and F × Z are quasi-isometric) or a no-route (requiring
an established claim that they are not). Never write a `requires: []` route into
it. A yes-answer also answers part (d) yes, and a no-answer to part (d) answers
this part no.

## Attempts

- **Coarse-embedding-monotone invariants.** F × Z embeds in F as a subgroup
  (elements supported in `[0,1/2]` times a cyclic group supported in `[1/2,1]`)
  and F embeds in F × Z, so the two groups coarsely embed in each other
  (established: `thompson-f-f-times-z-f-times-f-are-mutual-subgroups`). Every
  invariant that is monotone under coarse embeddings (asymptotic dimension,
  property A, coarse embeddability in Hilbert space) takes the same value on
  both; the same holds for invariants monotone under regular maps, such as the
  separation profile of Benjamini–Schramm–Timár and the Poincaré profiles of
  Hume–Mackay–Tessera, since subgroup inclusions are regular maps. Dies: no
  separation is possible this way.
- **Amenability, growth, ends, finiteness.** F × Z is amenable iff F is; both have
  exponential growth, one end, and type F_∞; both have quadratic Dehn function
  (Guba for F, and F × Z by the product structure). Dies: none of these separates.
- **Cohomology with group-ring coefficients.** `H^*(G; ZG)` is the classical coarse
  invariant of groups of finite type (quasi-isometry invariance: Gersten; not yet
  imported). It vanishes identically on F (Brown–Geoghegan 1984, Theorem 7.2:
  `thompson-f-has-vanishing-zg-cohomology`) and on `F × Z`
  (`thompson-products-have-vanishing-zg-cohomology`). Dies.
- **Open lines.** (i) A coarse invariant sensitive to a central Z factor that
  survives passage to a quasi-isometry (for instance coarse fibrations over Z with
  uniformly coarsely equivalent fibres). (ii) An explicit quasi-isometry built from
  the self-similarity of F: `F ≅ F_[0,1/2]` and the ascending HNN structure of F
  over a copy of itself.
