---
rg: 2
id: zaremsky-2-11-braided-v-inner-amenable
kind: claim
title: "Zaremsky Problem 2.11 resolved: is braided V inner amenable?"
root: true
distinct_from:
  braided-v-is-not-inner-amenable: that claim is the negative answer, a theorem about Brin's braided V; this one is the question itself, established only through an answer route
  thompson-t-and-v-are-not-inner-amenable: that is the Haagerup–Olesen theorem about T and V; this is the question for braided V, which surjects onto V with a non-amenable pure braided kernel
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 2, Problem 11, verbatim:
"Is braided V inner amenable? (Probably not.)"

This claim is the question. It is established only through an answer route:
- **No**: `zaremsky-2-11-by-no` requires `braided-v-is-not-inner-amenable`.
- **Yes**: `zaremsky-2-11-by-yes` would require a claim that braided V is inner amenable.

Never write a `requires: []` route into this claim.

**Reading.** "Braided V" is Brin's group bV (arXiv:math/0406042), also written V_br
(Bux–Fluch–Marschler–Witzel–Zaremsky, arXiv:1210.2931). Its elements are classes of triples
`(T_-, β, T_+)`: two binary trees and a braid, where an expansion cables a strand. A discrete
group G is inner amenable (Effros) if some finitely additive probability measure on `G ∖ {e}`
is invariant under conjugation.

**Known context.**
- F is inner amenable (Jolissaint). T and V are not (Haagerup–Olesen, arXiv:1609.05086v1,
  Theorem 3.4). The Higman–Thompson groups T_n and V_n are not (Bashwinger–Zaremsky,
  arXiv:2203.13798).
- `L(bV)` and `L(bF)` are II_1 factors, and the pure braided Thompson group bF is inner amenable
  (Bashwinger–Zaremsky, arXiv:2104.04826, abstract).
- The result for V does not pass to bV by itself. The kernel of `bV → V` is a directed union of
  pure braid groups, and a conjugation-invariant mean could live on that kernel.

## Attempts

- 2026-09-13 (lane z2-11-bv-inner-amen): negative answer proved in
  `braided-v-is-not-inner-amenable`, UNREVIEWED; the artifact is
  `research/artifacts/zp-braided-v-not-inner-amenable-2026-09-13.md`.
  - Method: apply the Haagerup–Olesen centralizer criterion to a free subgroup lifted from their
    copy Λ of PSL(2,Z) in T. Nontrivial kernel elements carry finite dyadic breakpoint sets,
    which centralizing elements of Λ must permute.
  - The route `zaremsky-2-11-by-no` lands after a verifier PASS.
  - A bounded arXiv search on 2026-09-13 found no earlier answer. Bashwinger–Zaremsky
    (2104.04826, 2203.13798) and Bashwinger–DeBonis (2507.18821) do not treat inner amenability
    of bV.
