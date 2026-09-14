---
rg: 2
id: nonhyperlinear-group-via-central-girth-twelve-local-data
kind: route
title: Central girth-twelve local data for a non-RU source give a nonhyperlinear finitely presented group
target: non-hyperlinear-group
requires:
  - some-nonru-bcs-has-central-local-data-of-girth-twelve
  - central-local-data-of-incidence-girth-twelve-keeps-the-phase
  - finite-readout-bcs-decoders-are-phase-surviving-local-colimits
  - hyperlinear-iff-group-factor-embeds-in-hyperfinite-ultrapower
---

Let `B` and `D` be as in
`some-nonru-bcs-has-central-local-data-of-girth-twelve`, and put
`Lambda = Lambda(D)`.

1. **Decoder.** By `central-local-data-of-incidence-girth-twelve-keeps-the-phase`,
   `J` has order `n` in `Lambda`. By (LC1) of
   `finite-readout-bcs-decoders-are-phase-surviving-local-colimits`, the
   readouts give a unital *-homomorphism
   `phi : A(B) -> C[Lambda] p_omega subset p_omega L(Lambda) p_omega`. Here
   `p_omega` is a nonzero central projection by Lemma 0 of that proof, and
   `Lambda` is finitely presented by (LC2).
2. **If `Lambda` were hyperlinear.** By
   `hyperlinear-iff-group-factor-embeds-in-hyperfinite-ultrapower`,
   `L(Lambda)` would embed trace-preservingly in `R^U`. The image `q` of
   `p_omega` is a projection of trace `tau(p_omega) > 0`; lift it to projections
   `q_k in M_(d_k)(C)` with `tr(q_k) -> tau(q)`. Then
   `q R^U q = prod_U q_k M_(d_k) q_k`, a tracial matrix ultraproduct with the
   renormalized trace. Composing, `A(B) -> q R^U q` is a unital *-homomorphism
   into a tracial matrix ultraproduct. So `B` would be `R^U`-satisfiable,
   contradicting the hypothesis.
3. **Conclusion.** `Lambda` is a finitely presented nonhyperlinear group.

Step 2 uses only the standard facts that projections in an ultraproduct of
matrix algebras lift to projections of the factors with converging traces, and
that the corner of an ultraproduct is the ultraproduct of the corners.
