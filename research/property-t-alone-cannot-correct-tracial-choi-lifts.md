---
rg: 2
id: property-t-alone-cannot-correct-tracial-choi-lifts
kind: claim
title: Property T alone cannot correct tracial generator lifts to ucp coordinate lifts
distinct_from:
  property-t-cstar-amenable-trace-forces-fd-quotient: Brown's theorem repairs already-ucp asymptotically multiplicative maps to finite-dimensional homomorphisms; this says property T cannot manufacture the missing ucp maps from arbitrary coordinate representatives.
  maslov-sector-tracial-generator-ucp-liftability: that asks for the lifting statement for one arithmetic twisted fibre; this no-go says no proof may use property T alone, because the general assertion has hyperlinear Kazhdan counterexamples.
---

There is no theorem based only on property (T) with the following conclusion:
every star-homomorphism from the full group C-star algebra of a property-(T)
group into a tracial matrix ultraproduct has ucp coordinate representatives
on a fixed finite generating operator system.

Indeed, such representatives are asymptotically in the multiplicative domain
on the canonical unitaries.  Telescoping over words would make the induced
trace amenable, i.e. give Kirchberg's factorization property.  Applying the
putative theorem to the hyperlinear Kazhdan group in
`thom-hyperlinear-kazhdan-without-factorization` contradicts Thom's failure
of factorization.

Thus a proof of `maslov-sector-tracial-generator-ucp-liftability` must use
specific arithmetic/Maslov information.  Kazhdan projection or spectral-gap
arguments enter only after complete positivity has been obtained; they
cannot provide a dimension-uniform correction of negative Choi directions.

The proof is `property-t-alone-no-choi-correction-proof`.
