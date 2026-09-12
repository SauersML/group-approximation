---
rg: 2
id: stw99-lxxvi-rr0-simple-pure-field-cu-regularity-proof
kind: route
title: Spectral endpoint bundles and finite hereditary sandwiches give full first-factor Cu surjectivity
target: stw99-lxxvi-rr0-simple-pure-field-cu-regularity
requires:
  - stw99-lxxvi-rr0-relative-strict-positive-embedding
  - stw99-lxxvi-compact-equality-strata-determine-comparison
  - stw99-lxxvi-all-base-compact-rigidity-k-stability
  - stw99-lxxvi-rr0-all-base-full-order-reflection
  - stw99-lxxvi-cu-regularity-passes-to-inductive-limits
  - stw99-lxxvi-cu-regularity-passes-to-ideals-and-quotients
artifacts:
  - research/artifacts/stw99-lxxvi-rr0-field-cu-regularity-2026-09-05.md
---

Given a target positive b and epsilon>0, use an intermediate spectral
cutoff. Its compact fibers have support bundles on neighborhoods
which dominate (b-epsilon)_+ and lie below b, and agree with both
endpoint bundles wherever the endpoint class is equal. Noncompact
fibers admit bounded soft coefficient labels between the cutoffs.

Finite coefficient Riesz interpolation assigns monotone values to
antichains of a finite cover. Choosing every new value soft retains
the original compact bundle labels. Truncating barycentric coordinates
produces closed patch supports whose overlapping labels are comparable.
Descending exact relative embeddings arrange their ranges inside the
largest active hereditary module. Their weighted sum is a source
positive a. The verified endpoint bundle data and the global comparison
criterion give [(b-epsilon)_+]<=phi[a]<=[b].

Applying this sandwich to successive target cutoffs, and using order
reflection, gives an increasing source sequence whose image has
supremum [b]. This proves surjectivity on finite-dimensional compact
bases. Continuity of the actual maps through coordinate approximations
gives arbitrary compact metric bases, and ideal permanence gives the
locally compact conclusion.
