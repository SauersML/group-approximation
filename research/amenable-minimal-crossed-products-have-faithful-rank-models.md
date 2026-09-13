---
rg: 2
id: amenable-minimal-crossed-products-have-faithful-rank-models
kind: claim
title: Crossed products of minimal Cantor actions of amenable groups embed in rank ultraproducts over any field
distinct_from:
  free-minimal-crossed-products-are-simple-with-rank-models: that is the Z^d box case with freeness, simplicity and centres over a finite field; this is every countable amenable group over every field, using only minimality for faithfulness.
  cantor-z-crossed-product-embeds-in-continuous-factor: that is the published Z case with the continuous factor and uniqueness of the rank function; this is a crude Følner model for amenable groups with no uniqueness.
artifacts:
  - research/artifacts/un-sofic-not-lef-2026-09-13-part1.md
---

**ESTABLISHED (unreviewed).** Let `Γ` be a countable amenable group acting minimally on an infinite compact totally
disconnected metrizable space `X`, and `k` a field. Then `R = LC(X, k) ⋊ Γ` has an injective unital ring homomorphism into
a rank ultraproduct `∏_ω M_(N_n)(k) / {rank-null}`. Hence `R` carries a faithful Sylvester matrix rank function and is
stably finite.

The models truncate the orbit representation to Følner sets. Minimality gives syndetic visits to a clopen set, which bounds
the rank of every nonzero element below by a fixed fraction. Freeness is not used.

Route: `amenable-minimal-crossed-products-faithful-rank-models-proof`.

**Review (un-verify-3, 2026-09-13): PASS.** Re-derived: the truncation defect has rank `o(|F_n|)`, and faithfulness follows from syndetic visits and a `K`-separated set of columns with disjoint supports `Kh`. Freeness is not needed. `research/artifacts/un-review3-2026-09-13-part3.md` §6.
