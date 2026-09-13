---
rg: 2
id: simple-lef-rings-are-exactly-matricial
kind: claim
title: A simple ring that is locally embeddable into finite rings embeds in a matrix ultraproduct over finite fields
distinct_from:
  simple-rings-with-local-matrix-models-are-matricial: that assumes exact local models into matrix algebras over one field; this assumes only exact local models into finite rings and lands over varying finite fields
  exactly-matricial-rings-are-lef-rings: that is the converse direction, exact matriciality giving LEF
  lef-simple-rings-are-not-finitely-presented: that shows finitely presented simple LEF rings are finite; this embeds every simple LEF ring in a matrix ultraproduct over finite fields
artifacts:
  - research/artifacts/un-lef-converse-2026-09-13-part1.md
---

**ESTABLISHED (unreviewed; proof route `simple-lef-rings-are-exactly-matricial-proof`, artifact §2).**

Let `R` be a countable simple unital ring that is LEF in the sense of `lef-simple-rings-are-not-finitely-presented`. Then
for every non-principal ultrafilter `omega` there is an injective unital ring homomorphism
`R -> prod_omega M_(d_n)(F_(q_n))` over finite fields.

With `exactly-matricial-rings-are-lef-rings`, a simple ring is LEF iff it is exactly matricial, and in that case
it is exactly matricial over finite fields.

**Model test.** `R = F_2 × F_2` is LEF and not simple. Projecting to one factor is unital but not injective,
so simplicity is needed.

**Review (un-verify-3, 2026-09-13): PASS.** Re-derived: the semisimple quotient of a finite ring is a product of `M_d(F_q)`, unital projection onto one factor, the ultraproduct homomorphism, and injectivity by simplicity. `research/artifacts/un-review3-2026-09-13-part3.md` §4.

**Hypothesis note (review).** Countability is used for the exhausting windows `W_n` and the ultrafilter on N. For uncountable `R` the same argument works with an ultrafilter on the directed set of finite windows.

**Review (un-verify-measure, 2026-09-13): PASS, with a hypothesis fix.** Artin–Wedderburn projection and injectivity by simplicity re-derived; "countable" added to match the proof. See `research/artifacts/un-review-measure-2026-09-13-part4.md` §F2.
