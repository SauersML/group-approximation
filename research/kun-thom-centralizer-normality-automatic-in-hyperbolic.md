---
rg: 2
id: kun-thom-centralizer-normality-automatic-in-hyperbolic
kind: claim
title: The Kun--Thom centralizer conclusion is automatic in a hyperbolic group
invalidates:
  - nonsofic-hyperbolic-via-kun-thom-centralizer
distinct_from:
  hyperbolic-compression-centralizer-rigidity: that is the compression statement for a single compressor and its consequence for the finite-residual witness word; this one is about infranormality — the whole compression semigroup — and its consequence for the soficity obstruction of Kun--Thom Theorem B
  finite-infranormal-subgroup-is-normal: that is the general lemma that a finite infranormal subgroup is normal; this applies it, together with hyperbolic centralizer finiteness, to the centralizer rather than to the subgroup, and concludes that a published soficity obstruction has no content in the hyperbolic category
artifacts:
  - research/artifacts/hyperbolic-residual-finiteness-audit-2026-08-17.md
  - research/artifacts/kun-thom-2608-06222-verified.md
---

Kun--Thom, arXiv:2608.06222, Theorem B, verbatim:

> Let G be a sofic group with Kazhdan's property (T), and let Γ≤G be an
> infranormal subgroup with Kazhdan's property (T).  Then C_G(Γ) is normal
> in G.

Claim: if `G` is word-hyperbolic, the conclusion holds **unconditionally** —
for every infranormal `Γ ≤ G` with property (T), with no soficity hypothesis
on `G` and no elementarity hypothesis on `Γ`.

## Why this matters here

Theorem B is a soficity obstruction, and the natural way to use it is by
contraposition: exhibit a Kazhdan pair `Γ ≤ G` that is infranormal with
non-normal centralizer, and conclude `G` is not sofic.  Applied to a
hyperbolic `G` that would produce a non-sofic hyperbolic group, hence — since
residually finite groups are sofic — a non-residually-finite one, settling
both `nonsofic-hyperbolic-group` and
`non-residually-finite-hyperbolic-group` at once.

This claim says the contraposition has no hyperbolic instances to work with:
the hypothesis `C_G(Γ)` non-normal is never satisfiable there.  The 2026-08
Kun--Thom obstruction is therefore not a new lever on the hyperbolic question,
and `nonsofic-hyperbolic-via-kun-thom-centralizer` is dead.

## Scope

The statement is about the *conclusion* of Theorem B, not about its proof, and
it is not a criticism of the theorem: outside the hyperbolic category the
conclusion is exactly as informative as Kun--Thom make it, and this graph uses
it there (`kt-centralizer-normalization-hs`, `wreath-not-sofic`).  What is
special about hyperbolic ambient groups is that centralizers of the subgroups
in question are finite, and finiteness alone forces the normality.

It also says nothing about Kun--Thom Theorem A, which produces non-sofic
*wreath products* — those contain `ℤ^2` and are not hyperbolic, so Theorem A
never had a hyperbolic reading to lose.
