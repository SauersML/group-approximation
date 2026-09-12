---
rg: 2
id: relatively-hyperbolic-dehn-filling-citation
kind: route
title: Import the filling theorem from Osin and Groves--Manning
target: relatively-hyperbolic-dehn-filling
requires: []
artifacts:
  - research/artifacts/hyperbolic-residual-finiteness-audit-2026-08-17.md
---

Literature import.  The theorem is Osin, arXiv:math/0510195, Theorem 1.1, and
independently Groves--Manning, *Dehn filling in relatively hyperbolic groups*,
Israel J. Math. 168 (2008), Theorem 7.2 (for peripherals that are almost
malnormal, which is automatic in the relatively hyperbolic setting used here).

Verification performed 2026-08-17: the arXiv abstract page was read from
source, confirming author, title and that the main result is "an algebraic
counterpart of Thurston's hyperbolic Dehn surgery theorem", together with the
two supporting statements the abstract does list — that peripheral subgroups
"'almost' have the Congruence Extension Property" and that `G` "is
approximated (in an algebraic sense) by its quotients obtained by peripheral
fillings", the latter being the injectivity-on-a-finite-set clause in the
abstract's own words.

**Numbered statement verified 2026-09-11** from the arXiv PDF,
math/0510195v3 (15 Sep 2006), pp. 2--3.  Verbatim:

> Suppose that `{H_λ}_{λ∈Λ}` is a collection of subgroups of a group `G`. To
> each collection `𝔑 = {N_λ}_{λ∈Λ}`, where `N_λ` is a normal subgroup of
> `H_λ`, we associate the quotient group `G(𝔑) = G/⟨∪_{λ∈Λ} N_λ⟩^G`.

> **Theorem 1.1.** Suppose that a group `G` is hyperbolic relative to a
> collection of subgroups `{H_λ}_{λ∈Λ}`. Then there exists a finite subset `ℱ`
> of non-trivial elements of `G` with the following property. Let
> `𝔑 = {N_λ}_{λ∈Λ}` be a collection of subgroups `N_λ ◁ H_λ` such that
> `N_λ ∩ ℱ = ∅` for all `λ ∈ Λ`. Then:
> 1) For each `λ ∈ Λ`, the natural map `H_λ/N_λ → G(𝔑)` is injective.
> 2) The quotient group `G(𝔑)` is hyperbolic relative to the collection
> `{H_λ/N_λ}_{λ∈Λ}`.
> Moreover, for any finite subset `S ⊆ G`, there exists a finite subset
> `ℱ(S)` of non-trivial elements of `G` such that the restriction of the
> natural homomorphism `G → G(𝔑)` to `S` is injective whenever
> `N_λ ∩ ℱ(S) = ∅` for all `λ ∈ Λ`.

> **Corollary 1.2.** Under the assumptions of Theorem 1.1, suppose in addition
> that `G` is finitely generated and `H_λ/N_λ` is hyperbolic for each
> `λ ∈ Λ`. Then `G(𝔑)` is hyperbolic.

The claim node's finite sets `B_i` are obtained by intersecting
`ℱ ∪ ℱ(S)` with the peripherals.  Not re-derived: the proofs in the body.
The Groves--Manning theorem number above was not re-checked in this pass.
