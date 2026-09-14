---
rg: 2
id: hyperbolic-relative-to-maximal-elementary-citation
kind: route
title: Import Osin's elementary-subgroup embedding theorem for ordinary hyperbolic groups
target: hyperbolic-group-relative-to-maximal-elementary-subgroup
requires: []
---

Literature import.  D. V. Osin, *Elementary subgroups of relatively hyperbolic
groups and bounded generation*, arXiv:math/0404118v1 (6 April 2004),
published in Internat. J. Algebra Comput. 16 (2006), DOI
`10.1142/S0218196706002901`.

Read from the arXiv PDF, pages 1--4, on 2026-09-11.  Verbatim:

> **Definition 1.2.** A group `G` is hyperbolic relative to a collection of
> subgroups `{H_λ, λ ∈ Λ}` if `G` is finitely presented relative to
> `{H_λ, λ ∈ Λ}` and the corresponding relative Dehn function is linear. In
> particular, a group is hyperbolic (in the ordinary non-relative sense) if
> and only if it is hyperbolic relative to the trivial subgroup.

> **Definition 1.4.** Let `G` be a group hyperbolic relative to a collection
> of subgroups `{H_λ, λ ∈ Λ}`. A subgroup `Q ≤ G` is said to be
> hyperbolically embedded into `G`, if `G` is hyperbolic relative to
> `{H_λ, λ ∈ Λ} ∪ {Q}`.

> We also say that an element `g ∈ G` is parabolic if it is conjugate to an
> element of `H_λ` for some `λ ∈ Λ`. Otherwise `g` is said to be hyperbolic.
> In Section 3 we notify that any hyperbolic element `g ∈ G` of infinite order
> is contained in a unique maximal elementary subgroup of `G`, which is denoted
> by `E(g)`.

> **Corollary 1.7.** For any hyperbolic element `g ∈ G` of infinite order,
> `E(g)` is hyperbolically embedded into `G`.

Specialization used by the claim.  Take the collection to be the trivial
subgroup alone, which Definition 1.2 permits for an ordinary word-hyperbolic
group.  The only parabolic element is then the identity, so every element of
infinite order is hyperbolic, and Corollary 1.7 gives relative hyperbolicity
with respect to `{ {1}, E(g) }`.

Not re-read: the Section 3 proofs.  The statement is imported at the level of
the numbered corollary, which was read verbatim.
