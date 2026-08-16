---
rg: 2
id: nuclear-embeddability-is-inherited-by-subalgebras
kind: claim
title: Nuclear embeddability passes to C-star subalgebras, and nuclear algebras have it
distinct_from:
  exact-stably-finite-non-mf-reduced-group-algebra: that claim asserts exactness of the concrete witness algebra, which rests on four external theorems and is not formalized; this is the definable fragment of that vocabulary and the two permanence facts that fragment actually supports.
  literal-stably-finite-non-mf-reduced-group-algebra: that concerns the concrete reduced group algebra of the literal witness, its stable finiteness and its failure of MF; this is a general C-star statement with no group in it, and it supplies none of that claim's clauses.
artifacts:
  - non_mf_groups_exist.tex
  - GroupApproximation/Analysis/CStarExactness.lean
---

Say a C-star algebra is **nuclearly embeddable** when it admits an injective
⋆-homomorphism into some C-star algebra which is a nuclear map — point-norm
approximable, uniformly on finite subsets, by composites of completely positive
contractions through a finite-dimensional C-star algebra.  Then:

- nuclear embeddability **passes to subalgebras**: if `A` embeds by an injective
  ⋆-homomorphism into a nuclearly embeddable `B`, then `A` is nuclearly
  embeddable;
- every **nuclear** C-star algebra (one whose identity is a nuclear map, i.e.
  with the completely positive approximation property) is nuclearly embeddable;
- `ℂ` is nuclear, so the notion is not vacuous;
- every ⋆-homomorphism of C-star algebras is completely positive, and completely
  positive maps compose, so the composition bookkeeping the two permanence facts
  need is available.

For separable algebras nuclear embeddability is Kirchberg's characterization of
**exactness**, and by Gelfand--Naimark it agrees with the textbook definition in
terms of a concrete representation on a Hilbert space.  Neither of those
equivalences is claimed here; they are what the definition is *chosen to match*.

## Why this is stated as the definable fragment rather than as exactness

`non_mf_groups_exist.tex` (paragraph *An exact stably finite non-MF algebra*)
says outright that exactness is the one clause of that paragraph not verified in
Lean, "the present formal library has no definition of exact C⋆-algebras", and
cites a chain of four research papers: amenable groups are exact; Guentner--
Higson--Weinberger for finitely generated linear groups; Kirchberg--Wassermann
for closure of exactness under extensions; Kirchberg--Wassermann for the
equivalence with exactness of the reduced group algebra.  None is in Mathlib.

What Mathlib lacks at the pinned revision (mathlib `v4.32.2`) is not a lemma but
the vocabulary: **no** tensor product of C-star algebras of any kind — minimal,
maximal, or any C-star norm on an algebraic tensor product — no Hilbert space
tensor product (only the algebraic inner-product space, with no completion
assembled), no nuclearity, no exactness, no quotient of a C-star algebra by a
closed two-sided ideal as a C-star algebra, no amenability of groups, and no
Gelfand--Naimark.  With no tensor product there is no short exact sequence to
tensor, so the *definition* of exactness cannot even be written.

This claim records what can be written down instead, and it is a genuine
definition with content rather than a stub: the approximation is by completely
positive **contractions** through finite-dimensional algebras, uniformly on
finite sets, and dropping any of those clauses would trivialize it.  The
permanence facts it supports are exactly the two the manuscript's argument uses
in the direction that does not need Kirchberg--Wassermann — heredity along an
embedding, and nuclear implies nuclearly embeddable — so the trust surface for
the paragraph is narrowed to the extension and group-algebra steps rather than
being left as "exactness is not formalized".
