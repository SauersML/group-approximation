---
rg: 2
id: greendlinger-free-product-lemma-citation
kind: route
title: Import classical C'(1/6) Greendlinger and torsion theory over free products
target: greendlinger-free-product-lemma
requires: []
---

The mathematical input of this claim is classical small-cancellation theory.

For ordinary free-group presentations, Lyndon--Schupp, *Combinatorial Group
Theory*, Chapter V, Section 4 (Greendlinger's lemma; Theorem V.4.4 in the
standard numbering) proves that a nonempty reduced trivial word in a
`C'(lambda)` presentation, `lambda <= 1/6`, contains an exterior subword of a
symmetrized defining relator of length greater than
`(1-3 lambda)|r|`, hence greater than `|r|/2` at `lambda=1/6`.  This is exactly
the free-group `GreendlingerGate` conclusion used by Cairn.

For a free product `F=*_{i} G_i`, Chapter V, Section 9 develops the same metric
small-cancellation theory with free-product syllable length.  Theorem V.9.3 is
the free-product Greendlinger theorem: under `C'(1/6)` the reduced boundary of
a nontrivial null word contains the corresponding long relator arc.  Its
standard Corollary V.9.4 gives injectivity of the factors; this is the relative
normal-form version needed by the router.

The standard torsion theorem for small-cancellation products in the following
section says that finite-order elements in the quotient are conjugate to the
finite-order elements coming from the factors (with the usual proper-power
exception for relators).  Thus, when the factors are torsion-free and the
chosen relators are not proper powers, the quotient is torsion-free.  With
finitely presented factors and a finite relator family, finite presentation of
the quotient is immediate by adjoining that finite family to the union of the
factor presentations.

These are theorem-level group-theoretic inputs independent of the repository's
unfinished Lean proof.  `SmallCancellationRouter.lean` may still formalize the
same combinatorics internally, but lack of that formalization is not a
mathematical gap in the claim recorded here.