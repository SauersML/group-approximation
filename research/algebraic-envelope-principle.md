---
rg: 2
id: algebraic-envelope-principle
kind: claim
title: A non-CE algebra inside an algebraic compact abelian crossed product yields a non-hyperlinear group
distinct_from:
  non-ce-property-t-equivalence-relation-exists: that produces the non-Connes-embeddable relation algebra; this converts any ALGEBRAIC-action envelope of such an algebra directly into a countable non-hyperlinear group by Pontryagin duality.
  kun-thom-clifford-crossed-product-ce: that asks Connes embeddability of one specific crossed product as an input to another lane; this is the general duality compiler showing that a negative answer for any algebraic compact abelian base is itself a non-hyperlinear group, with no further work.
  canonical-trace-promotes-non-ce-profile: that must promote a hosted non-CE trace profile to the canonical trace through group relations; here no promotion is needed because Fourier duality makes the ambient algebra LITERALLY a group von Neumann algebra with its canonical trace.
---

Let `K` be a compact second-countable abelian group with Haar
probability measure, and let a countable discrete group `Lambda` act on
`K` by continuous group automorphisms.  Let `A = hat K` be the
Pontryagin dual, a countable discrete abelian group with the dual
`Lambda`-action.  Then:

1. The Fourier transform implements a canonical trace-preserving
   isomorphism

   ```text
   L^infinity(K, Haar) rtimes Lambda  ~=  L(A rtimes Lambda),   (AEP1)
   ```

   carrying the crossed-product trace (Haar integration composed with
   the canonical conditional expectation) to the canonical group trace.

2. Consequently, if ANY non-Connes-embeddable tracial von Neumann
   algebra embeds trace-preservingly into
   `L^infinity(K) rtimes Lambda`, then the countable discrete group
   `A rtimes Lambda` is **not hyperlinear**.

This bypasses every stability question in the program: no
Hilbert--Schmidt stability, no packet recovery, no trace promotion, no
microstate soundness.  The canonical trace appears for free because the
ambient algebra is a group factor on the nose.  The entire remaining
content of this route to the goal is the envelope hole
`non-ce-relation-admits-algebraic-action-envelope`.

The principle also reads existing open nodes in a new way: a NEGATIVE
answer to a crossed-product CE question over an algebraic base (such as
the Clifford crossed products already tracked by the graph) is not
merely an obstruction elsewhere — through `(AEP1)` it IS an explicit
non-hyperlinear group.
