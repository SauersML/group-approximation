---
rg: 2
id: balanced-pauli-incidence-labeling
kind: claim
title: Label the occurrence Pauli incidence family with balanced mixed contours
distinct_from:
  colored-cayley-pauli-incidence-separation: that is the full Cayley placement theorem; this isolates the remaining combinatorial hypothesis needed by the balanced Greendlinger sign-separation theorem.
  expander-cloud-reduction-preserves-pauli-dimension-gap: that permits arbitrary fixed-gap expanders inside each equality cloud; this additionally constrains how pair incidences are distributed around every mixed contour.
---

OPEN.  Construct the dimension-preserving expander-cloud reduction of the
robust Pauli games together with a finite edge labeling satisfying one
ordinary graphical `C'(lambda)` condition and the balance condition `(BG2)`
of `balanced-greendlinger-separates-sign-cosets`, uniformly over the whole
family.

Pure equality-cloud cycles may be relators: the balanced Greendlinger proof
peels them.  The load-bearing demand is only on mixed contours.  Every mixed
contour must encounter sign/pair edges frequently enough that any interval
covering more than a `(1-3lambda)` fraction of the contour contains at least
three of them.

## Attempts

- **Ordinary independent expander clouds.**  They preserve the dimension
  witness, but a mixed cycle may travel a macroscopic distance inside one
  cloud between two pair incidences, so `(BG2)` is not automatic.
- **Make the incidence graph high girth.**  Girth controls total contour
  length, not the largest monochromatic equality arc, and therefore does not
  imply balance.
- **Take an arbitrary covering lift.**  This can improve local geometry but
  can unwind the contextual cycles or lose the dimension bound by the sheet
  factor.

The surviving design target is a replacement product in which equality
consistency remains an expander while pair ports form a uniform net on every
cycle, with a same-Hilbert-space decoder.

