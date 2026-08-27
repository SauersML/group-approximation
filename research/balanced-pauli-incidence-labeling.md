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
- **Growing pair clouds plus endpoint equality expanders.**  The game gap is
  preserved on the same Hilbert space, but every two copies of one logical
  pair edge form a mixed contour containing exactly two pair edges.  Taking
  that whole contour as the interval in `(BG2)` violates balance.  See
  `equality-synchronized-lifts-create-two-pair-contours`.

The surviving design target must avoid equality-connecting two copies of the
same logical pair edge.  A replacement product of ordinary equality fibers
cannot do this.  The remaining options are direct threshold-rectangle
labeling or a non-equality synchronizing code with a same-Hilbert decoder.

This replacement is genuinely necessary.  By
`complete-pauli-rectangles-defeat-three-p-balance`, the unmodified complete
table always has rectangles with one equality-edge gap and another gap of
growing diameter; an interval with only two pair edges then covers a fraction
tending to one.  Thus no relabeling of independent equality expanders can
establish `(BG2)`.

Bounded private sign cells do not alter this conclusion.  The ordinary part
of `constant-private-pauli-gadgets-fail-incidence-separation` shows that a
Magic-Square, Heisenberg, or central-square subdivision adds only `O(1)` to
the four corners of the short-gap/diameter-gap rectangle.  Its bad interval
still occupies `1-O(1/L)` of the contour.  Hence the surviving
non-equality synchronizing code must change the large-scale mixed incidence,
not merely replace each pair edge by a robust constant-size test.
