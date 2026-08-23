---
rg: 2
id: nonaffine-source-gadgets-force-a-pinned-two-tail-kernel
kind: claim
title: An exact R-star pp gadget for a nonaffine relation has a nonempty pinned two-tail kernel
distinct_from:
  fano-cap-range-sections-cannot-encode-nonaffine-relations: that gives the affine-projection obstruction once cap-valued witness ranges exist; this proves that low-incidence peeling would construct exactly those forbidden ranges.
  culf-mastel-rstar-reduction-is-support-blind: that audits the unspecified NP reduction in the paper; this gives an incidence property every possible exact gadget for a nonaffine source relation must satisfy.
---

**ESTABLISHED.**  Let a finite conjunction of `R_*` rows pp-define a
nonaffine Boolean relation `C` on its visible variables.  Pin all visible
variables and compute the pinned two-tail kernel of the target rows.  The
kernel is nonempty.

Otherwise reverse peeling constructs, simultaneously for every visible
assignment in `C`, target witnesses whose range at each target occurrence is
contained in a fixed maximal cap.  Affinizing those ranges stays inside
`R_*`, and projecting the resulting affine target system expresses `C` as an
affine relation.  This contradicts nonaffinity.

Consequently the incidence strategy cannot eliminate the hard local content
of the Culf--Mastel reduction.  It moves all of it into a finite pinned kernel
where every surviving `R_*` row has at least three visible-or-internally
shared coordinates.

