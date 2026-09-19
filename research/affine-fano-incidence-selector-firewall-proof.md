---
rg: 2
id: affine-fano-incidence-selector-firewall-proof
kind: route
title: Project the affine gadget and separate its zero-free tail image
target: affine-fano-incidence-selector-exists-iff-cap-support
requires:
  - rstar-fano-caps-have-seven-maximal-parity-covers
---

Project the affine scalar solution set of the proposed LCS gadget to the
visible tail and functional triples.  Its tail projection is affine and,
under sound incidence, omits zero.  Writing it as `b+W`, separate `b` from
`W` by a linear functional.  That functional is one on the whole projected
support, hence supplies the fixed maximal Fano cap.  Conversely a fixed cap
functional is itself one affine row.  Varying each incidence fiber shows
that the full incidence relation has no nonconstant affine functional and
therefore has full affine hull.
