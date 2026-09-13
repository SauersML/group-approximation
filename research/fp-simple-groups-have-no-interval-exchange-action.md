---
rg: 2
id: fp-simple-groups-have-no-interval-exchange-action
kind: claim
title: A finitely presented infinite simple group has no nontrivial action by interval exchange transformations
distinct_from:
  circle-rotation-zd-derived-full-groups-are-not-fp: that shows derived full groups of free Z^d circle-rotation codings are never finitely presented, because the coding is never of finite type; this shows every finitely generated interval exchange group is LEF, so no finitely presented infinite simple group acts by interval exchanges at all, with no freeness or full-group hypothesis
  periodic-approximable-subshifts-host-no-fp-simple-group: that removes subgroups of full groups of periodically approximable subshifts through SFT neighbourhoods; this removes groups of interval exchanges of the circle through LEF and rational specialisation
  interval-exchange-groups-are-lef: that is the LEF theorem for all finitely generated interval exchange groups; this is its consequence for finitely presented infinite simple groups
---

**ESTABLISHED.** Let `S` be a finitely presented infinite simple group. Every
homomorphism from `S` to the group of interval exchanges of the circle, or of `[0, 1)`,
is trivial.

**Why it matters for `fp-infinite-simple-amenable-group`.** Groups of interval exchanges
are the host where amenability is best understood: Juschenko–Matte Bon–Monod–de la
Salle prove that interval exchange groups with translation group of rank at most 2 are
amenable (arXiv:1503.04977, as recorded in `labbe-shift-derived-full-group-is-amenable`
and `fp-simple-amenable-z2-sft-2026-09-12.md`). This claim shows that no example lives
there. The same holds for any group mapping injectively into interval exchanges, for
example a full group realized by piecewise translations of a circle with finitely many
pieces.

Polygon exchanges are not covered. Rational perturbation of a toral polygon exchange
creates sliver atoms (`labbe-shift-derived-full-group-is-lef`, Attempts), and that is
where Labbé's shift lives.

Route: `fp-simple-groups-have-no-interval-exchange-action-proof`.
