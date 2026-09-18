---
rg: 2
id: free-minimal-zn-derived-full-groups-are-never-fp
kind: claim
title: For no free minimal action of Z^N on a Cantor set is the derived subgroup of its topological full group finitely presented
refuted_by:
  - labbe-shift-derived-full-group-is-finitely-presented
distinct_from:
  zd-derived-full-group-fp-forces-finite-type: that proves finite presentation of D([[Z^d ~ X]]) forces X to be of finite type; with it this claim, for free minimal subshifts, reduces to shifts of finite type.
  labbe-shift-derived-full-group-is-not-finitely-presented: that is the single instance for Labbé's minimal aperiodic Wang shift, the first test case of this claim.
  circle-rotation-zd-derived-full-groups-are-not-fp: that proves non-finite-presentation for codings of free circle-rotation Z^d actions only; this is the general free minimal Z^N case that Matui leaves open.
artifacts:
  - research/artifacts/gq-bh-openq-papers-list.md
---

**OPEN** (stated in the expected negative direction; the printed source asks whether
finite presentation can occur). H. Matui, *Topological full groups of étale
groupoids*, arXiv:1602.00383v2 (TeX main.tex l.1402–1406): after recalling that
Grigorchuk–Medynets proved `[[G_φ]]` locally embeddable into finite groups for
minimal `Z`-actions, "which implies that D([[G_φ]]) never be finitely presented",
Matui writes:

> We do not know if D([[G_φ]]) can be finitely presented when φ is a free minimal
> action of Z^N.

**Reduction on main (added 2026-09-18).** For free minimal subshifts, `zd-derived-full-group-fp-forces-finite-type` shows a finitely presented derived full group forces finite type. So among free minimal subshifts the open cases are the shifts of finite type. The reduction does not cover non-expansive (non-subshift) actions; for `Z`-actions their derived full groups are not even finitely generated (Matui), and the `Z^N` analogue is not recorded on main. The first test case is Labbé's `Omega_U` (`labbe-shift-derived-full-group-is-finitely-presented`, `labbe-shift-derived-full-group-is-lef`, both OPEN). A finitely presented answer for `Omega_U` refutes this claim. `periodic-approximable-subshifts-host-no-fp-simple-group` covers the periodically approximable case, and aperiodic SFTs are exactly where periodic approximations fail.

**Status on main.** `circle-rotation-zd-derived-full-groups-are-not-fp` (review
PASS) settles one family of free minimal `Z^d` actions. For `N = 1` the answer is
the Grigorchuk–Medynets LEF argument. The natural general route is local
embeddability into finite groups for free minimal `Z^N` actions (an infinite simple
LEF group is not finitely presented). The relevance to Boone–Higman: for free minimal subshifts these groups are finitely
generated, infinite and simple (`minimal-z2-subshift-derived-full-groups-are-fg-simple`), and they are
amenable in some cases (the interval-exchange realizations; see `circle-rotation-zd-derived-full-groups-are-not-fp`).
A finitely presented amenable one would answer Zaremsky's Problem 1.10
(`zaremsky-1-10-fp-infinite-simple-amenable-group`). *Correction (2026-09-18):* an earlier version
of this sentence called all of them amenable. That is not claimed: Elek–Monod constructed
minimal free `Z^2` subshifts whose full groups contain free subgroups (recalled, not re-read).

**Related printed problem.** AIM problem list *Amenability of discrete groups*
(http://aimpl.org/amenablediscrete), section "Topological Full group, IET and PRG",
Problem 2.5: "Find an example of a Z²-action on a Cantor set such that the commutator
subgroup of the topological full group is f.p." This allows Z² actions that are not free
or not minimal. So even if this node holds, the AIM problem stays open for those actions.
Accessed 2026-09-18; recorded in `research/artifacts/gq-bh-openq-lists.md`.
