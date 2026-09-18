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

## Attempts

1. **The residually finite case is settled; the rest is isolated (2026-09-18, lane `bh-free-12`).**
   - **Settled.** `rf-free-minimal-zn-actions-have-non-fp-derived-full-groups`: if `φ` is residually finite in the
     Kerr–Nowak sense, then `[[φ]]` is LEF (Ma, arXiv:2209.00580, Thm 5.5, read at source). So `D([[φ]])`, being simple
     and infinite, is not finitely presented (Vershik–Gordon).
     - This covers every product `φ_1 × ⋯ × φ_N` of minimal Cantor `Z`-systems, and every free `Z^N`-odometer.
     - For `N = 1` it is the Grigorchuk–Medynets argument.
   - **Where the LEF route stops.** `zn-subshift-is-rf-iff-periodically-approximable`: a `Z^N`-subshift is residually
     finite iff its patterns are uniformly approximable by configurations with finite orbit. So every minimal subsystem
     of a weakly aperiodic `Z^N`-SFT is **not** residually finite, and Ma's theorem says nothing about it.
   - **What is still open.** The question stands for free minimal `Z^N` actions that are not residually finite. These
     are not covered even by `circle-rotation-zd-derived-full-groups-are-not-fp`. Every minimal subsystem of a strongly
     aperiodic SFT, e.g. Robinson's, is such an action, and those are the natural test cases for AIM Problem 2.5. A
     decision there needs one of:
     - a proof of LEF (or of some other finite-presentation obstruction) that does not come from finite models of the
       action;
     - a genuinely new finite presentation, where the SFT's local rules would have to supply the finitely many
       relations.
