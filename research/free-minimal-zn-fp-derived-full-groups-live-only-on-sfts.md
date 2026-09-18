---
rg: 2
id: free-minimal-zn-fp-derived-full-groups-live-only-on-sfts
kind: claim
title: For a free minimal action φ of Z^N on the Cantor set, D([[φ]]) is finitely generated iff φ is expansive, and if D([[φ]]) is finitely presented then φ is conjugate to a minimal subshift of finite type; so Matui's question is exactly the question for free minimal Z^N SFTs, N ≥ 2
distinct_from:
  free-minimal-zn-derived-full-groups-are-never-fp: that is Matui's open question itself; this reduces it, for all free minimal actions and not only subshifts, to minimal free SFTs.
  zd-derived-full-group-fp-forces-finite-type: that proves "finitely presented forces finite type" for free minimal subshifts; this removes the subshift hypothesis.
  rf-free-minimal-zn-actions-have-non-fp-derived-full-groups: that settles residually finite actions through LEF; residually finite subshifts are never SFTs, so that case is also contained here, and this adds every non-expansive action.
  derived-full-group-fg-iff-minimal-subshift: that is the case N = 1 of the first statement (Matui's Theorem 5.4).
---

**ESTABLISHED** by `free-minimal-zn-fp-derived-full-groups-live-only-on-sfts-proof` (lane `bh-partials`, a
combination of one elementary lane proof and two nodes on main; not independently reviewed; no priority claimed).

## Statement

Let `N ≥ 1` and let `φ` be a free minimal action of `Z^N` on a Cantor space `X`.

1. `D([[φ]])` is finitely generated **iff** `φ` is conjugate to a (free minimal) subshift.
2. If `D([[φ]])` is finitely presented, then `φ` is conjugate to a free minimal `Z^N`-subshift **of finite type**.
3. For `N = 1` there is no such SFT, which recovers Matui's theorem that `D([[φ]])` is never finitely presented.
   For `N ≥ 2`, Matui's question (arXiv:1602.00383v2, TeX l. 1402–1406; node
   `free-minimal-zn-derived-full-groups-are-never-fp`) is **equivalent** to this one:
   *is `D([[Z^N ~ X]])` finitely presented for some free minimal `Z^N`-SFT `X`?*

## What this does to Matui's question

- **Settled here.** Every non-expansive free minimal action, where `D` is not even finitely generated: odometers,
  equicontinuous actions, products with an equicontinuous factor.
- **Already settled on main, now subsumed.**
  - Residually finite actions (`rf-free-minimal-zn-actions-have-non-fp-derived-full-groups`).
  - Non-SFT subshifts (`zd-derived-full-group-fp-forces-finite-type`).
- **Also settled on main, by its own argument.** Codings of free rotations
  (`circle-rotation-zd-derived-full-groups-are-not-fp`).
- **What remains, exactly.** Minimal free `Z^N`-SFTs. They are strongly aperiodic, and none is residually finite. The
  first test case is Labbé's `Omega_U` (`labbe-shift-derived-full-group-is-finitely-presented`, OPEN in both
  directions).
- **Status of the printed question.** It is still OPEN. It is now a single, sharply posed question about aperiodic SFTs.

## Lesson for general BH

- **The whole dynamical family collapses onto one object.** For free minimal abelian dynamics, finite generation forces
  a subshift (`free-action-fg-alternating-full-groups-force-expansivity`) and finite presentation forces finite type.
- **So both questions are one gate.** The only systems that can carry a finitely presented derived full group are
  minimal free SFTs. Deciding Matui's question positively is the same problem as the master route's `Z^2` building
  block: a minimal free SFT whose local rules supply finitely many relations (premise (P2), and quantum rigidity, E2).
- **No new obstruction family is needed.** There is none left outside SFTs to find. Any further progress on either side
  of Matui's question is progress on E2/P2 for aperiodic SFTs, and conversely.
