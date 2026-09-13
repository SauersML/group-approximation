---
rg: 2
id: labbe-shift-is-wall-rigid-proof
kind: route
title: Difference sets of Labbé tilings are crossing networks of fault sheets, syndetic sets, or unions of full fault lines
target: labbe-shift-is-wall-rigid
requires: [labbe-shift-is-a-toral-rotation-coding, minimal-aperiodic-wang-shift-exists]
artifacts:
  - research/artifacts/labbe-shift-wall-rigidity-2026-09-13.md
---

The artifact, Sections 1–3, gives the complete proof. Outline, with `x_i = f(T_i)` and `v = x_2 - x_1`:

1. **Lemmas.**
   - An interior point of an atom forces the letter, and a letter forces the closed atom.
   - Every tiling is a limit of generic codings, and reads a constant side along each exact-hit set of a
     segment.
   - For a minimal zero-entropy SFT, no `2D`-component of a difference set is finite. Flipping a finite
     cluster at syndetic occurrences would give positive entropy.
2. **Sheets.** `(ke)α = kαe` for `e ∈ {(1,0), (0,1), (1,-1)}`, and `mα ≡ (m_2 - m_1/φ)(1,-φ)` mod `Z^2`. So
   the orbit points near a segment of each boundary direction lie on lattice lines or golden strips with
   bounded gaps. Returns to intervals have bounded gaps, by the three-distance theorem for `φ`, which is
   recalled.
3. **Large `|v|`.** The partition is not translation-invariant, so an open ball of disagreement of uniform
   radius exists, and the difference set is syndetic.
4. **Small `|v| != 0`.**
   - Core parallelograms swept by segment interiors translated by `v` give core sheets inside the difference
     set, in at least two lattice directions.
   - These cross, forming a uniformly connected network, and every difference point lies on a core sheet.
   - Singular tilings are handled by passing to limits, using that paths in the network are local at scale
     `1/|v|`.
5. **`v = 0`.** Differences are full fault lines (consistent sides) plus finitely many vertex points. By the
   entropy lemma every component contains a full line. Lines of distinct directions cross, and parallel
   exact-hit sheets sit at bounded offsets.
6. **Conclusion.** Take `2D_0` above all the constants.
