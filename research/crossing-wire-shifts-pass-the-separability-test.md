---
rg: 2
id: crossing-wire-shifts-pass-the-separability-test
kind: claim
title: In a crossing-wire fixed-point tiling, two modifications that change the type of a common macrotile have intersecting difference sets; so the crossing-wire shifts, their one-way variant and its transplants pass the separable-modifications test, and complete crossing is exactly what the test asks of a layout
requires:
  - cross-layer-separable-modifications-kill-quantum-rigidity
  - crossing-wire-fixed-point-tile-sets-are-quantum-rigid
distinct_from:
  crossing-wire-fixed-point-tile-sets-are-quantum-rigid: that proves quantum rigidity through face-local edge families; this checks the classical necessary condition (no separable modifications) independently, and identifies complete crossing as its combinatorial content.
  cross-layer-separable-modifications-kill-quantum-rigidity: that is the test; this runs it on the E2 candidates on main.
---

**ESTABLISHED** for the Crossing Lemma and item 1 (lane bh-free-09, 2026-09-18; elementary, not
reviewed). Items 2–4 are an **audit**. They use the DRS structure facts recalled in the
crossing-wire nodes (unique macrotile decomposition, with faults allowed) and are not re-verified
line by line.

## Setting

`τ` satisfies (L0)–(L3) of `crossing-wire-fixed-point-tile-sets-are-quantum-rigid`, with a
deterministic zone, either (L4) or the one-way (L4′) of
`sw-crossing-wire-tiles-give-free-rigid-sfts-on-kazhdan-lattices`.
- A level-`n` macrotile of type `t` is the fixed pattern `S^n(t)`.
- `S` is injective, because the boundary of `S(t)` encodes the colours of `t`.
- Two points *share the decomposition* near a macrotile `M` if they cut `M` and its ancestors in the
  same way.

## Crossing Lemma

Let `x, x_1, x_2 ∈ Ω_τ` share the decomposition near a level-`n` macrotile `M`, and suppose the type
of `M` in `x_1` and the type in `x_2` both differ from the type in `x`. Then
`Δ(x, x_1) ∩ Δ(x, x_2) ∩ M ≠ ∅`.

*Proof, by induction on `n`.* The case `n = 0` is immediate, since `M` is one tile.

For the step, let `t, t_1, t_2` be the three types of `M`.
- *A differing bit.* A Wang tile is its colours, and the coordinates agree because the decomposition
  is shared. So `t_1` differs from `t` in some bit `β_1` on some side, and `t_2` in some bit `β_2`.
- *It shows up along wires.* By (L2), every level-`(n−1)` tile on a wire copy of `β_i` carries that
  bit, so its type in `x_i` differs from its type in `x`.
- *The two wires meet.* By (L3), some crossing tile `C` carries copies of both `β_1` and `β_2`. If
  `β_1 = β_2`, take any tile on its wire. So the type of `C` differs from the type in `x` both in `x_1`
  and in `x_2`.
- *Descend.* Apply the induction hypothesis to `C`. `∎`

**Refinement (determining sides).** Suppose the colours on a set `Σ` of sides determine every tile.
For example, `Σ = {bottom, left}` for SW-deterministic tiles (A4 of
`minimal-crossing-wire-fixed-point-shift-is-quantum-rigid-proof`). Then complete crossing among the
bits on the `Σ` sides suffices: a difference of types is already a difference of `Σ`-colours.

## Theorem

1. **Shared ancestors.** Let `x_1, x_2` be modifications of `x` that share all decompositions with
   `x`. Suppose some differing point of `x_1` and some differing point of `x_2` lie in a common
   macrotile. Then `Δ(x, x_1) ∩ Δ(x, x_2) ≠ ∅`.
   - *Proof.* A differing child forces a differing parent, since the content of a macrotile is
     `S^n` of its type. So both modifications change the type of that common macrotile, and the
     Crossing Lemma applies.
2. **Faults (audit).**
   - *Cross faults.* At a cross fault the four corner macrotiles are corner children of their
     parents. Corners are blank, so each corner type is fixed, and the four quadrants are forced.
   - *Single faults.* At a single horizontal or vertical fault, each side is a function of the fault
     colours, by side locality (L1). The fault colours at level `n` are functions of those at level
     `n+1`, and they are blank as soon as the ancestor positions leave the middle bit block. So the
     only freedom is a change at infinity along one nested-middle ray, and any two such changes
     alter the same macrotiles `M_n(0)` for all large `n`. Item 1 applies.
   - *Grid changes.* A modification that changes the level-`n` grid changes the type of every
     level-`(n−1)` macrotile of a fault region, so it shares a changed macrotile with any other
     modification that reaches that region.
   - *Conclusion.* No two modifications of one point are separable. **The separable-modifications
     test is passed.**
3. **The three candidates.**
   - *Crossing-wire tiles (4f793f5c3c).* They pass by items 1–2.
   - *The one-way SW variant (7d228882f).* Its Layout Lemma keeps (L3), since the row copy of one
     input meets the column copy of the other, and it keeps blank corners. So it passes.
   - *Its Busemann transplants.* Preimages of intersecting difference sets intersect, and the
     skeleton is handled by bh-invent-04's transport theorem. So no independent clash can arise.
   - *The minimal version (49939b957a, bh-g2-fixedpoint-a): checked, it passes.* The check was
     whether some component of the side colours bypasses the crossing box. Its proof node lists every
     component that the Durand–Romashchenko minimality adds:
     - the rank field of DR §2.4, and the (p4) role pattern of the three encoding zones, are both fixed
       by coordinates, so they are program-like and never differ between types of one position;
     - every macro-colour bit, including the constant encoding zones, travels on wires that meet by
       (M1) (A1 there);
     - the diversification slots are 2×2 blocks forced by skeleton frames whose colours are functions
       of real coordinates (A3 there), so they are the same in `S(t)` for every type `t` and a type
       change never touches them.

     The fake coordinates inside slots do not affect the lemma. It compares the real coordinates of a
     macrotile in its father, which are carried by the connected non-slot skeleton (A2 there). So no
     side component bypasses the crossing box, and the Crossing Lemma applies at every level of the
     variable zoom.
4. **Why crossing is needed (audit).** Without (L3), two changes of different input bits of one
   macrotile change disjoint wire sets. In a zone whose computation *merges* (an irreversible scan
   in which a flipped bit is later forgotten), their zone differences occupy disjoint time windows.
   Their difference sets can then sit a macrotile-dependent distance apart at every level. This is the
   classical face of the non-crossing Pauli contexts recorded on the crossing-wire node. It is a risk,
   not a proved kill.

## Lesson for general BH

- **Co-location and inseparability are the same design requirement, seen quantumly and classically.**
  - *Quantum side:* complete crossing makes the input bits of every macrotile commute (the
    crossing-wire proof).
  - *Classical side:* it makes the difference sets of any two changes of one macrotile meet (the
    Crossing Lemma).
- **A cheap pre-screen for every future G2 layout.** Route every side component through the crossing
  box, keep corners blank and margins side-local, and the necessary condition holds by the lemma
  above.
- **Where to look for a failure.** Any component that bypasses the crossing box is exactly where a
  separable freedom, and hence a rigidity failure, would appear.

## Referee (bh-ref-ffwz, 2026-09-18): Crossing Lemma and item 1 PASS; items 2–4 correctly labelled as audit

- **Crossing Lemma.** The induction is correct, given (L0)–(L3) of
  `crossing-wire-fixed-point-tile-sets-are-quantum-rigid`, which I did not re-verify here.
  - With a shared decomposition, a type difference is a data-bit difference.
  - (L2) propagates it along the wire.
  - (L3) gives a child carrying both differences.
  - When `β_1 = β_2`, any wire tile works.
- **Item 1.** Correct. Injectivity of `S` means a differing child forces a differing parent.
- **Scope.** This shows that two modifications which share the decomposition and touch a common
  macrotile have intersecting difference sets, so they are never more than `2D` apart. Changes
  of the decomposition, and faults, are covered only by the audit (item 2). The claim "the test
  is passed" is therefore as strong as that audit.
- **What the test gives.** Passing the separability test is necessary for rigidity, not
  sufficient. The node says so.
