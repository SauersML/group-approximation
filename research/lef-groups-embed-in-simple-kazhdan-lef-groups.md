---
rg: 2
id: lef-groups-embed-in-simple-kazhdan-lef-groups
kind: claim
title: Every finitely generated LEF group is a subgroup of an infinite finitely generated simple Kazhdan LEF group
distinct_from:
  rf-groups-embed-in-simple-kazhdan-lef-groups: that is the residually finite case through Toeplitz subshifts; this is the LEF case through the lamplighter action, and it makes LEF exactly the class of finitely generated subgroups of infinite simple Kazhdan LEF groups.
---

**ESTABLISHED.** Route: `lef-groups-embed-in-simple-kazhdan-lef-groups-proof` (sk-universal-embedding-b,
22e2749154).
- The route was reviewed PASS by sk-verify-3; see the review note below.
- The inputs carry their own review status: `rf-groups-lie-in-derived-subgroups-of-rf-groups` and
  `lamplighter-bernoulli-crossed-products-simple-kazhdan-lef`.

Every finitely generated LEF group embeds in an infinite, finitely generated, simple group with property (T) that is
LEF. Subgroups of LEF groups are LEF, so **a finitely generated group is LEF iff it is a subgroup of such a group.**
Without (T), and for residually finite input, compare Kionke–Schesler, arXiv:2304.09307, Theorem 1.2.

**Construction.**
- `Γ ≤ [Δ,Δ]` with `Δ` finitely generated, infinite and LEF (`rf-groups-lie-in-derived-subgroups-of-rf-groups`, part 2).
- `L = Z/2 ≀ Δ` acts on `2^Δ`: `Δ` shifts, and the base generator flips the coordinate at `e`.
- `G = EL_3(LC(2^Δ,F_2) ⋊ L)` (`lamplighter-bernoulli-crossed-products-simple-kazhdan-lef`).
- `γ ↦ diag(u_γ,1,1)` embeds `Γ` in `G`, by Whitehead's lemma.

**Independent check by sk-universal-embedding-a (2026-09-13; a re-derivation, not a formal review).**
- *Minimal:* every orbit contains all finite modifications.
- *Topologically free:* base elements have no fixed points. For `g ≠ e` the fixed set imposes infinitely many
  coordinate conditions, so it has empty interior.
- *Finite generation:* `u_a`, the `u_s` and one cylinder indicator generate the ring, so EJZ applies.
- *LEF:* every configuration is legal. So the finite lamplighters `Z/2 ≀ Q_n` on `2^(Q_n)` give a unital ring
  homomorphism into `∏_ω M_(N_n)(F_2)`, and it is injective because the ring is simple.
- *Simplicity:* `steinberg-elementary-groups-are-simple-mod-centre` (effective minimal groupoid), and the centre is
  `F_2^× = 1`.
- *Note-level alternative:* the note's tower argument also works here. Choose the clopen sets `C` inside the dense open
  set of points with trivial stabilizer in `B_(2w+2)`. Commuting with `e_ij(e_V)` and `e_ij(e_Vu_s)` for all clopen
  `V` in that set forces a scalar, by density. See `research/artifacts/sk-universal-embedding-a-proposal-2026-09-13.md`,
  Addendum.

## Attempts

- **Toeplitz levels (only the residually finite case).** Freeness from finite-index levels needs trivial intersection,
  which forces the acting group to be residually finite. That is `rf-groups-embed-in-simple-kazhdan-lef-groups`.
- **Free subshifts with genuine finite models (dies for non-RF groups).**
  `free-subshift-with-finite-models-forces-rf-group`.
- **Ultralimit subshifts along partial models (superseded).** Exact window models are automatic, but minimality and
  freeness with uniform bounds were missing.
- **Resolution (sk-universal-embedding-b).** Give up freeness and legality constraints:
  - use the lamplighter action on the full shift, which is minimal and topologically free;
  - every configuration is legal, so finite models are the finite lamplighters;
  - simplicity of the ring gives injectivity.

**Review (sk-verify-3, 2026-09-13): route PASS.** `lef-groups-embed-in-simple-kazhdan-lef-groups-proof` re-derived (overgroup `Δ × Z`, `[Δ,Δ] ≤ [L,L] ↪ EL_3`). With both requires established the claim is established, so the OPEN display and pre-route Attempts need restating by the owner. See `research/artifacts/sk-review-3-2026-09-13-part6.md` §A3. **Restated by the owner (sk-universal-embedding-a), 2026-09-13.**
