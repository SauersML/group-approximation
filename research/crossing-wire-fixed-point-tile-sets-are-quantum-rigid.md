---
rg: 2
id: crossing-wire-fixed-point-tile-sets-are-quantum-rigid
kind: claim
title: A fixed-point Wang tile set whose macrotiles are deterministic and in which every two input wires cross is quantum rigid over every field; so a free (aperiodic) Z^2 SFT with finitely presented crossed product exists
artifacts:
  - research/artifacts/gq-bh-g2-fixedpoint-a-crossing-layout.md
distinct_from:
  fixed-point-wang-tile-rigidity-is-edge-family-commutation: that reduces rigidity of side-local fixed-point sets to commutation of face-local edge families; this proves that commutation for one explicit layout.
  free-minimal-z2-sft-is-quantum-rigid: that asks for a FREE MINIMAL rigid Z^2 SFT; this gives a free rigid one, and minimality is not proved.
  permutive-triangle-sfts-are-quantum-rigid: that gets rigidity from a group-like permutive law and allows periodic points; this gets it from hierarchical determinism, with no periodic point at all.
---

**ESTABLISHED (2026-09-18)** through `crossing-wire-fixed-point-tile-sets-are-quantum-rigid-proof`. Lane proof
(bh-g2-fixedpoint-a), elementary, **one referee PASS (bh-ref-engines, 2026-09-18), conditional on the explicit crossing-wire layout; see Referee section** (it answers the
free half of gate E2 over `Z^2`). No priority claimed.

## Setting: crossing-wire fixed-point layouts

`τ ⊆ C^4` is a self-similar Wang tile set: Durand–Romashchenko–Shen, arXiv:0910.2415 §2, read at source.
Each tile is its four colours, and the simulation `S` has zoom `N`. In every macrotile `S(t)`:

- **(L0) Coordinates.** Tiles carry coordinates `(i, j) mod N`, incremented across edges (DRS Example 2).
  Program bits are fixed by coordinates (DRS §2.3, "hard-wired program").
- **(L1) Side-local, margin `m >= 1`.** As in `fixed-point-wang-tile-rigidity-is-edge-family-commutation`.
  The only non-blank border edges are the `k` middle *bit edges* of each side.
- **(L2) Wires copy.** Wire, turn and fan-out tiles have equal bits on all their wire edges and blank
  (coordinate-only) edges elsewhere.
- **(L3) Complete crossing.** For any two bit edges of the four sides, a copy of one crosses a copy of the
  other in some crossing tile `(a, a, b, b)`. One way to get this: fan out each input into a row copy and a
  column copy in a box of size `O(k) × O(k)`.
- **(L4) Deterministic zone.** The computation zone is a one-head Turing machine time-space diagram whose row
  `0` holds input copies, fixed program bits and a fixed head.
  - The head's crossing edge is fixed by the head cell's bottom edge.
  - The top edge of each zone tile is fixed by its other three edges.
  - The zone accepts exactly when the four side colours form a tile of `τ`, and rejects invalid encodings.

DRS fix the wiring "in any reasonable way". (L2)–(L3) add two standard gadgets, crossing and fan-out, whose
geometry is computable in `poly(log N)` time. So the fixed-point argument of DRS §2.3 goes through unchanged
and gives such a `τ` for all large `N` (construction step recalled, not re-verified line by line).

**Layout written out** (after referee review 11493c386): `research/artifacts/gq-bh-g2-fixedpoint-a-crossing-layout.md`. It gives the tile families, the crossing box,
the head-edge zone encoding, and a proof that every rule is coordinate-fixed and checkable in `poly(log N)` time.

## Theorem

Let `τ` satisfy (L0)–(L4). Then:

1. every face-local edge family of `τ` commutes;
2. `Ω_τ` is `D`-quantum rigid for every `D >= 1` and every field `k`;
3. `LC(Ω_τ, k) ⋊ Z^2` is finitely presented (`sft-crossed-product-fp-iff-quantum-rigid`);
4. `Ω_τ` has no periodic point (DRS §2.1: every period is divisible by every `N^k`).

**Mechanism.**
- Crossings make the raw input bits of each macrotile commute.
- Determinism makes every edge of the macrotile a function of those bits.
- So each macrotile is a commuting "level-1 tile", and the level-1 edge family is again an edge family of
  `τ`. Iterate.
- Two edges are either in one level-`K` block or within the margins of a common side (or corner), and they
  commute either way.

## Consequences and limits

- **First aperiodic rigid shift here.** This is the first quantum-rigid `Z^2` SFT without periodic points on
  main. It settles the free half of `free-minimal-z2-sft-is-quantum-rigid`.
  - Minimality is not proved. `Ω_τ` has fault configurations, and a minimal version would need the
    Durand–Romashchenko mechanism (arXiv:1802.01461) run with deterministic slots.
  - Every sub-SFT of `Ω_τ` is rigid (`quantum-rigidity-passes-to-sub-sfts`). So a free minimal SFT *inside*
    `Ω_τ` would finish gate E2 over `Z^2`.
- **Not matricial.** By `matricial-aperiodic-sft-rings-are-not-quantum-rigid`, `LC(Ω_τ, k) ⋊ Z^2` is a
  finitely presented algebra with no unital embedding into an ultraproduct of matrix algebras.
- **Crossings are needed for the proof.** Suppose instead that a single head scans inputs `B_1, …, B_4` and
  keeps only their parity. Operators then have to commute only inside the contexts `{B_1, B_2}`,
  `{B_1 B_2, B_3}` and `{B_1 B_2 B_3, B_4}`, and the Pauli choice `ZI, IZ, XX, −YY` satisfies every context of that
  block while `ZI` and `XX` anticommute. This is local to one macrotile; no global edge family is claimed.

## Lesson for general BH

- **Rigidity is manufactured by co-location, not by geometry.** Two raw bits commute once copies of them meet
  in one tile. Deterministic gates then spread commutation to everything they compute.
- **Design rule.** A hierarchical simulation is quantum rigid when every macrotile brings every pair of its
  inputs together (complete crossing) and computes everything else deterministically. Faults cost nothing,
  because side-local margins make both sides functions of one shared side.
- **For the master route.**
  - E2 over `Z^2` is now reduced to *minimality* of a crossing-wire fixed-point shift.
  - The same design should be tried in the simulations over `Λ_0 × Z^2`
    (`plane-constant-simulation-computation-layers-are-quantum-rigid`).
  - There, the forced ambiguity of `bounded-determination-simulations-only-realize-sft-shadows` must be
    carried on crossing wires.

## Referee (bh-ref-engines, 2026-09-18): PASS, conditional on writing out the layout

I checked the proof node line by line, together with the parent reduction
(`fixed-point-wang-tile-rigidity-is-edge-family-commutation`). I also re-read DRS arXiv:0910.2415 §2 at source
(`fpt-arxiv.tex`: Example 2, Prop. `selfsimilar-aperiodic`, "Simulating a tile set" and "Simulating itself").

**The operator argument (proof Steps 1–5) is correct, given (L0)–(L4).**
- *Step 1.* The coordinate projections lie in the algebra of every single edge and are transported along the grid,
  so they are central. This is correct.
- *Step 2(a).* The wire and fan-out tiles force equal PVMs, via F1 plus F2 on mismatched bits. The crossing tile
  `(a,a,b,b)` makes the copies of `e` and `e'` commute by F1. Both steps are correct.
- *Step 2(c), crossing edges.* For a deterministic one-head machine, "head leaves `j−1` to the right in state `q`"
  is exactly the set of tiles at face `(t, j−1)` whose bottom edge has the head in a right-moving transition to
  `q`. So `P_(R,q)(v)` is a sum of bottom-edge projections. Top edges follow from the face rule. This is correct.
- *Step 3.* On a joint spectral projection `Π` of the `4k` bits, every edge of the block is a scalar colour. If a
  face has no valid completion, `Π = Π·(vanishing product) = 0`. So `P^1` is an FLEF of `τ`. Also `A(Z) = A_1(Z)`,
  because each single bit is a sum of `P^1` projections once non-encoding values vanish. This is correct.
- *Steps 4–5.* The margin induction (I2) is the reduction node's scaling of the margin (`m N^(K−1)`). The case
  split "same block / shared side / shared corner" is exhaustive once `d < m N^(K−1) ≤ N^K`. This is correct.
- *Field independence.* Only idempotents and finite central decompositions are used, so the argument works over
  every field.

**The gap: the layout is a modification of DRS, not DRS as written.**
- DRS say explicitly: "(this can be done in any reasonable way; **we assume that wires do not cross each
  other**)". So (L3) complete crossing departs from their stated layout. The node's gloss "DRS fix the wiring in
  any reasonable way" should add this.
- Their computation zone is described through 3×2 window tiles (footnote `local-rules-footnote`). It does not
  literally give (L4) ("top edge fixed by the other three; the head's crossing edge fixed by the head cell's
  bottom edge"). (L4) needs the standard direct encoding of a deterministic one-head machine, in which cells
  carry a symbol plus an optional head state on horizontal edges and head moves are carried on vertical edges.

**Why the modification is harmless.**
- DRS's fixed-point step ("Simulating itself") needs only one thing: the program can check, in time polynomial in
  the `O(log N)`-bit input, that macro-tiles obey `τ`'s coordinate-determined local rules (coordinates, wires,
  zone, program bits). Crossing tiles, fan-out tiles and the direct machine encoding are further such rules.
- So the Kleene-style closure goes through verbatim, and a `τ` with (L0)–(L4) exists for all large `N`. I judge
  the claim correct.
- Recommended: write the crossing box and the zone encoding explicitly in the node, as a checkable
  coordinate→role table.

**Trimming (no gap).** The proof shows that every FLEF of the **untrimmed** `τ` commutes. FLEFs of the trimmed
`τ' ⊆ τ` are FLEFs of `τ`, and `Ω_τ' = Ω_τ`. So item 1 of the reduction node, which is stated for trimmed sets,
applies with `τ'`.

**Items 3–4.** These are imported: `sft-crossed-product-fp-iff-quantum-rigid` (not re-checked here) and DRS
Prop. `selfsimilar-aperiodic` (read at source). Nonemptiness of `Ω_τ` is DRS's compactness remark.

**Credit.** Durand–Romashchenko–Shen for the fixed-point tile sets. The co-location mechanism is new here as far as
I know. The local Pauli example is in the spirit of Mermin–Peres contextuality.
