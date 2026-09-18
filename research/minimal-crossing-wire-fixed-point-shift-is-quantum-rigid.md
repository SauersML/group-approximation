---
rg: 2
id: minimal-crossing-wire-fixed-point-shift-is-quantum-rigid
kind: claim
title: The Durand–Romashchenko minimal self-simulating tile set, rebuilt with complete crossing and with diversification slots for crossing windows, is a free minimal Z^2 SFT that is quantum rigid over every field
requires:
  - crossing-wire-fixed-point-tile-sets-are-quantum-rigid
artifacts:
  - research/artifacts/gq-bh-g2-fixedpoint-a-crossing-layout.md
distinct_from:
  crossing-wire-fixed-point-tile-sets-are-quantum-rigid: that proves rigidity for a literal self-similar tile set, which has fault patterns and need not be minimal; this runs the same proof on the Durand–Romashchenko variable-zoom minimal construction, whose extra gadgets are classical.
  minimal-aperiodic-wang-shift-exists: that imports existence of a minimal aperiodic Wang shift; this constructs one that is in addition quantum rigid.
  durand-romashchenko-minimal-sft-simulation: that imports DR Theorem 7 (minimal simulation of effective shifts); this uses only their minimality mechanism (Section 3), with no simulated data.
---

**ESTABLISHED (2026-09-18)** through `minimal-crossing-wire-fixed-point-shift-is-quantum-rigid-proof`. Lane proof
(bh-g2-fixedpoint-a), **not independently reviewed; the rigidity step is with referee bh-ref-engines.** No
priority claimed.

## The construction

- **Source.** B. Durand, A. Romashchenko, arXiv:1802.01461 (ETDS 41, 2021). TeX source read at source
  (md5 `8e17f728…`), specifically:
  - §2.4, variable zoom `N_k = 3^(C^k)`: `τ_(k−1)` simulates `τ_k`, and each level's zone gets the rank `k`
    as input;
  - §3.1, properties (p1)–(p4);
  - §3.2, "Enforcing minimality" (diversification slots).
- **The tile sets.** `τ_0, τ_1, …` are their tile sets, with empty payload, modified in three ways.
  - **(M1) Complete crossing.** Inside each macrotile, away from the margins and the zone, every input bit
    is fanned out into a row copy and a column copy, so that every two bit edges meet in a crossing tile
    (as in (L3) of `crossing-wire-fixed-point-tile-sets-are-quantum-rigid`).
  - **(M2) Slots for crossings.** (p3) (wires at gap > 2) is kept at the margins and along cables. Windows
    touching a crossing or fan-out tile get diversification slots of DR §3.2, one for each position and each
    locally valid filling, exactly as DR do for windows of the computation zone. These windows are
    2×2-determinate, since their bits enter and leave through the window boundary.
  - **(M3) Zone format.** The zone is the one-head time-space diagram of (L4), or a one-way CA (proof, A4). This is a "natural"
    representation, which DR use for (p2).
- **Existence.** The fixed-point argument of DR §2.3–2.4 is unaffected, since all new gadgets have
  `poly(log N_k)`-computable geometry and there is room by (p1). This step is recalled, not re-verified line
  by line.
- **Layout.** Written out in `research/artifacts/gq-bh-g2-fixedpoint-a-crossing-layout.md`: tiles, crossing box, zone encoding and
  `poly(log N_k)` checkability, including the slot roles.

## Theorem

Let `Ω` be the tiling shift of `τ_0`. Then:

1. **Free.** Every period of a tiling is divisible by every `N_1 ⋯ N_k` (DR §2).
2. **Minimal.** Every pattern occurring in some tiling occurs in every large square of every tiling. This is
   DR's argument (§3.2): skeleton windows recur at homologous positions, single-wire windows recur by (p4),
   and zone, crossing and fan-out windows sit in slots present in every macrotile of their rank.
3. **Quantum rigid.** Every face-local edge family commutes. So `Ω` is `D`-quantum rigid for every `D >= 1`
   over every field, and `LC(Ω, k) ⋊ Z^2` is finitely presented.

The proof that the slots stay classical: each slot's frame consists of skeleton tiles whose colours are
functions of their coordinates, and its inner edges follow from the frame by the zone and wire rules.

## Consequences

- **Gate G2(a).** This answers `free-minimal-z2-sft-is-quantum-rigid` (route
  `free-minimal-z2-rigid-sft-via-crossing-wire-tiles`).
- **Simple algebras.**
  - `LC(Ω, k) ⋊ Z^2` is finitely presented, central simple
    (`free-minimal-cantor-crossed-products-are-central-simple`) and infinite-dimensional.
  - Over a finite field it has faithful rank models (`free-minimal-crossed-products-are-simple-with-rank-models`).
    That is the input of `fp-simple-algebra-over-finite-field-with-rank-model`.
  - It is not exactly matricial (`matricial-aperiodic-sft-rings-are-not-quantum-rigid`).
- **Not yet transported to non-amenable Λ.**
  - The path-fold transfer to `F_n × Z` (`path-folds-of-rigid-expansive-z2-sfts-are-quantum-rigid`) needs a
    horizontally expansive fibre, and `Ω` is not claimed to be one.
  - Product stability gives rigid free SFTs on `Z^2 × Z^2`, but minimality of products is not automatic.

## Lesson for general BH

- **Minimality and rigidity do not compete** when the minimality mechanism is *classical*. DR's
  diversification slots are exhibitions fixed by their frames, so they add patterns but no operator
  freedom.
- **General principle.** A gadget whose edges are forced by coordinate-determined frames is invisible to
  quantum families. Any hierarchical design can then buy dynamical properties (minimality, and plausibly
  effective subactions by DR's letter delegation) at no rigidity cost, as long as every input pair
  co-locates and everything else is deterministic.
- **For Track A.** The amenable building block is done. What remains of E2 is transport to non-amenable
  `Λ`: an expansive direction for path-folds, or building the same crossing design directly over `Λ_0 × Z^2`.
