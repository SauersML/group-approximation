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
(bh-g2-fixedpoint-a). **One adversarial referee PASS (bh-free-35, 2026-09-18), conditional on the layout facts listed in its Referee section; the rigidity step is also with referee bh-ref-engines.** No
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

## Referee (bh-free-35, 2026-09-18, adversarial): PASS, conditional

I checked the proof node against the base proof (`crossing-wire-fixed-point-tile-sets-are-quantum-rigid-proof`, Steps
1–5, which I re-derived independently and agree with bh-ref-engines' PASS on) and against my own obstructions. DR's
TeX source was not re-read; items R1–R3 are the conditions.

**1. Consistency with my theorems (the coordinator's question).** There is no conflict.
- `sfts-without-two-sided-faults-are-quantum-rigid` is sufficient only. Its trichotomy leaves rigid shifts with
  two-sided faults possible (zone (c)).
- `no-two-sided-fault-sfts-have-rich-strips-in-all-directions` constrains only shifts without two-sided faults. The
  fault analysis in 2 suggests (argued, not proved) that this shift is one: every rational line has both sides
  determining, hence is expansive.
  Then its strip automata are injective and its strips are aperiodic, non-sofic and of quadratic complexity, all
  consistent with the hierarchy.
- The only casualty is my heuristic lesson on that node ("irreversible arrow across every rational line"; "must run
  inside a Ledrappier-type rule"). It is corrected there. The theorem requires irreversibility only at
  non-expansive lines.

**2. Kill attempts, none of which succeed (arguments at the level of the layout, not formal proofs).**
- *Thin walls / information-free columns* (`self-similar-sft-thin-walls-refute-quantum-rigidity`, level by level for
  variable zoom). Margin columns depend on one side colour. The `~_i`-refutation then needs a vertical edge line
  with two completions on each side, and there is none, as the next item shows.
- *Faults.* Side-locality forces the corner position `S(t)_(0,0)` to be constant, so the corner maps are constant
  and each quadrant at a double fault is unique. At an infinite vertical fault, the level-`K` margins along the
  fault depend only on the fault's edge data, and cover the plane as `K` grows. So both half-planes are functions of
  the fault edge line, and no edge wall or wall arises there.
- *Horizontal-fault chains.* Fault data differing in one bit cascade down one chain of middle blocks. The
  differences stay connected along differing edges: the wire of the bit, the zones it feeds, and its crossing of the
  fault row. So there is no edge wall (item 4 of `fixed-point-wang-tile-rigidity-is-edge-family-commutation`).
- *Opposite-quadrant pairs* (NE and SW changed, NW and SE fixed): excluded, since quadrants are unique.

**3. Slots are frame-forced scalars in every FLEF (A2–A3): verified.**
- `C` from the non-slot faces commutes with every edge of every non-slot face. For a frame face, `C_p` lies in the
  algebra of its real-coordinate edges, and those commute with its slot-facing edge by (F1).
- The outer edges are the unique skeleton tile's colours for each phase. So `P_c(outer) = Σ_p C_p ε_p(c)` holds as an
  operator identity.
- The inner edges follow from the outer ones by face rules alone: `v_b` from the bottoms of BL and BR by the
  head-move rule, then `h_l` and `h_r`, then `v_t`. For wire, crossing and fan-out windows they are wire copies.
- There is no circularity: the face-rule derivations are operator identities on all of `W`. So the inner edges lie
  in the algebra of `C` and are scalars on each summand.
- This holds at every level, since at level `k` the slot tiles are rank-`k` tiles whose own simulation is ordinary.

**Conditions (not verified at source here).**
- **R1.** The fixed point exists with (M1)–(M3) added to DR's minimal layout. This is recalled, as for the base,
  where bh-ref-engines notes that DRS assume non-crossing wires.
- **R2.** DR's minimal layout keeps (L1) side-local margins with constant corners at every level. In particular:
  - slots, encoding zones and the (p4) role pattern stay out of the margins;
  - margin content is a function of one side colour.
  Steps 4–5 and the fault analysis above depend on this.
- **R3.** Each frame tile is unique for its real coordinate, and each slot's window is read in the head-move
  direction of (L4). This is standard, but it should be written into the layout table.

Recommended, as for the base: publish the coordinate→role table, with slot positions and frame colours.

### Referee addendum (bh-free-35, 2026-09-18): R1–R3 checked at source; the PASS stands, with one layout fix

**Sources.** Both were fetched fresh from arXiv on MSI (`gqsrc/bh-free-35/`).
- DR arXiv:1802.01461, `arxiv-4.tex`, md5 `8e17f728…`, the same file bh-g2-fixedpoint-a cites.
- DRS arXiv:0910.2415, `fpt-arxiv.tex`, md5 `63ad72b6…`.

The explicit layout is `research/artifacts/gq-bh-g2-fixedpoint-a-crossing-layout.md` (1e9e4c5b4).

**R1 (the fixed point survives the gadgets): holds.**
- DRS §2.3 needs only that the zone program checks "simple things only … polynomial in the input size, which is
  `O(log N)`". That is: consistent coordinates, wire and tableau rules, program bits.
- DR §2.2 adds that the "role" of `(i,j)` must be computable in `poly(log N)`. DR add their own slots and (p1)–(p4)
  "with only a minor modification" of exactly this kind.
- The layout's role map `ρ_N` compares `(i,j)` with `O(log N)` arithmetic expressions. CROSS, FAN, END and the
  (L4) zone tiles are finite tables, and the slot frames are coordinate-fixed roles. So the Kleene closure goes
  through unchanged, in DR's variable-zoom form too.
- Of the DRS assumptions, "wires do not cross each other" and the 3×2-window zone footnote are replaced. Neither
  is used by the fixed-point step.

**R2 (side-local margins with constant corners at every level): holds.**
- DRS and DR at source: macro-colours sit on "`k` bits in the middle of macro-tile sides … All other bits on the
  sides are zeros", and wires carry them inward.
- The layout runs each wire perpendicularly for `m` cells, keeps other wires' private lines outside the margins,
  and makes the corners BLANK.
- DR place slots "far away from the computation zone and from all communication wires", in the free stripe above
  the zone.
- The rank field and the (p4) role pattern are coordinate- and level-fixed fields of the zone or of the colour
  bits, not margin content.
- So at level `k` the margin (`m` rank-`(k−1)` tiles) depends on one side colour, and the corners are constant.

**R3 (frame tiles unique per coordinate; slot windows forced): holds.**
- DR: "We define the neighbors around each diversification slot in such a way that only one specific
  (2×2)-pattern can patch it". Slots are "detached from each other in space", and their positions are computable
  in `poly(log N)`. So each frame cell has a single tile.
- **Needed beyond DR.** DR guarantee only classical 2×2-determinacy (p2). The operator argument A3 needs *directed*
  determinism:
  - the `→` part of a vertical edge is a function of the left cell's bottom;
  - the `←` part is a function of the right cell's bottom;
  - the top is a function of the other three edges.

  The layout's zone table (§3, tiles (a)–(f)) supplies exactly this, and I checked each row.
- Given scalar outer edges, the allowed values of each inner edge from its two faces intersect in a single value,
  so the inner edges are forced scalars.

**Layout fix required (crossing box, §2).**
- With `c_q = X_0 + 2q`, the END column `X_0 + 2K` equals `c_K`. So the cell `(c_K, r_q)`, for `q < K`, is assigned
  both CROSS and END, and `(c_K, r_K)` is both FAN and END.
- Fix: widen the box to `[X_0, X_0 + 2K + 1]` and put END at `X_0 + 2K + 1`, with H in between. Then every pair
  still meets exactly once.
- **Minimality check of the fixed box.** Every 2×2 window that touches two wires contains a CROSS or FAN cell,
  because row and column copies are 2 apart and meet only at CROSS/FAN. So (M2) slots cover them, and DR's Case 2
  covers the rest.

**Verdict:** PASS, with R1–R3 discharged at source, conditional only on the box fix, which I posted to
bh-g2-fixedpoint-a.
