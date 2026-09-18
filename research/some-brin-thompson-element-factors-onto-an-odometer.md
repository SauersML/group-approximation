---
rg: 2
id: some-brin-thompson-element-factors-onto-an-odometer
kind: claim
title: For some k and m >= 2, some element of the Brin-Thompson group kV has the m-adic odometer as a topological factor
distinct_from:
  renormalizable-thompson-elements-are-odometer-codes: that proves every renormalizable element has such a factor; this asks whether any element of any kV has one at all.
  bs12-embeds-in-brin-thompson-2v: that asks for BS(1,2) in some nV; a negative answer here kills only the renormalization route to it, and a positive one does not give BS(1,2).
  three-v-contains-aperiodic-rationals: that uses a periodic-point-free SMART element of 2V; this asks whether some such element has continuous eigenvalues of unbounded order.
---

**OPEN.** There are `k >= 1`, `m >= 2`, `T ∈ kV` and a continuous surjection
`π: C^k -> Z_m` with `π ∘ T = π + 1`. Equivalently, for every `j` the space
`C^k` is split into `m^j` clopen sets that `T` permutes cyclically.

**Why it is a hole.** `renormalizable-thompson-elements-are-odometer-codes` proves
this is necessary for the renormalization route
(`renormalizable-thompson-elements-give-baumslag-solitar`) to
`bs12-embeds-in-brin-thompson-2v`. So a negative answer kills that route for
every `k` and `m`.

**Known constraints on a witness.**
- `T` has no periodic points, since `m^j` divides every period.
- This excludes the topological full group of the full shift, whose elements fix
  the constant configurations.
- Candidates must be periodic-point-free, such as SMART-type machines in `2V`
  (`three-v-contains-aperiodic-rationals`).

**Lead.** In Callard--Salo (arXiv:2208.00685v3) the level moves of SMART take
`f(k+1) = 3 f(k) + 4` steps. A SMART-type machine with exact tripling
`f(k+1) = 3 f(k)` is the natural candidate both for this claim and for a height-3
renormalization. Whether SMART itself has continuous eigenvalues was not
checked.

## Attempts

- 2026-09-17 (lane gq-nv-obstruct). **Not decided.** Four results and one tool.
  - *Necessary conditions*, `odometer-factor-witnesses-mix-coordinates` (ESTABLISHED). Every power of a
    witness is periodic-point-free, because `Z_m` is torsion-free. So no power lies in any `kV`-conjugate
    or coordinate-permutation image of the triangular subgroup `T_k`: triangular elements always have
    periodic points. In particular `k = 1` is impossible (`T_1 = V`), and a witness must mix
    coordinates.
  - *One-way machines die.* Suppose the head only ever moves one way along a coordinate, as in a
    Turing machine `τ ∘ β` that moves right at every step. Then the cells it leaves behind are frozen.
    On a constant input, its bounded active window runs through a finite automaton, so the window's
    period is bounded independently of the scale `j`. But `π mod m^j` must read the time `n mod m^j`
    from a window of bounded radius. That is a contradiction for large `j`. By the same argument, one
    coordinate alone cannot count: a deterministic pushdown run on unary input has an ultimately
    periodic top window. So the counting must use at least two coordinates as two-way memory, as in a
    Turing machine. This is a lane argument, not written as a node.
  - *Tool*, `brin-thompson-first-return-maps-lie-in-kv` (ESTABLISHED). The first-return map of an
    element of `kV` to a clopen set with bounded return times is, up to a brick-local conjugacy, again
    an element of `kV`. So SMART's per-level overhead can be deleted by inducing, provided the overhead
    configurations form a clopen set with bounded runs and removing them leaves the level moves exactly
    tripled. The candidate is then an element of `2V` with `f(k+1) = 3 f(k)` exactly.
  - *SMART itself.* SMART's moving-tape map `F ∈ 2V` is minimal and periodic-point-free, and its
    column shift is substitutive (Cassaigne–Ollinger–Torres-Avilés). The substitution was not
    obtained: the HAL and publisher pages refused access. Heuristic, not a proof: if the level lengths
    are `3^n c_a − 2` with the constant from `f(k+1) = 3f(k)+4`, Host's eigenvalue criterion is
    violated for `e^{2πi/3^j}` unless a coboundary absorbs the `−2`. So the exactly tripled induced map
    is the better candidate.
  - *Next step.* Read SMART's substitution from the arXiv e-print source of Callard–Salo
    2208.00685v3 (`distortion-1-smart.tex`, which lane e-nv-walls already read for the transition
    table). Then test whether the "turn" steps are locally recognizable. Inducing on their complement
    gives a constant-length-3 substitution in the column shift. By Dekking's theorem, a primitive
    aperiodic constant-length-3 substitution has `Z_3` in its maximal equicontinuous factor, and that
    would answer this claim YES.

- 2026-09-17 (lane gq-affq). **Not decided. The exact-tripling target is already met by SMART after recounting.**
  - *Table.* This entry uses the transcription in
    `experiments/nv-measured-walls-2026-09-17/smart_belt_periods.py` (checked reversible there). Its states
    are `(shape, dir, phase)`, with shape `F` or `H`, dir `±`, phase 1 or 2. Phase 2 moves by dir and enters
    phase 1. Phase 1 reads, writes and enters phase 2:
    - `(F,±)`: on `0` it writes `1` and goes to `(F,∓)`; on `1` or `2` it keeps the symbol and goes to
      `(H,∓)`;
    - `(H,±)`: on `0` it writes `2` and goes to `(F,±)`; on `1` it writes `0` and goes to `(F,±)`; on `2`
      it writes `0` and goes to `(H,∓)`.
  - *Recursion, checked by hand.* Crossing `s+ 0^(k+1) s*` from `(F,+,2)` on `s+` runs, in order:
    - `M▶(k)`, taking the last zero as `s*`;
    - one step: `(F,+,1)` reads that zero and writes `1`;
    - `M◀(k)` back to `s+`;
    - one step: `(F,-,1)` reads `s+`;
    - `M⊳(k)`, taking the new `1` as right delimiter;
    - one step: `(H,+,1)` rewrites that `1` as `0`;
    - one step: the move onto `s*`.

    So `f(k+1) = 3 f(k) + 4`. The case `k = 1` takes 7 steps, and the tape is restored.
  - *No defect after shifting.* Put `g(k) = f(k) + 2 = 3^(k+1)`. Then `g(k+1) = 3 g(k)` exactly.
    - Counting a crossing together with two joint steps already gives exact tripling. So "a variant with
      `f(k+1) = 3 f(k)`" is a matter of accounting, not a new machine.
    - The blocks of `g(k)` consecutive fine steps inside a level-`(k+1)` unit do not align with the
      three sub-crossings. The second block ends one step into the third sub-crossing.
    - In macro steps (read plus move) the crossing time is `c(k) = 3(3^k - 1)/2`. It satisfies
      `c(k+1) = 3(c(k) + 1)`, and `c(k) ≡ 0 mod 3` for every `k`. So crossing times give no obstruction to
      a continuous eigenvalue `e^{2πi/3}`: every crossing has the same residue.
  - *What a height-3 renormalization would still need (heuristic, not a proof).* By item 3(c) of
    `renormalizable-thompson-elements-are-odometer-codes`, `T^3 e_0 = e_0 T`. So a configuration and its
    coarsening must differ within a bounded window of the head at all times. For SMART that window must
    carry "one extra zero in the block being crossed", together with a local phase shift of one step at
    each joint.
    - Zeros are interchangeable, so inside a zero block the extra zero costs nothing.
    - SMART never shifts nonzero cells. So once the head leaves the block for good, the extra zero is
      stranded far behind the head, unless the hierarchy always brings the head back to that block.
    - Deciding this needs SMART's global substitution. That is the plan of lane gq-nv-obstruct above,
      which reads it from the e-print source. Coarsening that deletes a zero next to the head is the
      candidate `e_0^{-1}` to test there.
- 2026-09-17 (lane gq-nv-obstruct, second pass). **YES claimed, under review.** This pass used the
  Callard–Salo e-print source. `smart-level-zero-return-map-factors-onto-3-adic-odometer` (OPEN until
  gq-referee-a and gq-referee-b PASS) and route `odometer-factor-via-smart-level-zero-return-map`.
  - SMART's moves nest by the constant-length-3 substitution `b→bdp, d→dbq, p→bqp, q→dpq`, plus 2 special
    configurations per move. Those give `f(k+1) = 3f(k)+4`.
  - The level-0 configurations form a clopen set `Y`, and inducing on `Y` makes every level-`k` move exactly
    `2·3^k` long.
  - The position within the level-`k` move is read off `k+2` cells, via the two unmodified cells of
    `fig:bottom-up-analysis-smart`. So `F_Y` factors onto `Z/2 × Z_3`, and by
    `brin-thompson-first-return-maps-lie-in-kv` it is conjugate to an element of `2V`.
  - Proof: `research/artifacts/gq-gq-nv-obstruct-smart-odometer.md`.
