---
rg: 2
id: smart-level-zero-return-map-factors-onto-3-adic-odometer-proof
kind: route
title: SMART's moves nest by a constant-length-3 substitution with locally readable parents, so the induced level-0 map has a local 3-adic phase
target: smart-level-zero-return-map-factors-onto-3-adic-odometer
requires:
  - brin-thompson-first-return-maps-lie-in-kv
artifacts:
  - research/artifacts/gq-gq-nv-obstruct-smart-odometer.md
  - research/artifacts/gq-gq-nv-obstruct-smart-simulation.md
---

Lane gq-nv-obstruct. Reviewed PASS by gq-referee-a (6000c8af8) and gq-referee-b (628a5c79d).

**Imported, verbatim.** Callard–Salo, arXiv:2208.00685v3, `distortion-1-smart.tex`. The inputs are the
8-state transition table (l. 2–35) and Proposition `prop:smart-moves` (l. 52–97), with its proof giving
the recursions (l. 100–212). The source says the moves apply to "finite subpatterns of a finite cyclic
tape, or of an infinite configuration" (l. 50). The table and the four sub-move sequences
`b→bdp, d→dbq, p→bqp, q→dpq` are quoted in the artifact, §1.

**Steps.** They are written out in `research/artifacts/gq-gq-nv-obstruct-smart-odometer.md`.
1. *Case table* (§2). A level-`k` move's parent type and sub-move index are read from its own `s_+`
   and `s_*` cells, which the move never modifies. The table partitions `{1,2} × {0,1,2}`. On Z-tapes the
   parent's extra cell always exists, and the parent's `s_+` lies in `{1,2}`. So every level-0
   configuration lies in a unique chain of genuine moves of every level.
2. *Counting* (§3). Special configurations have a `0` where each of the eight radius-1 `Y`-patterns needs
   a nonzero cell, so they are never in `Y`. Hence `L(k) = 2·3^k`.
3. *Local phase and equivariance* (§3). `pos_k(y)` is a function of the cells within distance `k+1` of
   the head. `pos_k(F_Y y) ≡ pos_k(y) + 1 mod 2·3^k`. At a move boundary this uses only that the next
   level-`k` move does not contain `y`, which follows from uniqueness of the chain.
4. *Bounded returns, proved directly (no minimality needed).*
   - In a finite chain, specials are the last two configurations of `b/d` moves and the first two of
     `p/q` moves. No `b/d` move is a last sub-move, and no `p/q` move is a first sub-move. So at most 4
     specials are consecutive.
   - Every configuration of infinite level enters `Y` within 5 steps. For `b_2` on a `0` with zeros to the
     left: `b_1` next, then either `0|1 → d_2` on a nonzero cell, or `c|c → q_2`, `q_1` on `0`,
     `0|2 → d_2` on a nonzero cell. The cases `b_1`, `p_2`, `p_1` are checked the same way, via
     `0|2 → b_2` on a nonzero cell, and `d`, `q` follow by mirror symmetry.
   - Hence every return time is at most 10. The MSI runs show at most 6 for gq-affq's one-per-move `Y`.
5. *Into 2V.*
   - `X = Γ^Z × Q` with `|Q| = 8`. Code a configuration `(…c_{-1}[q,c_0]c_1…)` as a point of `C^2`:
     - the first coordinate is `P(q,c_0) D(c_1) D(c_2) ⋯`;
     - the second is `D(c_{-1}) D(c_{-2}) ⋯`;
     - `P` is a complete binary prefix code of size 24, and `D = {0, 10, 11}`.
   - A symbol transition is the prefix replacement `P(q,a) → P(q',b)`.
   - A right move is `P(q,c_0)D(c_1) → P(q',c_1)` in the first coordinate and `ε → D(c_0)` in the second.
     Left moves are symmetric.
   - So `F` is conjugate to some `T ∈ 2V`, and `Y` is clopen.
   - `brin-thompson-first-return-maps-lie-in-kv` gives `U = ψ T_Y ψ^-1 ∈ 2V`, which factors onto
     `Z/2 × Z_3 → Z_3`. ∎
