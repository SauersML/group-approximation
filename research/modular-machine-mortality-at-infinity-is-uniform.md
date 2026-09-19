---
rg: 2
id: modular-machine-mortality-at-infinity-is-uniform
kind: claim
title: A modular machine terminates on every m-adic configuration iff its running time on N² is uniformly bounded, and then its halting basin H_0(M) is finite; so in a relative seed for (K_M, T'_M) the rogue sheets run the m-adic machine, and halting marks are forced there only for machines with finite H_0
distinct_from:
  machine-subgroup-is-core-free-and-draws-the-machine: that shows the transported-bit candidate is not rigid once two unterminated components sit 2D apart; this shows unterminated components are unavoidable at infinity for every machine with infinite H_0, mortal or not.
  every-decidable-set-has-a-mortal-decider: that gives machines that halt from every configuration in N², which forces the marks on the genuine base sheet; this shows mortality on N² does not reach the rogue sheets, where configurations are m-adic.
---

**ESTABLISHED** for items 1, 2 and 4 given 3 (lane proof, bh-free-56, 2026-09-18; elementary; not reviewed). Item 3 is a lane sketch: its induction along runs is written out only for the fate-bit and residue rules of the cited candidate.

**Setting.** `M` is a modular machine with modulus `m` (Chiodo–Vyas, arXiv:1604.03788, §4.1). A
quadruple `(a, b, c, R)` sends `(um + a, vm + b)` to `(um² + c, v)`, and type L is symmetric. There is at
most one quadruple per residue pair, and a configuration is terminal when none applies.

The same formulas define the **m-adic machine** `M̂` on `Z_m²`, the pairs of `m`-adic integers.
- Its moves are injective.
- Its first `k` moves, and whether a run lasts `k` steps, depend only on residues mod `m^{2k+1}`.

## Statement

1. **Mortality at infinity.** Every run of `M̂` terminates iff the running time of `M` on `N²` is
   bounded by a constant `T`.
2. **Uniform mortality trivializes the basin.** If the running time on `N²` is at most `T`, then
   `|H_0(M)| ≤ (q + 1)^T`, where `q` is the number of quadruples.
3. **Rogue sheets are m-adic.** Take any relative seed for `(K_M, T'_M)` of mark type:
   - the sheet layers of `machine-subgroup-is-core-free-and-draws-the-machine` item 3;
   - a finite mark layer transported exactly along the move words `x^{a_i} y^{b_i} r_i x^{-c_i}`;
   - marks pinned at terminals.

   In a configuration without an origin, the successive sheets met along a run carry residue labels
   whose deeper digits are chosen freely, subject only to the `φ_i`-compatibility rules. So the runs of
   rogue sheets are exactly the runs of `M̂`.
4. **Consequence.** The marks are locally forced on every configuration iff `H_0(M)` is finite. For every
   machine with infinite `H_0`, some configuration of the seed space has an unterminated component. This
   includes the mortal deciders of `every-decidable-set-has-a-mortal-decider`. On that component the
   pinned rules leave both mark values admissible.

## Proof

1. For each `k`, let `U_k ⊆ Z_m²` be the set of points whose run lasts at least `k` moves.
   - `U_k` is clopen, since it depends on residues mod `m^{2k+1}`. The sets are nested.
   - `N²` is dense in `Z_m²`, and `M̂` restricts to `M` on `N²`. Here `α ≡ a (mod m)` and `α ≥ 0` give
     `u ≥ 0`, so the moves stay in `N²`.
   - *Bounded time ⇒ mortality.* If running time on `N²` is at most `T`, then `U_{T+1} ∩ N² = ∅`. So
     `U_{T+1} = ∅`, because it is open and `N²` is dense.
   - *Mortality ⇒ bounded time.* If the running time is unbounded, every `U_k` is nonempty. By
     compactness `⋂ U_k ≠ ∅`, which is an infinite run of `M̂`.
2. `p ∈ H_0` iff `μ_σ(p) = (0, 0)` for the quadruple sequence `σ` of its run, with `|σ| ≤ T`.
   - Each `μ_σ` is injective, so it has at most one preimage of `(0, 0)`.
   - There are at most `(q + 1)^T` sequences.
3. The fate-bit and residue rules along a move word relate only:
   - the residue class of `φ_i(z)` modulo a bounded power of `m`, to that of `z` modulo a bounded power;
   - the marks at the two ends.

   Following a run through the tree of sheets reached by `r`-edges, each new sheet is constrained only
   through these congruences. By induction along the run, the residue labels met are exactly the
   residues of an `m`-adic configuration and its `M̂`-run. Every `M̂`-run occurs this way, because
   locally consistent residue labels exist for every choice of digits.
4. If `H_0` is infinite, the running time on `N²` is unbounded, by the contrapositive of 2. So `M̂` has an
   infinite run by 1, and by 3 it is realized on a rogue sheet as an unterminated component. The pinned
   rules act only at terminals, so both mark values are admissible there.
   - Conversely, if `H_0` is finite, choose a machine with bounded running time for it. Then every
     component terminates and the marks are forced. `∎`

## What this says for the seed tower

**Where mortality helps, and where it does not.**
- Mortality on `N²` (`every-decidable-set-has-a-mortal-decider`) is what makes `H_0(M)` recursive. It
  forces the marks on the genuine base sheet, which is needed for isolation (S1).
- It does not reach the rogue sheets. There, configurations are `m`-adic, and termination is uniform
  mortality, which makes `H_0` finite.
- So "rogue runs also terminate" is false for every machine relevant to CAP.

**Consequence for exact transport with pinned endpoints.** With the atom and chain lemmas of
`relative-seeds-glue-graphs-of-groups-into-class-c` §2, exact transport plus pinned endpoints makes
each unterminated component carry one free projection. So rigidity needs one of two things:
- every two unterminated components of every configuration come within `2D`, so their projections must
  commute; or
- an additional coupling layer between components.

The first is a strong combinatorial condition on `M̂`, open. The second is the permutive space-time
layer of gate 4.

## Lesson for general BH

A machine that halts on every genuine input can still run forever at infinity. The rogue regions of a
seed see the machine's completion, here its `m`-adic extension. By compactness, termination there
means a uniform time bound, which leaves only finitely many accepted configurations. So an answer can be
pinned at the end of every run only for trivial machines.

A rigid seed that computes must control its unterminated computations at infinity by determinism in
several directions. Pinned endpoints are not enough. This is the point where CAP either breaks (if
permutive encodings of `M̂`-runs exist) or holds.
