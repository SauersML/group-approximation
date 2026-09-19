---
rg: 2
id: rope-readers-cannot-be-deterministic-and-must-couple-chains
kind: claim
title: No deterministic extension of the scaling seed marks a rope set that is not residue-periodic, co-deterministic readers maximize the freedom at infinity instead of removing it, and the uncoupled numeral reader is not quantum rigid; a rigid rope reader must couple its descent chains
distinct_from:
  modular-machine-scaling-seed-reads-regular-numerals: that builds the reader and leaves gate (RR) open with two proposed fixes; this refutes fix (b), shows the reader as built is not rigid, and replaces (RR) by the coupling gate (RR′).
  extension-rigidity-is-base-centrality-plus-pointwise-rigidity: that is the general extension criterion; this applies its necessity half to one reader.
  deterministic-extensions-of-rigid-sfts-are-rigid: that transfers rigidity through determinism; this shows no deterministic extension can do the rope's job.
---
**ESTABLISHED** for parts 1–3 (lane proof, bh-invent-15, 2026-09-18; not reviewed). Part 4 is a
design with a sketch, and it is **OPEN**.
- This answers gate (RR) of the parent negatively for the reader as built, with only chain
  constraints. The parent claimed no rigidity, and its parts 1–3 stand.
- Notation as in the parent: `S_M`, its seed, coset origins, rows `β = 0`, and `l`-descent.
- A reader is an SFT extension `Y^+ → Y` whose forced point carries `v(x^α) = [α ∈ I]` on the
  sink row.
- `I ⊆ N` is **residue-periodic** if for some `K`, membership of every `α ≥ m^K` depends only
  on `α mod m^K`. Cohen's rope set (all base-`m` digits in `{1,…,2n}`, with `m − 1 > 2n`) is not.

## Theorem
1. **No deterministic reader.** Suppose the reader layer is a continuous equivariant function
   of the base configuration (a deterministic extension). Then `I` is residue-periodic.
2. **Co-determinism is the wrong property.**
   - On an unanchored descent chain, the reader constraints `q(h) = δ(q(hl), d(h))` admit one
     run for each state in `∩_k δ(Q, d_k ⋯ d_0)`.
   - Every chain has a unique run iff `𝒜` is **definite**: some `k` exists such that every
     length-`k` word sends `Q` to one state. Definiteness forces residue-periodicity (compare
     part 1).
   - A co-deterministic or reversible `𝒜` has injective letter maps. That gives exactly `|Q|`
     runs on every chain, the maximum possible.
   - So the proposed fix (b) cannot work for any rope set that is not residue-periodic, whatever
     the reading direction.
3. **The reader as built is not rigid.**
   - In the parent's `Y^+`, some boundary configuration carries two unanchored descent chains
     with all-good digit tails, and no rule links them.
   - By the lifting half of `extension-rigidity-is-base-centrality-plus-pointwise-rigidity`,
     noncommuting idempotents on the two chains give a noncommuting quantum family.
   - So `Y^+` is not `D`-quantum rigid for any `D`.
4. **The coupling gate (RR′).** Add the rules below, all true on the forced point:
   - (L) **block rule:** `q(hl) = q(h x^{a'−a} l)` for row elements in the same `m`-block;
   - (R) **scaling rule:** `q(hr) = δ(δ(q(hl), 0), 0)`.

   Sketch: in every boundary configuration, the free choices of all unanchored chains are then
   linked into one global bit. That bit is invariant under the bounded shifts, carries and digit
   shifts that relate the chains. **(RR′):** prove the linking, then verify base-centrality
   (C_D) for this one-bit extension. A free global bit is rigid on its own:
   `Y × {0^Λ, 1^Λ}` is rigid by product stability.

## Proof
**1.**
- **The factor has bounded radius.** A continuous equivariant map on a compact subshift is a
  sliding-block code of some radius `k` (Curtis–Hedlund–Lyndon). So `v(x^α)` is a function of the
  base labels on `x^α·Ball(k)`.
- **Those labels see only low digits.** Each `g = x^α w` with `|w| ≤ k` is reached by at most
  `k` moves, each a shift by a generator of `Z^2` or a scaling `α ↦ ⌊α/m⌋, mα, m^2α` together with
  a residue label. So the coset, position residue, marker sign and pointer of `g` are
  determined by the moves in `w` and by the digits of `α` at levels `≤ 2k`, provided
  `α ≥ m^{2k+2}` (then no position along the way reaches the origin region). This last step is
  a sketch.
- **So `I` is residue-periodic** with `K = 2k + 2`.
- **Cohen's `I` is not.** Take `α = 11⋯1` (base `m`, `K + 2` digits), which is in `I`. Changing
  its digit at level `K + 1` to `0` keeps `α mod m^K` and leaves `I`.

**2.**
- **Runs.** A run on a chain `…, h l^2, h l, h` is a sequence with
  `q(hl^j) = δ(q(hl^{j+1}), d_j)`. By compactness the set of states at `h` reachable by
  left-infinite runs is `∩_k δ(Q, d_{k-1}⋯d_0)`. It is one state for every stream iff some `k`
  works uniformly, again by compactness over `{0,…,m−1}^N`. That is definiteness.
- **Definiteness gives a factor.** A definite `𝒜` makes the anchored verdict depend only on the
  last `k` digits read, so `I` is residue-periodic.
- **Injective maps.** They make each image `δ(Q, w)` equal to `Q`, so every state is reachable.
- **Other directions.** Reading the other way, or the reversal, only changes which end of the
  chain carries the free state.

**3.**
- **The boundary configuration.** Take a limit of `g_N·y_*^+` with base points at `(α_N, 0)`,
  where `α_N` has all digits in `{1,…,2n}` and more and more of them. The chains through `(α_N, 0)`
  and `(α_N + 1, 0)` are unanchored in the limit and have all-good tails.
  - For Cohen's automaton, each such chain has exactly the runs `ok ≡` and `bad ≡` (parent,
    part 4).
  - In the parent's `Y^+` the reader rules act only along `l`, so no rule mentions both chains.
- **The noncommuting family.** Let `y` be the base configuration. Define a `y`-relative family:
  - `G_ok(u) = P` on chain 1 and `P'` on chain 2, with `P, P'` idempotents that do not commute;
  - `G_bad = 1 − G_ok` on both chains;
  - scalars at all forced sites.

  (Q1) and (Q2) hold. (Q3_y) holds, because the forbidden patterns inside one chain are
  `ok|bad` switches on all-good segments, and `P(1−P) = 0`. No pattern linking the two chains is
  forbidden.
- **Conclusion.** Lifting (item 2 of the criterion) gives a base-central family of `Y^+` that does
  not commute.

**4 (sketch).**
- (L) links the chains of one `m`-block through their common `l`-image position.
- Consecutive blocks are linked one level deeper by (L) in the child cosets. For all-good tails
  the carry stops, because `m − 1` is a bad digit. Chains with infinitely many bad digits have a
  unique run anyway.
- (R) links rows across `r`-edges.
- Bounded moves preserve "the digit tail is all good", so the linked components share one bit.
- What is not done: connectivity of the linking graph in every boundary configuration, and (C_D).

## Lesson for general BH
- **A reader of a non-periodic set cannot be a function of the seed.** A sliding-block factor
  sees only boundedly many digits. So rope readers must carry a genuine choice at infinity, and
  co-determinism maximizes that choice rather than removing it.
- **Why the obvious fix fails, and the better one.** Independent choices on different chains
  break quantum rigidity outright, by pointwise fibre rigidity. The right design links all
  chains through local rules that are true on the seed, so the freedom collapses to one global
  bit, which is rigidity-neutral in isolation.
- **For seed towers.** The machine's positions must be read by a coupled reader whose only
  freedom is a single bit at infinity.
