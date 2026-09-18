# Referee report (gq-referee-c): smart-induced-map-has-brick-local-height-3-renormalization

- **Nodes:**
  - `research/smart-induced-map-has-brick-local-height-3-renormalization.md`;
  - the route `bs13-in-3v-via-smart-renormalization`;
  - the artifact `gq-gq-nv-obstruct-smart-renormalization.md`.
  - All landed 9fadf5ac6 by lane `gq-nv-obstruct`.
- **Lens:** independent re-derivation from Callard–Salo arXiv:2208.00685v3, `distortion-1-smart.tex`
  (`prop:smart-moves` and the transition table), plus calibration.
- **Verdict: PASS.** Items (a)–(g) below all check:
  - (a) the renormalization identity `φU^3 = Uφ` on `A`;
  - (b) the four-case `φ`;
  - (c) the induction lemma;
  - (d) the density and continuity step, including the limiting configurations;
  - (e) brick-locality after transport;
  - (f) bijectivity of `φ`;
  - (g) the route to `BS(1,3) <= 3V`.
- **The gq-affq conflict** is settled by the author's retraction and its MSI pass (cba5854a6). I did not rerun
  it.

## 1. The machine, from the source

- Phase-2 states move: `b_2, p_2` move right, and `d_2, q_2` move left, to the phase-1 state of the same letter.
- Phase-1 states read `a`, write, and change state:
  - `b_1`: `0 -> 1, d_2`; `1 -> 1, q_2`; `2 -> 2, q_2`.
  - `d_1`: `0 -> 1, b_2`; `1 -> 1, p_2`; `2 -> 2, p_2`.
  - `p_1`: `0 -> 2, b_2`; `1 -> 0, b_2`; `2 -> 0, q_2`.
  - `q_1`: `0 -> 2, d_2`; `1 -> 0, d_2`; `2 -> 0, p_2`.
- Sub-move order, from the proof of `prop:smart-moves` and its mirrors:
  - `M_b(k+1)` is `M_b, M_d, M_p`;
  - `M_p(k+1)` is two steps, then `M_b, M_q, M_p`;
  - `M_d(k+1)` is `M_d, M_b, M_q`;
  - `M_q(k+1)` is two steps, then `M_d, M_p, M_q`.
- So last sub-moves are always `p` (in `b` and `p` parents) or `q` (in `d` and `q` parents), and `b`, `d` are
  never last.

## 2. A and φ

**Parents are read off boundary values.** For `M_b(k)` on `(s_+ 0^k s_*)`:
- `s_* = 0` gives parent `b`, index 0;
- `s_* ≠ 0` and `s_+ = 2` gives parent `p`, index 0;
- `s_* ≠ 0` and `s_+ = 1` gives parent `d`, index 1.

For `M_p(k)` on `(s_* 0^k s_+)`:
- `s_* = 0` gives parent `p`, index 2;
- `s_* ≠ 0` and `s_+ = 1` gives parent `b`, index 2;
- `s_* ≠ 0` and `s_+ = 2` gives parent `q`, index 1.

`d` and `q` are the mirrors. So every move has a unique parent, whose extra cell may take any value, and every
point of `Y` has an infinite chain.

**Description of A.** `A` is `b_2` on a nonzero cell whose right neighbour is `0`, or `b_2` on a `2` whose right
neighbour is nonzero, plus the mirrors for `d_2`. There are no `p_2` or `q_2` points. This agrees with the node's
table, and `A` is clopen at radius 1.

**The four cases of φ.** I checked each against the recursions: the first `Y`-point of `M_x(1)` goes to the start
of `M_x(0)`.
- **`p` case.** `M_p(1)` begins `p_2 ▶`, then `p_1` reads `0`, writes `2` and goes to `b_2`. So the first
  `Y`-point is `b_2` on the written `2`. Deleting that cell, moving the head left and setting the state to `p_2`
  gives the start of `M_p(0)` on `(s_*, s_+)`.
- **`b` and `d` cases.** A zero deletion next to the head.
- **`q` case.** The mirror of `p`.

**Check of the lemma at K = 2 (`b` type).** I verified all three level-1 sub-move starts by hand:
- `ρ = 0`: `b_2` on `s_+`, tape `s_+ 0 0 s_*`;
- `ρ = 1`: `d_2` on the `1`, tape `s_+ 0 1 s_*`;
- `ρ = 2`: `b_2` on the written `2`, tape `s_+ 2 1 s_*`.

Under `φ` they go to the three level-0 sub-move starts of `M_b(1)`: `b_2` on `s_+`, `d_2` on the `1`, and `p_2` on
`s_+`, each over the tape `s_+ · s_*`. ✓

## 3. The induction lemma (§2 of the artifact)

- The extra cell of a sub-move in its parent never changes:
  - it is the parent's `s_*` on the right for `b`, and on the left for `p`;
  - `prop:smart-moves` says `s_*` is visited only at the last step (for `b`) or the first step (for `p`).
- The boundary map `β` checks out:
  - for `b`: `(s_+, 0)`, `(1, s_+)`, `(1, s_+)`;
  - for `p`: `(2, s_+)`, `(2, s_+)`, `(s_+, 0)`.
  - It does not depend on the level.
- `φ` reads only the state, the head cell and one neighbour. At every first `Y`-point of a level-1 move, these
  lie inside that move's 3-cell region, hence inside the sub-domain. So the case choice is the same at level `K`
  and at level `K-1`. ✓
- `Y`-membership during a move's run depends only on the move's domain:
  - every `p_2` there sits at the left end of a sub-domain and reads its right neighbour inside;
  - every `q_2` sits at the right end and reads its left neighbour inside.
  - So the count of `3^k` `Y`-points per level-`k` move (`smart-induced-on-genuine-moves-has-exact-tripling`)
    applies inside any context `[L] … [R]`. ✓

## 4. Density, continuity and limiting configurations

- **Where the identity can fail.** Case (1) fails exactly on all-`p` or all-`q` chains.
- **Shape of an all-`p` chain.** Every ancestor is a `p` inside a `p` parent, so every `s_*` is `0`. The domains
  grow leftward, the whole left tape is `0`, and all levels share the right cell `v ∈ {1,2}`.
- **The perturbation.** Set the far-left cell of the level-`N` ancestor to `1`. That ancestor is still `M_p(N)`:
  - its `s_*` is visited only at the first step;
  - `β(p, ·)` does not depend on `s_*`.

  So the lower chain and the window are unchanged. The new parent is `q` (index 1) if `v = 2`, or `b` (index 2)
  if `v = 1`, and `b` is never last. So case (1) holds for the perturbed point. ✓
- **Continuity.** `U` is continuous, because the return time is at most 6 (tripling node, item 1). `φ` is
  brick-local, hence continuous. Two continuous maps that agree on a dense subset of `A` agree on all of `A`. ✓
- **The limiting configurations need no separate treatment.** These are the all-`p`/all-`q` points, whose
  ancestors all end at once. The continuity argument covers them.

## 5. Brick-locality after transport

- **The encoding.** Coordinate 1 is `P(state, c_0) D(c_1) …` and coordinate 2 is `D(c_(-1)) …`, with complete
  prefix codes.
- **The four cases as prefix replacements:**
  - `b`: `P(b_2,c_0) D(0) -> P(b_2,c_0)` in coordinate 1;
  - `d`: `D(0) -> ε` in coordinate 2;
  - `p`: `P(b_2,2) D(c_1) -> P(p_2,c_(-1)) D(c_1)` in coordinate 1 and `D(c_(-1)) -> ε` in coordinate 2, split by
    `c_(±1)`;
  - `q`: `P(d_2,2) D(c_1) -> P(q_2,c_1)` in coordinate 1, split by `c_(-1) ≠ 0`.
- **Transport.** `ψ : e(Y) -> C^2` is brick-local: a finite union of bricks is brick-locally homeomorphic to
  `C^2`. Composites of brick-local maps are brick-local. So `(ψA, ψφψ^(-1))` satisfies items 1–3 of
  `renormalizable-thompson-elements-give-baumslag-solitar` for `U' = ψUψ^(-1) ∈ 2V`. ✓
- **This was the disputed point, and gq-nv-obstruct is right.** A deletion next to the head is a prefix
  replacement in this encoding, just like a head move of `F`.

## 6. Bijectivity

- The inverse is chosen by state: `b_2`, `d_2`, `p_2`, `q_2` images come from cases `b`, `d`, `p`, `q`.
- It inserts `0` (cases `b`, `d`) or `2` (cases `p`, `q`), and every preimage lies in `A` by the parent table:
  - `b_2` on `s_+` with right neighbour `0`: index 0 of `b`;
  - `b_2` on `2` with right neighbour `s_+ ≠ 0`: index 0 of `p`.
- So `φ : A -> Y` is a brick-local homeomorphism. ✓

## 7. The route to BS(1,3)

- With §5 and my PASS of the criterion (`gq-referee-c-renormalizable-thompson-elements-give-baumslag-solitar.md`),
  `k = 2`, `m = 3` gives `BS(1,3) ≅ ⟨U' × id, u⟩ <= 3V`, with `|s^(3^n)| = O(n)`.
- Infinite order of `U'` is automatic (criterion report, §3).
- **Not checked here: priority.** The node notes that Sheng arXiv:2209.11982 v1 claimed Baumslag–Solitar
  exclusions for `nV` and v2 withdrew them. A literature check (`gq-lit-arxiv`) on `BS(1,n) ≤ nV` should precede
  any novelty claim.
