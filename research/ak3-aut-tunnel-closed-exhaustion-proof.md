---
rg: 2
id: ak3-aut-tunnel-closed-exhaustion-proof
kind: route
title: Computation of the tunnel-closed AK(3) component (capped BFS, full tunnel sweep of the capped component, growth from the new endpoints) plus Whitehead peak reduction for the path corollary
target: ak3-aut-tunnel-closed-exhaustion
requires: []
artifacts:
  - experiments/ak3-aut-tunnel-closure-2026-09-17/README.md
  - experiments/ak3-aut-tunnel-closure-2026-09-17/tunnel.c
  - experiments/ak3-aut-tunnel-closure-2026-09-17/grow.c
  - experiments/ak3-aut-tunnel-closure-2026-09-17/tbfs.c
  - experiments/ak3-aut-tunnel-closure-2026-09-17/sweep2.log
  - experiments/ak3-aut-tunnel-closure-2026-09-17/grow2.log
  - experiments/ak3-aut-tunnel-closure-2026-09-17/growcaps.log
  - experiments/ak3-aut-tunnel-closure-2026-09-17/tr2.log
  - experiments/ak3-aut-tunnel-closure-2026-09-17/tr3.log
---

States, moves, tunnels, T_C and S_C are as in the target. All tools share the move
generator, canonical form and goal test of
`experiments/ak3-thick-z-pair-search-2026-09-17/thzsearch.c` by `#include`.

## Step 1: S_24 in rank 2

`thzsearch 2 24 … dump` gives S_24: 261720 states, EXHAUSTED. The Neuwirth and primitivity
tests found no goal on it (`ak3-rank2-caps14-24.log` of the earlier search). The dump is
reproduced by the same command.

## Step 2: one tunnel step from all of S_24

`sweep.sh 2 s24r2.txt 261720 40000` runs `tunnel 2 24 0` on seven chunks, each exit 0
(`sweep2.log`). For every state and every (M1) product it records the following:

- **Capped products.** 19,260,026 products of length at most 24. Each one is looked up
  in S_24, and 0 are missing, so S_24 is closed under capped (M1).
- **Tunnels.** 532,381,654 products above the cap, each Whitehead-reduced. The reduction
  uses the cut formula |φ(w)| − |w| = cap(A) − deg(a) on the Whitehead graph, checked
  against direct application at every step. 0 endpoints have an entry of length 1.
- **New endpoints.** 16383 tunnels end within the cap outside S_24. They give 2194
  distinct pairs and 649 canonical classes (`canon.c`).

## Step 3: growth to closure

`grow 2 24 s24r2.txt newcanon.txt out` loads S_24 as known and inserts the 649 classes.
It then runs a BFS over new states only, with capped (M2), capped (M1) and tunnels. Every
new state gets the full goal test: `is_primitive` on each entry, and `thick2` on the pair.

The run ends EXHAUSTED (`grow2.log`):
- 922 new states;
- 2,221,463 tunnels, of which 0 are PRIM;
- goals PRIM 0 and THICK 0, with 922 Neuwirth tests and 0 undecided.

S_24 is closed under capped moves (Steps 1–2) and its tunnels land in the seeds. The new
states are closed under all three move types. So T_24 = S_24 ∪ new, with 262642 states.

**Cross-check.** `grow` from AK(3) alone reproduces `tbfs`, an independent BFS loop: at
caps 20, 21 and 22 in rank 2 both give 6955, 23515 and 41531 states. At cap 22 both give
75,833,783 tunnels (`growcaps.log`, `tr2.log`). `tbfs … notun` also reproduces the
capped count 6875 of `thzsearch` at cap 20 in rank 3.

## Step 4: smaller caps and rank 3

- Rank 2, caps 13–22: `tbfs` and `grow` from scratch (`tr2.log`, `growcaps.log`).
- Rank 3, caps 13–21: `tbfs` (`tr3.log`).

All runs are EXHAUSTED with no goal and no PRIM tunnel endpoint.

## Step 5: the path corollary

**Cited.** Peak reduction for tuples of cyclic words (Higgins–Lyndon; Lyndon–Schupp,
*Combinatorial Group Theory*, Ch. I, Prop. 4.20).

Let W be a tuple of cyclic words in F_n and φ ∈ Aut(F_n). Then φ factors into Whitehead
automorphisms σ_k ⋯ σ_1 with no peak. So every intermediate tuple σ_i ⋯ σ_1(W) has length
at most max(|W|, |φ(W)|).

In `thzsearch.c`, the type-1 Whitehead automorphisms (permutations and inversions of
generators) are absorbed in the canonical form. The type-2 ones are the (M2) moves, all of
them, and the set is closed under inverses. Hence:

**(A)** If a state s and an automorphic image φ(s) both have length at most C, then φ(s) is
reached from s by capped (M2) moves.

**(B)** Take an excursion e: s_0 → s_1 → ⋯ → s_{k+1}, with |s_0|, |s_{k+1}| ≤ 24 and
|s_i| > 24 for 1 ≤ i ≤ k.

- *Suppose e is one (M1) move s_0 → s_1 followed by automorphisms.* The tunnel from s_0 on
  that product computes a Whitehead-minimal m with m = ψ(s_1) for some ψ. Since
  s_{k+1} = ψ′(s_1), m is Aut-equivalent to s_{k+1}, and |m| ≤ |s_{k+1}| ≤ 24 by minimality.
  So the tunnel lands on m, and m ∈ T_24 when s_0 ∈ T_24. By (A), s_{k+1} is reached from m
  by capped (M2) moves, so s_{k+1} ∈ T_24.
- *Suppose e is automorphisms only.* Then s_{k+1} is an automorphic image of s_0, and (A)
  gives s_{k+1} ∈ T_24.

The (M1) moves and the tunnels are applied to the canonical representative. The move set
is equivariant under the symmetries that define states, since it uses all rotations, both
entries and both signs. So nothing depends on the representative.

Now take a path from AK(3) to (x, y). Suppose every excursion is of one of the two kinds
in (B). Every move below the cap is a capped (M1) move or, by (A), a composite of capped
(M2) moves. By induction along the path, every state of length at most 24 on it lies in
T_24. The endpoint (x, y) has an entry of length 1 and is PRIM, but T_24 contains no PRIM
state. This is a contradiction, so the corollary holds. ∎

## What is not covered

- An (M1) move multiplies by a conjugate g v^{±1} g⁻¹ with g of length at most one, at a
  rotation. A general AC product u · w v^{±1} w⁻¹ with longer w is not a single (M1) move.
  The corollary is about paths of (M1) moves and automorphisms.
- Tunnel endpoints above the cap are tested only for an entry of length 1, which is weaker
  than primitivity. The corollary does not use this test.
