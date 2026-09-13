---
rg: 2
id: atlas-literal-packet-cannot-authenticate-any-common-mode
kind: claim
title: No literal entry of the 4,648-entry Atlas packet authenticates a common right-hand-side mode
distinct_from:
  atlas-first-common-rhs-return-star-has-rank-two: that computes the single first common-RHS star x_12(ee); this censuses every right-hand-side occurrence met by any of the 4,648 packet entries.
  atlas-reverse-dictionary-does-not-close-ee-return: that appends the twelve reverse rows to the x_12(ee) star only; this appends every meeting literal row, including involutivity and reverse rows, to every star.
  mixed-steinberg-loops-admit-morita-rectangular-model: that constructs an exact Morita-rectangular model of pasted Steinberg loops; this is the complete literal occurrence census of the packet in the nuisance-quotient language of atlas-mixed-minor-needs-nuisance-quotient-rank.
artifacts:
  - experiments/atlas_packet_occurrence_rank_scan.py
  - research/artifacts/atlas-packet-occurrence-rank-scan-2026-09-13.md
---

**ESTABLISHED EXACT PACKET CENSUS (not independently reviewed).**  Reconstruct
the complete rank-five packet with `atlas-rank-five-complete-packet-exporter`
(ordered word-list SHA-256 `9e751115…6c2b99`) and linearize every entry in the
free rectangular language used by `atlas-mixed-minor-needs-nuisance-quotient-rank`:
place arbitrary finite-dimensional `F_2`-spaces at the five indices, let each
root be `x_kl(w)=1+N` with `N=iota_k w p_l` for an arbitrary rectangular
coefficient map `w`, use the packet convention `[x,y]=x y x^-1 y^-1`, and read
a reverse entry `g w_g^-1` blockwise as `g=w_g`.  Expanding each relator `=1`
gives one exact linear equation per matrix block among path monomials and
generator blocks.  Then:

1. **(LP1)** The 200 `root_*` and 2,980 `orth_*` entries project to zero.  The
   24 involutivity entries project to `2N` and vanish over `F_2`.
2. **(LP2)** Each of the 1,432 `st3_ijk_rs` entries projects to exactly one
   equation `P=R`: its composable path monomial equals its right-hand-side
   occurrence.  The twelve reverse entries project to 16 blockwise equations,
   each equating one generator block with one single-root occurrence.
3. **(LP3)** Every nonzero projected equation equates exactly two monomials.
   Hence the assignment that is constant on each connected component of the
   packet's incidence graph satisfies all 1,448 projected equations: **no
   literal packet entry pins any common mode**.
4. **(LP4)** Each of the 320 two-letter nonconstant right-hand-side occurrences
   meets exactly three packet rows, all `st3`, with quotient increment
   `rank[C D]-rank(D)=2` and surviving common mode.  In particular the
   literal packet never raises a two-letter common-RHS star above rank two.
5. **(LP5)** The 100 one-letter right-hand-side occurrences have increments
   `1` (20 stars), `4` (48) and `5` (32).  The first star in canonical packet
   order with increment above two is `x_13(e)`, entries
   `3182,3186,3356,3360,3425`, with increment `4`.  These stars factor a
   one-letter occurrence through displayed constant coefficients `1` or a
   reverse one-factor seam; their increments control only path differences,
   and every common mode survives.

The census reproduces the hand-checked families: packet entries `3261,3262`
give increment `0`, and the common-RHS star `3261,3336,3409` gives increment
`2`.

**Consequence.**  The third quotient direction demanded by `(AMQ5)` for a
same-reservoir decoder cannot be supplied by any literal packet entry, however
the literal rows are grouped.  Deciding
`atlas-half-block-root-face-full-packet-model-exists` through the
nuisance-quotient route requires a normal-closure consequence of the packet
(for example the nested returns already recorded) or an identity that uses
ring relations among the coefficient letters, which this free census does not
impose.

**Scope.**  The language imposes no relation among coefficient maps, exactly
as in the hand-checked Atlas nodes.  Leavitt relations such as `Ee=1` are
satisfied by the Morita-rectangular model of
`mixed-steinberg-loops-admit-morita-rectangular-model`, which realizes every
literal equation above, so imposing them does not create the missing
direction on the literal rows either.  No claim is made about
normal-closure consequences.

DERIVATION
atlas-literal-packet-common-mode-census-proof
