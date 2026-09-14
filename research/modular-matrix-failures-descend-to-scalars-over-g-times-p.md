---
rg: 2
id: modular-matrix-failures-descend-to-scalars-over-g-times-p
kind: claim
title: Some M_n(F_p[G]) fails direct finiteness exactly when F_p[G × P] does for some finite group P of order prime to p
distinct_from:
  kaplansky-direct-stable-finiteness-one-universal-group: that proves direct and stable finiteness agree after quantifying over all groups, through one universal host; this keeps the host, trading the matrix size for a finite direct factor P, group by group.
  stable-finiteness-failure-refutes-surjunctivity: that turns a one-sided matrix inverse over a finite field into a strict automaton over the alphabet k^n; this moves the one-sided inverse down to n = 1, over the prime field, at the price of replacing G by G × P.
  some-nonsurjunctive-group-gives-a-binary-one: that is universal binary descent for arbitrary strict automata; this proves binary descent only for strict automata that are linear over a field of characteristic two.
artifacts:
  - research/artifacts/gk3-binary-descent-2-2026-09-14.md
---

**ESTABLISHED** by `modular-matrix-failure-descent-proof`. Elementary (Maschke's theorem plus an explicit
monomial representation); no novelty is claimed, and no statement of it was found on main.

Let `p` be a prime and `G` a group.

**Theorem.** The following are equivalent.
1. `M_n(F_p[G])` is not directly finite for some `n >= 1`.
2. `F_p[G × P]` is not directly finite for some finite group `P` with `p ∤ |P|`.

In (1) ⇒ (2) one may take `P = (C_q)^r ⋊ C_r`, with `C_r` permuting the coordinates cyclically, for any
primes `q, r` different from `p` with `r >= n`. For `p = 2` and `n <= 3`, `P = C_3^3 ⋊ C_3` (order 81) works.

**Automaton form** (`linear-strict-pairs-are-transposes-of-post-surjective-automata`, items 2 and 3, over
`k = F_p`):
- `G` carries an `F_p`-linear injective, non-surjective automaton over the alphabet `F_p^n` for some `n`,
- iff `G × P` carries an `F_p`-linear injective, non-surjective automaton over the alphabet `F_p`, for some
  finite `P` with `p ∤ |P|`.

An automaton that is linear over `F_(p^d)` is `F_p`-linear after a choice of basis, so it is covered.

**Consequences.**
- **Binary descent for linear witnesses.** A strict automaton, over any group `G` and any alphabet, that is
  linear over a field of characteristic two gives a binary strict automaton over `G × P` with `|P|` odd. So
  `some-nonsurjunctive-group-gives-a-binary-one` holds for such witnesses, and the binary witness keeps the
  host up to a finite direct factor.
- **Host-level stable finiteness.** `F_p[G]` is stably finite iff `F_p[G × P]` is directly finite for every
  finite `P` of order prime to `p`. (Forward direction: `F_p[G × P]` is a finite product of rings
  `M_(r_i)(F_i[G])`, each a unital subring of some `M_N(F_p[G])`.)
- **Scope.** Nonlinear strict automata are not touched. The proof uses linear complements (Maschke), which
  have no analogue for nonlinear rules; what survives nonlinearly is
  `binary-shifts-over-odd-fibers-split-off-the-augmentation-shift`.

**Calibration** (artifact Section 3). For `p = 2`, `q = r = 3`, the 81 matrices `ρ(P)` in `GL_3(F_4)` span
an `F_2`-space of dimension 18 = `dim_(F_2) M_3(F_4)`. With `ζ` replaced by `1` the image has 3 elements and
spans dimension 3, so the surjectivity step genuinely uses `ζ != 1`.
