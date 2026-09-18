---
rg: 2
id: abelian-layer-alphabets-kill-magnus-pieces-of-rank-two
kind: claim
title: For Magnus rank n >= 2, a shift configuration whose letter at a coordinate generates a solvable normal layer of bounded derived length kills an explicit nontrivial element of the piece, so the Baumslag--Gersten prepend tower does not pass to n >= 2
distinct_from:
  bg-shift-chains-die-in-residually-linear-alphabets: that kills whole alphabets (residually linear, solvable, periodic) for the n = 1 chain of BG; this allows any alphabet and kills only representations whose layer at the extreme letter is solvable of bounded length, at every n >= 2, including alphabets that satisfy (AA) for BG.
  baumslag-gersten-elementary-amenable-quotient-keeps-a: that proves the abelian prepend tower works at n = 1; this proves the same tower, and every tower with layers of bounded derived length, fails separation at n >= 2.
  amenable-alphabet-magnus-shift-dictionary-sofic: that is the dictionary with hypothesis (AA); this is an obstruction to one way of producing (AA), not to (AA) itself.
artifacts:
  - research/abelian-layer-alphabets-kill-magnus-pieces-of-rank-two-proof.md
---

ESTABLISHED (written proof, unreviewed). Proof:
[[abelian-layer-alphabets-kill-magnus-pieces-of-rank-two-proof]].

**Setting.** A Magnus rewriting `W_0(a_0,...,a_n)` involves both `a_0` and
`a_n`, and `n >= 2`. The piece is `B_0 = <a_0..a_n | W_0>`, with
`F_- = <a_0..a_(n-1)>` free of rank `n` (Freiheitssatz). Let
`psi : B_0 -> Q` be any homomorphism, for instance the coordinate-0 window
representation `a_i -> x_i` of a shift configuration.

Define `b_1 = [a_0, a_1 a_0 a_1^(-1)]` and
`b_(d+1) = [b_d, a_1 b_d a_1^(-1)]`. These are words in `a_0, a_1`.

**Theorem.** (a) Each `b_d` is a nontrivial element of `F_- <= B_0`.
(b) If `psi(a_0)` lies in a normal subgroup `S` of `<psi(a_0),...,psi(a_n)>`
that is solvable of derived length at most `d`, then `psi(b_d) = 1`.

**Corollary.**
* **The abelian prepend tower.** The tower of
  [[bs12-amenable-square-chain-induced-tower-proof]], applied to any
  rewriting with `n >= 2`, with any seed and any linearizable extreme, puts
  each letter `x_j` in an abelian normal layer. So every one of its window
  representations kills `b_1`. Hypothesis (AA) of
  [[amenable-alphabet-magnus-shift-dictionary-sofic]] then fails at
  `E_1 = {b_1}`.
* **Bounded solvable layers.** The same failure, at `E_1 = {b_d}`, happens for
  any family of towers whose layers are solvable of derived length at most
  `d`.
* **What (AA) needs at `n >= 2`.** A family of alphabets that witnesses (AA)
  must realize the extreme letter `a_0` in normal layers of **unbounded**
  derived length, or in non-solvable amenable layers.
* **Why BG escapes.** For `n = 1`, `F_- = <a_0>` is cyclic and `b_1 = 1`. So
  the success at `n = 1` does not pass to `n >= 2`.

## Where this leaves the dictionary

The prepend-and-limit mechanism is still available at `n >= 2`. But the
prepend functor can no longer be an abelian (or bounded-solvable) extension.
It has to be a **relative one-relator product**
`P(K) = (K * <X>) / <<W_0(X, x_1, ..., x_n)>>`, or an amenable quotient of it
that keeps the normal closure of `X` residually faithful on `F_-`. It must
also send injections `K -> L` to injections. That functoriality is a
Freiheitssatz for one-relator products over amenable coefficient groups.
It is the concrete open input for pushing the tower past `n = 1`.
