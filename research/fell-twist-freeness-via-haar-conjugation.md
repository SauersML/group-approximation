---
rg: 2
id: fell-twist-freeness-via-haar-conjugation
kind: claim
title: Attempt at the Fell-twist freeness estimate by Haar conjugation, reducing it to relative asymptotic freeness of a permutation twist
distinct_from:
  strong-convergence-fell-shifted-hnn-model: that states the conditional (R MF iff Fell twist free rel L) and names the estimate; this attempts the estimate and reduces it to a concrete, possibly-known relative-freeness fact.
  hnn-over-infinite-cyclic-subgroups-preserves-mf: that is the rank-1 case done by spectral means; this attacks arbitrary rank by conjugation freeness.
---

OPEN.  A direct attempt at the sole remaining input of
[[strong-convergence-fell-shifted-hnn-model]].  Steps graded.

**What must be shown.**  In the PFF model `rho_n : G x C -> U(d_n)`, with
`W_n` the Fell twist on the `L`-regular corner, the pair
`(rho_n(G x C), W_n)` is asymptotically `*`-free with amalgamation over
`rho_n(L x 1)`; equivalently, for every alternating word in `s^{+-1}` and
`(G x C) \ L`, the normalized trace tends to `0`.

## Reduction to a fresh-unitary model `[PROVED, standard]`

MF is witnessed by ANY strongly convergent sequence.  We are free to enlarge
`d_n` and pre-compose `W_n` with a Haar-random unitary `U_n` on the corner
that commutes with `rho_n(L)` (so as not to disturb the edge relation `(S)`).
Replacing `W_n` by `U_n W_n U_n^*` keeps
`(U_n W_n U_n^*) rho_n(l,1) (U_n W_n U_n^*)^* = rho_n(l,phi(l))` because
`U_n` commutes with `rho_n(L)` and the edge relation only involves `L`.
`[PROVED]`.  So we may take the twist to be `W_n' = U_n W_n U_n^*` with
`U_n` Haar in the relative commutant of `rho_n(L)`.

## Voiculescu asymptotic freeness `[STANDARD, the load-bearing citation]`

Voiculescu's theorem: a Haar-random unitary `U_n` is asymptotically free from
any fixed sequence of matrices, in the strong (operator-norm) sense after
Collins--Male and Bordenave--Collins.  The **relative** (amalgamated) version
over a common subalgebra `B_n = rho_n(L)''`: if `U_n` is Haar in the relative
commutant `B_n' cap M_{d_n}`, then `U_n` is asymptotically free from
`rho_n(G x C)` **with amalgamation over `B_n`**.  `[STANDARD -- amalgamated
strong asymptotic freeness of Haar unitaries over a fixed corner, in the
operator-norm/PFF setting]`.

## Transferring freeness from `U_n` to `W_n' `[GAP: the twist is not itself Haar]`

`W_n' = U_n W_n U_n^*` is a *conjugate* of the Fell twist, not a Haar unitary.
Conjugating a fixed unitary `W_n` by a Haar `U_n` (relative to `B_n`) makes
`W_n'` free from any fixed algebra *provided* `W_n` and the fixed algebra are
both in `general position`, but conjugation by `U_n` alone does not make
`W_n'` free from `rho_n(G x C)` unless `W_n` is `B_n`-free from `rho_n(G x C)`
to begin with -- conjugation preserves the joint distribution of
`(W_n, rho_n(G x C))` up to the `U_n`-average, and freeness of `W_n'` from the
ambient requires that `W_n` have the right `B_n`-valued distribution
(e.g. a `B_n`-Haar or `B_n`-semicircular element).  `[GAP]`.

## The residual point `[GAP, honestly the same estimate relocated]`

`W_n` is the Fell twist: on the `L`-regular corner
`l^2(L)^{(m_n)} (x) C^{k_n}` it acts as `(shift on l^2(L)) (x) sigma_n`-ish,
a permutation-times-rep unitary.  Its `B_n = rho_n(L)`-valued distribution is
that of a `B_n`-diagonal isometric shift, NOT a `B_n`-Haar unitary, so the
clean Haar-conjugation freeness does not directly apply.  What is true:

* If the twist were replaced by a genuine `B_n`-Haar unitary, freeness would
  follow from the standard amalgamated Voiculescu theorem `[STANDARD]`, and
  `R` would be MF.  So the group
  `R_haar = < G x C, s | [s, L x 1] = 1 >` (central HNN, `phi = 0`, i.e. the
  twist is trivial hence any Haar `s` works) is MF -- consistent with
  [[regular-mf-central-hnn-closure]].
* For the *actual* twist implementing `phi != 0`, the `B_n`-valued
  distribution is pinned (it must reproduce `s (l,1) s^* = (l,phi(l))`), so we
  cannot randomize it into a `B_n`-Haar unitary; the edge relation and
  freeness pull against each other exactly as in
  [[fp-forces-hnn-edge-into-free-entropy-obstruction]].

## Verdict

Haar conjugation cleanly handles the `phi = 0` (central) case and re-proves
[[regular-mf-central-hnn-closure]], but for `phi != 0` the twist's
`B_n`-valued distribution is forced by the edge relation and is not Haar, so
the standard amalgamated asymptotic-freeness theorem does not apply as a black
box.  The estimate that remains is: a `B_n`-diagonal *shift* twist
implementing a fixed `B_n`-cocycle `phi` is asymptotically free from a PFF
ambient over `B_n`.  This is a specific `B_n`-valued strong-freeness statement,
neither a black-box citation nor refuted -- it is the genuine open estimate,
now identified as "amalgamated strong freeness of a cocycle-twisted shift",
one notch more concrete than before.

## Attempts

The Haar-conjugation reduction (Steps 1--2) is standard and disposes of the
central case; the twisted case (Steps 3--4) is the open estimate, now stated
as amalgamated strong freeness of a `phi`-cocycle-twisted shift over the
`L`-corner.
