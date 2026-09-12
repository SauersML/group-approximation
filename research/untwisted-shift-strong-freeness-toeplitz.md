---
rg: 2
id: untwisted-shift-strong-freeness-toeplitz
kind: claim
title: Attempt at strong freeness of the untwisted B-shift via the exact Toeplitz operator norm, isolating the one convergence input
distinct_from:
  cocycle-twisted-shift-freeness-galois-corner: that reduced to strong freeness of the untwisted B_n-shift from the PFF ambient; this attacks that residual by computing the limiting object as an amalgamated free product with a Toeplitz/creation generator, where the norm is exactly known.
  hnn-over-infinite-cyclic-subgroups-preserves-mf: that is the rank-1 spectral case; this is the general-rank shift via its exact operator norm.
---

OPEN.  Final residual of [[cocycle-twisted-shift-freeness-galois-corner]].
Steps graded.

**The limit object.**  As `n -> oo` along `U`, the PFF ambient `rho_n(G x C)`
strongly converges to `C*_r(G x C)`, and `B_n = rho_n(L)''` to `C*_r(L) = L(F_r)`
(with the regular trace, `L` free of rank `r`).  The untwisted shift `W''_n`
converges to the `B`-valued creation/shift operator `V` on the full Fock module
`F_B(H)` over `B = L(F_r)`.  The pair `(C*_r(G x C), V)` generates the reduced
amalgamated free product `C*_r(G x C) *_B (B-Toeplitz)`, whose norm is exactly
computable (Voiculescu/Haagerup operator-valued Fock norm).  `[STANDARD -- the
limit is an operator-valued free-Toeplitz algebra]`.

## Step 1 -- weak convergence is free `[PROVED, imported]`

The `*`-moments (traces of words) of `(rho_n(G x C), W''_n)` converge to those
of `(C*_r(G x C), V)` amalgamated free over `B`: this is the tracial (weak)
statement, and it holds because `W''_n` is an honest `B_n`-shift (creation
operator on a growing Fock corner) whose moments against the ambient are the
free-Fock moments by direct computation -- a reduced word with a non-`B`
letter between opposite shift powers has one uncancelled creation, hence trace
`0`.  `[PROVED]` (this is the same computation as Britton's lemma at the trace
level).

## Step 2 -- strong (norm) convergence `[GAP, the sole remaining input]`

MF needs `| ||P(rho_n, W''_n)|| - ||P(pi, V)|| | -> 0` for every
noncommutative polynomial `P`, not just the traces.  For a SINGLE free Haar
unitary or free semicircular against a strongly convergent family this is
Haagerup--Thorbjornsen / Collins--Male; the operator-valued (amalgamated over
`B`) version for the free-Toeplitz shift `V` against a PFF family is the
needed theorem.  `[GAP]`.

## Step 3 -- why strong convergence is plausible here, and the precise missing lemma `[GAP]`

Two reductions that make Step 2 concrete:

* **Fock dilation.**  `V` is a one-sided shift; `V + V^*` is an operator-valued
  semicircular element over `B` (free Poisson / free-Fock).  Strong
  convergence of `rho_n(G x C)` plus an INDEPENDENT operator-valued
  semicircular converging strongly is exactly the amalgamated Haagerup--
  Thorbjornsen theorem of Collins--Guionnet--Parraud-type.  If `W''_n` can be
  realized as (the isometric part of) such a strongly convergent operator-
  valued semicircular over `B_n`, Step 2 follows.  `[REDUCES TO Collins--
  Guionnet--Parraud amalgamated strong convergence]`.

* **The gap.**  I do not have a citation that the amalgamated (over a
  non-scalar `B_n = L(F_r)`-corner) strong convergence holds for the specific
  deterministic `W''_n` we built (it is deterministic, not Gaussian).  The
  honest statement is: Step 2 holds IF the deterministic `B_n`-shift is
  strongly free from the PFF ambient over `B_n`, which is what recent strong-
  convergence technology (Bordenave--Collins 2019; Belinschi--Capitaine 2022
  operator-valued; Magee--de la Salle 2023) is designed to prove, but which I
  cannot assemble to proof standard here.

## Verdict

The limit object is identified exactly (operator-valued free Toeplitz over
`B = L(F_r)`), the weak/tracial convergence is PROVED (Britton at trace level),
and strong convergence -- the one thing MF needs beyond the trace -- is the
amalgamated strong-freeness theorem for an operator-valued shift, reducible to
Collins--Guionnet--Parraud / Belinschi--Capitaine operator-valued strong
convergence.  That is the terminal lemma.  It is a known-technology,
very-likely-true statement, not a new obstruction, but its rigorous proof is
beyond what I can reconstruct.

This closes the decomposition: the prize is
```text
MF_fp is Pi^0_2-complete
  <==  the operator-valued B-shift is strongly free from the PFF ambient over B
```
with everything on the left of `<==` proved.  The right side is a single
operator-valued strong-convergence statement in current free-probability
technology.

## Attempts

Weak convergence proved (Step 1); strong convergence (Step 2) reduced to
operator-valued Collins--Guionnet--Parraud / Belinschi--Capitaine strong
freeness (Step 3), the terminal lemma.
