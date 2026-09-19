---
rg: 2
id: matrix-restricted-burnside-gap
kind: claim
title: Approximate exponent-N power laws force the restricted Burnside relators, dimension-free
distinct_from:
  corona-restricted-burnside-equals-power-law-moduli: that is the established equivalence between this statement and the corona formulation; this is the statement itself, the frontier hole the equivalence isolates.
  finite-group-opnorm-support-profile: that fixes a finite group in advance and corrects an approximate model of ITS presentation; here no group is fixed -- only an exponent -- and the finite word set W is part of the conclusion, not the hypothesis.
  opnorm-packet-exactification-is-dimension-free: that rounds approximate matrix units with a modulus depending only on the packet size; this rounds nothing and asserts an implication between word norms.
artifacts:
  - research/artifacts/opnorm-burnside-dossier-2026-08-24.md
---

Fix `m, N >= 2` and the presentation `R(m,N) = <x_1..x_m | s_1..s_k>` of
`(RB1)`. For every relator `s_j` there exist a **finite** set of words
`W subset F_m` and `eta > 0`, depending on `m, N, s_j` only, such that for
every matrix size `d` and every `(U_1,...,U_m) in U(d)^m`,

```text
max_(w in W) || w(U)^N - I || < eta
   ==>   || s_j(U) - I || < delta_N,       delta_N = 2 sin(pi/N).
```

By the sharpened-target paragraph of
`corona-restricted-burnside-equals-power-law-moduli`, the single threshold
`delta_N` suffices; quantifying over all `eps > 0` is not needed.

## Attempts

1. **Fix the group first and quote finite-group stability.** The repository's
   `finite-group-opnorm-support-profile` gives exactly this shape once a
   finite group `H` and a finite presentation of it are fixed in advance:
   sufficiently accurate operator-norm models are dimension-freely close to
   exact representations, in the same dimension. That is not available here.
   The hypothesis names only the exponent; the tuple is not known to be near
   any representation of `R(m,N)`, and the number of power equations needed
   to pin it is not bounded a priori. Dies precisely at "which finite group".

2. **Compactness in one dimension.** For a fixed `d` a limit argument in
   `U(d)^m` turns approximate power laws into exact ones and Schur plus
   Mal'cev finish (this is the mechanism of
   `bounded-dimension-microstates-force-lef`). It gives `eta = eta(d)` and
   nothing uniform: `U(d)^m` is compact for each `d` but the family is not
   uniformly so. Dies on dimension dependence, which is the entire content.

3. **Average into an exact commutant, as in the abelian case.**
   `corona-commuting-torsion-lifts-proof` handles commuting torsion families
   by averaging over the finite abelian group built so far and rounding the
   spectrum. Its Step 2 finite exactification lemma **is** this statement for
   the abelian relators. It does not generalize: with no commutation
   hypothesis there is no finite group to average over until the theorem is
   already proved.

4. **Metric approximate subgroups (Hrushovski--Rodriguez Fanlo,
   arXiv:2209.01262, J. Math. Logic 2025).** Their bounded-exponent result
   removes the connected Lie component: a `(k,r)`-metric approximate subgroup
   of bounded exponent is close to a `(1,r')`-metric approximate subgroup.
   The hypothesis is a quantitative covering/discretization bound of the form
   `N_(2^-m)(X) <= C^m N_1(X)`. Obtaining that control for the growing word
   balls of an arbitrary operator-norm matrix model is not supplied by
   anything here, and no argument for it is known to this lane. Their theorem
   does **not** prove this claim; it identifies the surviving obstacle as the
   totally disconnected residue.

5. **Voiculescu's almost-commuting unitaries** are the standing warning that
   general finite partial group laws are *not* operator-norm stable. Fixed
   bounded exponent may remove that particular `K`-theoretic freedom -- the
   Voiculescu obstruction is a Bott class, and torsion spectra are rigid --
   but no theorem is known here that it always does. Deferred, not refuted.
