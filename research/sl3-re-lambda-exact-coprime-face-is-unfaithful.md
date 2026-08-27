---
rg: 2
id: sl3-re-lambda-exact-coprime-face-is-unfaithful
kind: claim
title: No relative-embeddability witness of the SL3 lattice pair has coprime-level lambda-exact microstates
distinct_from:
  arithmetic-pair-is-not-relatively-embeddable: that is the full non-RE/C statement over all microstate sectors; this closes exactly the coprime-to-p lambda-exact face of it, for the SL3 pair only, by citation to the sector collapse.
  odd-congruence-lambda-exact-sector-collapses: that is the relative-commutant collapse (RC3) on the coprime lambda-exact sector; this reads its exact W=1 evaluation as a statement about relative embeddability, showing the same sector carries no RE/C witness.
---

Let `Lambda = SL_3(Z) <= Gamma = SL_3(Z[1/p])`, `B = L(Lambda)`,
`h = diag(p, 1, p^-1)`.  A candidate witness of `RE/C`
(`relatively-embeddable-pair-makes-the-hnn-group-hyperlinear`) is a
regular-trace embedding `pi : Gamma -> M = prod_U M_(d_k)` with subalgebras
`B_k subset M_(d_k)` such that `dist_2(pi_k(g), B_k) -> 0` for `g in Lambda`
and `||E_(B_k)(pi_k(a))||_2 -> 0` for `a in Gamma - Lambda`.  Call it
**`Lambda`-exact of coprime type** if its `Lambda`-restriction has genuine
finite-dimensional microstates `sigma_m` factoring through
`SL_3(Z/n_m)` with `gcd(n_m, p) = 1`.

**THEOREM.**  No `RE/C` witness of the `SL_3` pair is `Lambda`-exact of
coprime type.  Equivalently, the coprime-to-`p` `Lambda`-exact face of
`arithmetic-pair-is-not-relatively-embeddable` is closed.

**Proof.**  On this face `odd-congruence-lambda-exact-sector-collapses`
(coprimality-only form) proves, via the Weyl three-term relation
`h h''^-1 = h'`, that the corrector `W = V'^* pi(h)` equals `1` exactly,
where `V' = [sigma_m(lambda_(h,m))]` is the congruence slot of `h`
(`lambda_(h,m) in Lambda`, `= h mod n_m`).  Thus

```text
pi(h) = V' in pi(Lambda)'' subseteq M.                          (RECF1)
```

`V'` is a `||.||_2`-limit of image elements of `Lambda`, so it lies in
`pi(Lambda)''`.  Near-containment is exact containment in the ultraproduct:
`dist_2(pi_k(g), B_k) -> 0` and `B = prod_U B_k` is `||.||_2`-closed, so
`pi(Lambda) subset B`, hence `pi(Lambda)'' subseteq B`.  With `(RECF1)`,
`pi(h) in B`.  Since `Gamma = <Lambda, h>` (conjugating elementary
matrices of `Lambda` by powers of `h` scales the off-diagonal entry by
powers of `p`, generating every `e_ij(p^k)`), and `pi(h), pi(Lambda) in B`
with `B` an algebra,

```text
pi(Gamma) subset B,   so   ||E_(B_k)(pi_k(a))||_2 -> 1   (a != e),   (RECF2)
```

contradicting `||E_(B_k)(pi_k(a))||_2 -> 0` for `a notin Lambda`.  So no
such witness exists. ∎

**Why `SL_3` and coprime.**  The exact `W = 1` uses the rank-two three-term
Weyl relation; at `SL_2` only `W^2 = 1` survives
(`two-power-sector-conjugator-dichotomy`, the Iwahori involution seed), so
the `SL_2` coprime face is NOT closed this way.  Coprimality is what makes
`sigma_m` factor through a quotient in which `h` has a congruence value; at
`p`-power levels `h` is not defined mod `n_m` and the argument stops
(`odd-congruence-lambda-exact-sector-collapses`, mixed-level analysis).

**Consequence.**  Combined with the peer confinement
`kazhdan-subgroup-weak-ucp-exactifies-microstates` (which, under
`sl3-z-weakly-ucp-stable`, moves every `RE/C` candidate to the
`Lambda`-exact face) and `lambda-exact-face-of-the-collapse-closes`
(regular-type `p`-power towers), the residual enemy sector of
`arithmetic-pair-is-not-relatively-embeddable` at `n = 3` is exactly the
residual enemy sector of the collapse `(RC3)`: non-regular-type `p`-primary
`Lambda`-exact towers plus the uniformly-inexact `Lambda`-outliers.  The
host-only weakest target and the RCC face are then one problem.  For the
`p = 3` pair the coprime-to-3 face includes every `2`-power level, so this
theorem closes strictly more of the `RE/C` question there.

## Attempts

- **DEMOTED TO OPEN (2026-08-21 adversarial audit).**  The step `(RECF1)`
  `pi(h) = V' in pi(Lambda)''` is false: `V'` is a limit of image elements
  `[sigma_m(mu_m)]` with VARYING `mu_m`, which lie in
  `prod_U sigma_m(Lambda)''`, not in `pi(Lambda)''`.
  `congruence-slot-escapes-ultraproduct-lambda-algebra` exhibits the
  counterexample inside these hypotheses (regular representations of
  `SL_3(Z/n_m)`, coprime levels: `W = 1` on the nose, `pi_m(h)` in every
  coordinate subgroup algebra, yet `E_(pi(Lambda)'')(pi(h)) = 0`), and
  invalidates the route.  The sector collapse
  `odd-congruence-lambda-exact-sector-collapses` is unaffected -- it is a
  statement about commutants, where the coordinatewise/ultraproduct
  distinction does no harm.
- **What survives: the logarithmic-rate theorem.**  Put
  `delta_k(u) = || u - E_(B_k)(u) ||_2` and `eps_k = max_(s in S) delta_k(pi_k(s))`
  for a fixed finite generating set `S` of `Lambda`.  Since `|| E_(B_k) ||_op <= 1`,
  `delta_k(uv) <= || (u - E u) v ||_2 + || (E u)(v - E v) ||_2 <= delta_k(u) + delta_k(v)`,
  so `delta_k(pi_k(mu)) <= |mu|_S eps_k` for every word `mu`.  `SL_3(Z)` has
  property `(tau)`, so its congruence quotients are expanders and the slot
  `lambda_(h,k)` can be chosen with `|lambda_(h,k)|_S = O(log n_k)`.  With
  `W = 1`, `pi_k(h) = pi_k(lambda_(h,k))` up to `o(1)`, hence
  `|| E_(B_k)(pi_k(h)) ||_2 >= 1 - o(1) - O(eps_k log n_k)`.  THEREFORE: no
  `RE/C` witness of the `SL_3` pair is `Lambda`-exact of coprime type with
  `eps_k log n_k -> 0`.  Nothing in Gao's definition constrains the rates,
  so a witness with `eps_k -> 0` slower than `1 / log n_k` is the surviving
  enemy shape on this face: huge `pi_k(Lambda)''` with slow near-containment.
  This conditional statement is a theorem by the above; it has not yet been
  promoted to its own claim.
- **Scope caveat.**  The witness format used here (matrix coordinates,
  `B_k subset M_(d_k)`) is the sufficient form `(CF1)` of
  `relatively-embeddable-pair-makes-the-hnn-group-hyperlinear`; Gao's
  Definition 1.1 allows QWEP coordinates with HYPERFINITE `B_k`.  Even a
  repaired theorem closes the coprime face only among matrix-form
  witnesses.

