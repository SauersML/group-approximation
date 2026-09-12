---
rg: 2
id: kt-coset-bernoulli-essentially-free
kind: claim
title: The Kun--Thom generalized Bernoulli coset action is essentially free
distinct_from:
  coset-bernoulli-action-is-essentially-free: that proves essential freeness for the ARITHMETIC pair (SL_3(Z[1/p]), SL_3(Z)) through the Bruhat--Tits building of SL_3(Q_p); this asks it for the Kun--Thom Theorem E pair, whose actor is an elementary group over a Laurent ring extended by SL_d(Z) and has no single building, so that argument does not transfer.
artifacts:
  - research/artifacts/kt-wreath-double-re-unification-2026-09-11.md
---

**OPEN.**  Fix the Kun--Thom Theorem E pair `Gamma < G`, put `I = G/Gamma`,
and let `G` act on `X = {-1,1}^I` with the Bernoulli(1/2) product measure by
permuting coordinates.  Prove that the action is essentially free:
`mu(Fix_X(g)) = 0` for every `g != 1`, equivalently every `g != 1` moves
infinitely many cosets in `I` (finitely many moved cosets gives a
positive-measure fixed set; infinitely many gives measure zero by independence
of the orbit-constancy events).

**Why it is worth posing.**  Essential freeness is exactly the hypothesis
Feldman--Moore needs to make the lamp algebra `L^infinity(X)` a Cartan masa in
`L(W) = L^infinity(X) rtimes G`, the wreath of
`kt-wreath-hyperlinear-iff-double-hyperlinear`.  With that Cartan in hand the
Jung--Hayes strong-1-boundedness bound applies verbatim, exactly as it does for
the arithmetic wreath in
`coset-wreath-hyperlinearity-forces-strong-one-boundedness`: any hyperlinear
model of `W` would then have to be rigid, its microstate spaces admitting
subexponential-in-`d^2` epsilon-nets, so no `c d^2`-parameter family of
pairwise non-conjugate models can exist.  This is the entropy-ceiling
discipline the arithmetic lane already enforces; establishing this claim
imports it to the Kun--Thom wreath, the group that is actually nonsofic.

## Attempts

- **Building argument (arithmetic pair) does not transfer.**
  `coset-bernoulli-action-is-essentially-free` proves the analogue for
  `(SL_3(Z[1/p]), SL_3(Z))` by identifying `I` with the type-0 vertices of the
  Bruhat--Tits building of `SL_3(Q_p)` and using convexity of fixed sets in the
  CAT(0) building. The Kun--Thom actor `EL_r(F_q[x^(±1)]) rtimes SL_d(Z)` is
  not a single arithmetic lattice in one p-adic group, so there is no one
  building to run the convexity endgame in.
- **The elementary directions look tractable.** For `g` in the Laurent
  elementary subgroup `EL_r(F_q[x^(±1)])`, a monomial substitution moves some
  exponent of a nonzero Laurent polynomial out of any fixed cone, which should
  move infinitely many cosets; this is the same mechanism the compression
  semigroup uses in `kt-two-positive-compressors-generate-full-obstruction`.
- **The `SL_d(Z)` factor and mixed elements are open.** A nonidentity element
  supported on or mixed into the finite-dimensional `SL_d(Z)` factor could a
  priori fix a cofinite set of cosets; ruling this out is the unproved core of
  the claim and the reason it is posed separately from the arithmetic node.
