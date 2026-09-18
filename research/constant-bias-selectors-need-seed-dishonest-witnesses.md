---
rg: 2
id: constant-bias-selectors-need-seed-dishonest-witnesses
kind: claim
title: On any doubled LEC with near-uniform directions, comparable marginals, fibre separation kappa and tight outer soundness, a polynomial-time branch selector with YES lift value 1/2 + gamma puts the source in RP unless its witnesses carry seed-dishonest satisfied mass above gamma - gamma' - kappa against every honest labelling of every good outer labelling, so A-side non-honesty is worth at most kappa = 1/(2^l - 1) and the constant-bias cell reduces to a statement about seed labels alone
distinct_from:
  near-perfect-selectors-die-on-every-rigid-doubled-lec: that is Theorem S* at lift value 1 - xi, with 99 percent rigidity (agreement outside mass zeta) as hypothesis; this works at every lift value 1/2 + gamma, replaces rigidity by the much weaker 50 percent condition that only the satisfied, ev-dishonest mass be small, and shows that this mass is controlled by seed labels alone up to kappa.
  efficient-branch-selectors-list-decode-honest-outer-labels: that decodes at 1/2 + gamma only when the witness is the honest encoding or near it (endpoint disagreement zeta < gamma); this allows witnesses that disagree with every honest encoding on all their A-labels, provided the seed labels of their satisfied constraints are mostly honest.
  view-local-selectors-beat-one-half-through-non-honest-witnesses: that is the OPEN heretic H2 for view-local selectors; this is a selector-free necessary condition on the witnesses of H2 and of the constant-bias cell of H1, for every selector, with the survivor pinned to seed-level non-honesty.
  parity-leaking-branch-selectors-reach-near-perfect-completeness: that is the OPEN hole H1; this covers its constant-bias cell (1/2, 1 - 10^(-5)), which every recorded kill left untouched, on every doubled LEC meeting the four hypotheses.
artifacts:
  - experiments/ugc-constant-bias-2026-09-17/check_seed_dishonest_mass.py
---

**ESTABLISHED.** Route: `constant-bias-selectors-need-seed-dishonest-witnesses-proof`.
This is conditional on `NP not in RP`, which cannot be removed (Theorem 2 of
`efficient-branch-selectors-list-decode-honest-outer-labels`).

## Setting

A *doubled LEC* `x -> D(x)` is as in
`near-perfect-selectors-die-on-every-rigid-doubled-lec`:

- an outer projection game `Phi = (A, B, rho, pi)` with `A`-labels in `F_2^m`,
  where `2^m <= poly(|x|)`;
- an inner 2-to-1 game `G` on `P x Q` with law `mu` and onto 2-to-1 maps
  `pi_e : Sigma_(p_e) -> Sigma_(q_e)`, where `|Sigma_q| <= 2^(l-1)`;
- annotations `(a_e, x_e, ev_e)`, with seed `w_e := q_e`.

An orientation `o` gives the doubled lift `U_o`, with constraint
`sigma -> (pi_e(sigma), o_e(sigma))` and bit function `G_e(tau, b) := ev_e(sigma)`
for the unique `sigma` sent to `(tau, b)`.

Fix a labelling `H = (sigma, tau)` of `G` and an outer labelling `lambda`. Write
`Sat(H) := { e : pi_e(sigma_(p_e)) = tau_(q_e) }`.

* The **ev-dishonest satisfied mass** is
  `D(H, lambda) := mu{ e in Sat(H) : ev_e(sigma_(p_e)) != <lambda_(a_e), x_e> }`.
* For a second labelling `H0 = (sigma*, tau*)`, the **seed-dishonest satisfied
  mass** is `beta(H, H0) := mu{ e in Sat(H) : tau_(q_e) != tau*_(q_e) }`.
* `H0` is a **`lambda`-reference with defect `r`** if
  `mu{ e : e notin Sat(H0) or ev_e(sigma*_(p_e)) != <lambda_(a_e), x_e> } <= r`.
  This is dirt plus violated mass. The honest encoding of a good `lambda` in a
  composition with completeness `1 - eta` has defect `<= eta + d`.

## Hypotheses

They are needed on YES inputs only, except (S).

* **(E_tau)** For every `(q, a)` in the support of `(w_e, a_e)`, the law of
  `x_e` is `tau`-close to uniform on `F_2^m` in total variation.
* **(M)** `nu_A(a) <= K rho_A(a)`, where `nu_A` is the `mu`-law of `a_e`.
* **(Sep_kappa) fibre separation.** Let `c(p) := max` over pairs
  `sigma != sigma'` in `Sigma_p` of
  `Pr_(e~mu)[ pi_e(sigma) = pi_e(sigma') | p_e = p ]`. Then
  `E_(p ~ mu_P) c(p) <= kappa`, where `mu_P` is the `mu`-law of `p_e`. The
  pointwise form `c(p) <= kappa` for every `p` is the usual special case.
* **(S)** On NO inputs `val(Phi) <= s < c0/2`, where
  `p = gamma'^3 2^(-l-2)` and `c0 = p^2/K^2 - 2 eps`.

**(Sep_kappa) for Grassmann tests.** Suppose `Sigma_p` is the set of linear
functionals on an `l`-space `L`, and the constraints at `p` restrict to a
hyperplane `L'` of `L` that is uniform given `p`. Two distinct functionals agree
on `L'` iff their nonzero difference vanishes on `L'`, and that happens for
exactly one hyperplane. So `kappa = 1/(2^l - 1)`.

Folded labels are functionals on `L + H_U` with prescribed values on `H_U`. For
them the difference is a functional vanishing on `H_U`, and the same count
holds with `L'` replaced by `L' + H_U`. The artifact checks the plain case
exhaustively for `(n, l) = (3,2), (4,2), (4,3), (5,3)`.

For DKKMS the hyperplane `L'` given `(U, L)` is uniform up to the smoothing
distance `SD`, which gives `kappa <= 1/(2^l - 1) + SD`. That is recorded as an
argument, not as an established premise.

## Statements

**Lemma F (A-side non-honesty is worth at most kappa).** Assume (Sep_kappa).
Let `H` be any labelling of `G`, and let `H0` be a `lambda`-reference with
defect `r`. Then

```text
D(H, lambda)  <=  beta(H, H0) + r + kappa.
```

**Theorem C (constant-bias decoding).** Let `x -> D(x)` be a doubled LEC for a
promise problem `Lang` satisfying (E_tau) with `tau <= gamma'/4`, (M) and (S).
Suppose that on every YES input the following 50% condition holds.

* **(Str(gamma, gamma', eps))** Every labelling `H` of `G` with
  `val_G(H) >= 1/2 + gamma` has an outer labelling `lambda` with
  `val_Phi(lambda) >= 1 - eps` and `D(H, lambda) <= gamma - gamma'`.

Let `S` be any randomized polynomial-time algorithm that outputs an orientation
of `G(x)`. It may be global, adaptive and parity-leaking. Suppose that for every
YES input `x`,

```text
Pr_S [ val(U_(S(x))) >= 1/2 + gamma ]  >=  theta(|x|)  >=  1/poly(|x|).
```

Then `Lang in RP`, with one-sided success probability `>= theta c0/2` per trial.

**Corollary C' (seed form).** Under (Sep_kappa), (Str) follows from the
following condition on seed labels alone.

* **(Seed(gamma, gamma', eps, r)).** Every labelling `H` of `G` with
  `val_G(H) >= 1/2 + gamma` has a `lambda`-reference `H0` of defect `<= r`, for
  some `lambda` with `val_Phi(lambda) >= 1 - eps`, such that
  `beta(H, H0) <= gamma - gamma' - r - kappa`.

So on every doubled LEC with (E_tau), (M), (S) and (Sep_kappa), if `NP not in RP`,
any selector reaching YES lift value `1/2 + gamma` needs witnesses of the
following kind. For every good `lambda` and every `lambda`-reference `H0` of
defect `r`, their satisfied constraints carry seed labels that differ from
those of `H0` on mass `> gamma - gamma' - r - kappa`.

## What it does to the constant-bias cell (impact types 2 and 3)

Every recorded kill of H1 (`parity-leaking-branch-selectors-reach-near-perfect-completeness`)
stops at lift value `1 - 10^(-5)`:

- Theorem S and Theorem S\* need 99% rigidity;
- spectral gates are vacuous once `l` grows;
- the honest list decoder covers only near-honest witnesses.

The cell `(1/2, 1 - 10^(-5))` was open for every selector, and H2 was open with
no condition on its witnesses.

* **Class killed (under `NP not in RP`).** Consider witnesses whose
  non-honesty sits on the A-side: they are obtained from an honest encoding
  (or any low-defect reference) by changing A-labels arbitrarily, keeping seed
  labels on all but `gamma - gamma' - r - kappa` of their satisfied mass. This
  includes:
  - zoom-in or zoom-out relabellings of A-vertices;
  - per-vertex mixtures of several good assignments at the A-side;
  - folding-class relabellings;
  - an honest encoding with a `1/2 - gamma` fraction of A-vertices replaced by
    garbage.

  All of these die, for every selector and at every lift value `1/2 + gamma`
  with `gamma > gamma' + r + kappa`. The **invariant** is the seed-dishonest
  satisfied mass `beta`. **Every member dies at the counting step of Lemma F.**
  Two distinct A-labels share a seed projection on at most a `kappa` fraction
  of their constraints, so an A-label that disagrees with the reference is
  ev-dishonest on a satisfied constraint only where the seed label also
  disagrees, up to `kappa`. The seed-guessing list decoder of Theorem 1 then
  reads a predictor of advantage `gamma'` from the selector's own bits.
* **Decomposition.** The constant-bias cell on doubled LECs now needs one of
  (C1) no linear read-out with `gamma'/4`-uniform directions, (C2) unbounded
  `K`, (C3) outer soundness not below `c0/2 = Theta(gamma'^6 4^(-l)/K^2)`, or
  (C4) failure of (Seed). (C4) is a statement about the inner game alone,
  and in fact only about B-labels: YES instances must carry labellings of value
  `>= 1/2 + gamma` whose satisfied seeds disagree, on constant mass, with every
  honest encoding of every good outer labelling. It mentions no selector and no
  complexity assumption. For Grassmann tests `kappa = 1/(2^l - 1)`, which is
  negligible against a constant `gamma` once `l` is large, as it is in DKKMS.
* **Why seed-dishonest labellings are the hard case.** Take two good
  assignments `lambda, lambda'` and label each B-vertex by the one that the
  majority of its A-neighbours use. On an outer game whose `A-B` graph mixes,
  every balanced split of the A-side leaves most B-vertices with nearly
  balanced neighbourhoods. The value is then about `1/2`, with seed-dishonest
  mass about `1/4` against each of `lambda, lambda'`. So value above `1/2`
  forces a majority explanation at the seeds, *provided* the split is balanced
  at almost every B-vertex. (C4) is exactly the negation of that 50% statement.
  This is a heuristic, not a proof.

This neither proves nor refutes UGC.

## Not covered

* 2-to-2 inner games. The bit-free identity used here is for 2-to-1
  constraints.
* Whether (Seed) holds on DKKMS. It is a 50%-regime inverse statement for the
  B-side of the Grassmann 2-to-1 test, and it is OPEN.
