---
rg: 2
id: value-free-star-list-references-put-np-in-rp
kind: claim
title: Theorem CL survives with the value condition on the references deleted -- if each star-list reference is only required to be outer-consistent on the satisfied part of the star (edge (a_e, b(w_e)) respected), the unchanged seed-guessing decoder still puts the source in RP, at a loss of 1/L^4 and with no eps term; on DKKMS the seed-to-B marginal costs K1 <= 1/(1-2^(l-k)), so honest encodings of ANY assignment with outer loss below gamma-gamma' are killed with no goodness hypothesis
distinct_from:
  list-star-coherent-selector-witnesses-put-np-in-rp: that requires every list member to have val_Phi >= 1-eps and pays -2eps in Step 4; this drops the value requirement entirely, replacing it by outer consistency on the satisfied star mass (the set X^C), and recovers the outer value from the good stars themselves. Its hypothesis implies this one (Corollary IMP), not conversely.
  efficient-branch-selectors-list-decode-honest-outer-labels: that decodes from one honest witness of value >= 1-eps; this reuses its decoder verbatim (A-rule and B-rule) with arbitrary, possibly very bad, outer references.
  constant-bias-selectors-need-seed-dishonest-witnesses: that is Theorem C with one good global reference; this is the value-free star-list form.
artifacts:
  - experiments/ugc-value-free-star-2026-09-17/check_value_free_star.py
---

**ESTABLISHED** (Theorem CLV and Corollaries IMP, DK^C, HON).
Route: `value-free-star-list-references-put-np-in-rp-proof`.
The consequences are conditional on `NP not in RP`, as for Theorems C and CL.

## What was asked

H1 (`parity-leaking-branch-selectors-reach-near-perfect-completeness`) is open
in the constant-bias cell. Theorem CL
(`list-star-coherent-selector-witnesses-put-np-in-rp`) kills every selector
witness whose satisfied ev-dishonest star mass is small against some member of
a list of GOOD outer labellings (`val_Phi >= 1 - eps`). A counterexample to the
constant-bias cell must therefore escape every list of good references.

The natural escape is to explain the witness by outer labellings that are
*not* good: honest encodings of an assignment `y` that violates a constant
fraction of outer constraints, or per-star references glued from such
encodings. This node shows that escape is closed: the value condition is not
needed. What the decoder needs is only that the reference respect the outer
constraint at the satisfied edges of the star it explains.

## Setting

The notation is that of Theorem CL: a doubled LEC `x -> D(x)` with outer game
`Phi = (A, B, rho, pi)`, inner 2-to-1 game `G` with law `mu`, annotations
`(a_e, x_e, ev_e)`, seed `w_e` with alphabet of size `<= 2^l`, lift `U_o`,
projection `H = (sigma, tau)` of a lift labelling, `Sat(H)`, the star law `nu`
of `(w_e, a_e)`, and `X(H, lambda)`. Hypotheses (E_tau) and (M)
(`nu_A <= K rho_A`) are those of Theorem CL.

Two further structural hypotheses, both about the instance only:

* **(Bw) the seed names the B-vertex.** There is a map `b(.)` with
  `b_e = b(w_e)` for every constraint `e`, where `b_e` is the outer `B`-vertex
  that `e` is built from.
* **(M_B) seed-to-B marginal.** For all `a, b`:
  `mu(b_e = b | a_e = a) <= K1 rho(b | a)`.

An **outer labelling** here is ANY `lambda = (lambda_A, lambda_B)`, with no
condition on `val_Phi(lambda)`. Put

```text
X^C(H, lambda) := X(H, lambda)  union  { e in Sat(H) : pi_(a_e b_e)(lambda_(a_e)) != lambda_(b_e) },
D^C_L(H, Lambda) := E_((w,a) ~ nu)  min_j  mu( X^C(H, lambda^j) | w_e = w, a_e = a ).
```

So a reference is charged for a satisfied edge of the star either when it
predicts the edge's evaluation wrongly or when it breaks the outer constraint
`(a_e, b_e)` the edge was built from. The reference may change from star to
star, as in Theorem CL.

Put `kappa := 2^(-l) gamma'^2 / 4` and `p := kappa gamma' = gamma'^3 2^(-l-2)`.
The soundness hypothesis is

* **(S^C_L)** on NO inputs `val(Phi) <= s < c0^C_L / 2`, where
  `c0^C_L := p^2 gamma'^2 / (K1^2 K^4 L^4)`.

## Statements

**Theorem CLV (value-free star-list decoding).** Let `x -> D(x)` be a doubled
LEC for a promise problem `Lang` satisfying (E_tau) with `tau <= gamma'/4`,
(M), (Bw), (M_B) and (S^C_L). Let `S` be a randomized polynomial-time algorithm
that outputs an orientation of `G(x)`. Suppose that on every YES input `x`,
with probability `>= theta(|x|) >= 1/poly(|x|)` over the coins of `S`, the
orientation `o = S(x)` has the following two properties:
* a lift labelling `W` with `val(U_o, W) >= 1/2 + gamma`;
* a list `Lambda` of at most `L` ARBITRARY outer labellings such that the
  projection `H` of `W` has `D^C_L(H, Lambda) <= gamma - gamma'`.

Then `Lang in RP`, with one-sided success `>= theta c0^C_L / 2` per trial. The
decoder is exactly the decoder of Theorem CL (the Step 0 decoder of
`efficient-branch-selectors-list-decode-honest-outer-labels`, with a guessed
seed label and threshold `gamma'/2`, and the B-rule
`hat lambda_b := pi_(a'b)(hat lambda_(a'))`, `a' ~ rho(.|b)`), with acceptance
threshold `c0^C_L / 2`.

**Corollary IMP (CL implies CLV).** Under (M) and (M_B), if every list member
has `val_Phi >= 1 - eps`, then
`D^C_L(H, Lambda) <= D_L(H, Lambda) + L K K1 eps`. So the hypothesis of
Theorem CL with slack `gamma'` gives the hypothesis of Theorem CLV with slack
`gamma' - L K K1 eps`. The converse fails: CLV accepts references of any value.

**Corollary DK^C (DKKMS).** On the DKKMS instances `(Phi_k, G_multi)` in the
form of `dkkms-2to1-instances-satisfy-selector-decoding-hypotheses` (A-vertex
`U`, seed `w = (V, L')`, B-vertex `V`):
* (Bw) holds with `b(V, L') = V`;
* (M_B) holds with `K1 <= 1/(1 - 2^(l-k)) <= 2` for `k >= l + 1`;
* (E_tau) with `tau = 2^(l-1-2k)` and (M) with `K = 1` hold as recorded there;
* (S^C_L) holds once `eps_k = exp(-k/exp(ql)) < p^2 gamma'^2 / (8 L^4)`, in
  particular for every

```text
L  <  (p gamma' / 3)^(1/2) exp( k / (4 exp(ql)) )
```

at large `k`. No condition on `eps_3` or on the value of the references is
needed.

**Corollary HON (honest encodings of arbitrary assignments).** On DKKMS, let
`y` be any assignment to the source variables, `lambda^y` its induced outer
labelling (`lambda_U = y|_U`, `lambda_V = y|_V`), `eps_out(y)` the mass of
`U` containing an equation violated by `y`, and `hon(y)` its honest inner
labelling. For every lift labelling with projection `H = (sigma, tau)`,

```text
D^C_1(H, lambda^y)  <=  eps_out(y)  +  mu( sigma_(p_e) != hon(y)_(p_e) ).
```

Hence a selector witness whose A-side agrees with the honest encoding of some
`y` outside a mass `z`, with `eps_out(y) + z <= gamma - gamma'`, is killed by
Theorem CLV, whatever `val_Phi(lambda^y)` is.

**Remark (what is and is not new on DKKMS).** With the certified smoothness
`beta = log log k / k` of `dkkms-certified-parameters-lie-in-the-selector-kill-regime`,
the canonical local-fix labelling of `y` (fix each violated equation of `U` by
flipping its first variable; on `V` apply the same fix on whole equations) has
`val_Phi = (1 - beta delta / 3)^k` when `y` violates a `delta` fraction of
disjoint equations. Check C gives losses `<= 1.1e-2` at `eps_out(y) <= 0.4`, and
the loss tends to `0` with `k`. So on DKKMS, Corollary HON is also reachable
from Theorem CL through a good local-fix reference at large `k` (its
`D(H, lambda')` is also `<= eps_out(y) + z`). What Theorem CLV adds there is that
no reference value has to be traded against `eps`, and that no local-fix
construction is needed. The gain is structural: in any composed instance where
`beta` is a constant (so local fixes lose `Theta(beta)` per violation), or
where witnesses are glued from references of value bounded away from `1`,
Theorem CL says nothing and Theorem CLV still applies.

## Consequence for H1

A counterexample to the constant-bias cell of H1 on an instance satisfying
(E_tau), (M), (Bw) and (M_B) must have `D^C_L(H, Lambda) > gamma - gamma'`
for EVERY list of `L` outer labellings, good or bad (with `L` up to the
Corollary DK^C budget on DKKMS). That is, on average over stars, every
labelling either mispredicts or breaks the outer constraint on more than a
`gamma - gamma'` part of the satisfied star. Escapes that explain the witness
by honest encodings of low-value assignments (domain-wall and near-kernel
encodings) are therefore closed.

The remaining prerequisite for the constant-bias cell is:

* **(Star-List^C)** every constant-bias selector witness on DKKMS admits a list
  of `L <= exp(o(k))` arbitrary outer labellings with
  `D^C_L(H, Lambda) <= gamma - gamma'`.

It is weaker than the Star-List prerequisite of Theorem CL (Corollary IMP).

**Status of (Star-List^C): likely false at small gamma, by a parallel lane.**
Near the end of this wave, the parallel lane swarm-0917-w15-w15-ugc-pull posted
node `dkkms-ev-list-structure-needs-lists-exponential-in-k` (not on this
branch). It has Lemma A: for a proper subspace `W` of `X` and `psi != 0`,
`Pr_(x in X \ W)[psi(x) = 0] <= 1/2`. On defect edges of rank-`(k-8)`
J-instances, therefore, every linear form other than the branch assignment's
predicts at most half. From this it derives list lower bounds
`t >= 2^(k-l-11)` at value `0.605` and `D > 0.110`.

Lemma A does not use the value of the reference. So if that witness's
branches at a fixed `U` range over `2^(Theta(k))` distinct linear forms, as the
bound indicates, the same count gives `D^C_L > 0.110` for every list of
`L < 2^(k-l-11)` ARBITRARY labellings. That is far above the budget
`exp(k/(4 exp(ql)))` of Corollary DK^C. This transfer has not been checked
against that node's proof here. If it holds, (Star-List^C) fails on DKKMS for
every `gamma <= 0.11`.

Theorem CLV then says something sharper about that failure: **reference value
was never the bottleneck.** The obstruction to the list route is branch
multiplicity per A-vertex, a count that value-free references cannot beat.
Routes that survive both results need one of the following:
* `gamma > 0.11`;
* sources without generic large-rank homogeneous kernels;
* a decoder whose loss is not polynomial in the list size (for example, one
  that guesses the branch from the seed, which is what Step 3 already does
  per star, but aggregated without the `1/L` pigeonhole).
