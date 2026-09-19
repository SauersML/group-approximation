---
rg: 2
id: list-reference-constant-bias-decoding-loses-t-squared
kind: claim
title: Theorem C of the constant-bias cell survives a per-seed list of t good outer references at the cost of a factor t^-2 in the outer soundness it needs, while its seed form pays an exactly sharp collision term min(t, 2^l - 1)/(2^l - 1), so on Grassmann tests the list prerequisite must have t below gamma 2^l, not merely 2^O(l)
distinct_from:
  constant-bias-selectors-need-seed-dishonest-witnesses: that is the single-reference Theorem C and Lemma F (t = 1); this is its list rerun, asked for as part (b) of need 4a85435f, with the loss computed exactly and the seed-form collision term shown sharp.
  dkkms-list-seed-needs-lists-exponential-in-l: that proves every list must have t >= 2^(l-6) on J-instances; this shows the seed form of the rerun is vacuous once t >= 2^l - 1, so the surviving window for (List-Seed) is 2^(l-6) <= t < gamma 2^l, and moves the target to the ev-form (List-Str_t), where t = 2^O(l) costs only soundness.
  efficient-branch-selectors-list-decode-honest-outer-labels: that is the seed-guessing Fourier decoder with one planted outer labelling; this runs the same decoder against a seed-dependent choice among t labellings and extracts one of them by averaging.
  parity-leaking-branch-selectors-reach-near-perfect-completeness: that is the OPEN hole H1; this narrows the prerequisite of the kill of its constant-bias cell and settles the list-decoding half of the prerequisite pair.
artifacts:
  - experiments/ugc-list-rerun-2026-09-17/check_list_lemma_f.py
---

**ESTABLISHED.** Route: `list-reference-constant-bias-decoding-loses-t-squared-proof`.
Conditional on `NP not in RP` in the same way as its parent Theorem C.

## Setting

Notation and hypotheses (E_tau), (M), (Sep_kappa) are those of
`constant-bias-selectors-need-seed-dishonest-witnesses` (a doubled LEC with
outer game `Phi = (A, B, rho, pi)`, inner 2-to-1 game `G` on `P x Q`, law `mu`,
annotations `(a_e, x_e, ev_e)`, seed `w_e = q_e`, seed alphabet `<= 2^l`).

A **t-list** for a labelling `H = (sigma, tau)` of `G` is a family
`Lambda = ((lambda^i, H0^i))_(i <= t)`, each `lambda^i` an outer labelling
with `val_Phi(lambda^i) >= 1 - eps` and each `H0^i = (sigma^i, tau^i)` a
`lambda^i`-reference of defect `<= r`, together with a **covering map**
`i : Q -> [t]`, any map with `tau_q = tau^(i(q))_q` whenever some index
satisfies this (arbitrary otherwise). Put

* `beta(H, Lambda) := mu{ e in Sat(H) : tau_(q_e) != tau^j_(q_e) for all j }`
  (uncovered satisfied mass);
* `D(H, Lambda) := mu{ e in Sat(H) : ev_e(sigma_(p_e)) != <lambda^(i(q_e))_(a_e), x_e> }`
  (list-ev-dishonest satisfied mass; it contains the uncovered satisfied edges
  that happen to be dishonest).
* `c_t(p) := max` over `sigma in Sigma_p` and sets `T` of at most `t` labels
  of `Pr_e[ exists sigma' in T \ {sigma}: pi_e(sigma') = pi_e(sigma) | p_e = p ]`,
  and `kappa_t := E_(mu_P) c_t(p)`. Always `kappa_t <= min(1, t kappa)`.

## Statements

**Lemma F_t (list Lemma F).** For every `H`, every t-list and every covering map,

```text
D(H, Lambda)  <=  beta(H, Lambda) + t r + kappa_t .
```

For Grassmann 2-to-1 tests (labels are functionals on an `l`-space `L`,
constraints restrict to a uniform hyperplane `L'`),
`kappa_t = min(t, 2^l - 1)/(2^l - 1)`, and this is **sharp**: for every `L`,
every `sigma` and every `t <= 2^l - 1` there are `t` honest references
(`r = 0`) and seeds on the hyperplanes of `L` such that, conditional on
`p_e = L`, the uncovered satisfied mass is `0` and the covered ev-dishonest
satisfied mass is exactly `t/(2^l - 1)`.

**Theorem C_t (list constant-bias decoding).** Let `x -> D(x)` be a doubled
LEC for `Lang` with (E_tau), `tau <= gamma'/4`, (M), and

* **(S_t)** on NO inputs `val(Phi) <= s < c_t0/2`, where
  `p = gamma'^3 2^(-l-2)` and `c_t0 := p^2/(t^2 K^2) - 2 eps`.

Suppose that on YES inputs

* **(List-Str_t(gamma, gamma', eps))** every labelling `H` of `G` with
  `val_G(H) >= 1/2 + gamma` has outer labellings `lambda^1..lambda^t` of value
  `>= 1 - eps` and a map `i : Q -> [t]` (any map; no references are needed in
  this form) with `D(H, Lambda) <= gamma - gamma'`, `D` defined by the same
  formula.

Then any randomized polynomial-time orientation selector `S` with
`Pr_S[val(U_(S(x))) >= 1/2 + gamma] >= theta >= 1/poly` on YES inputs puts
`Lang` in RP, with one-sided success `>= theta c_t0/2` per trial. The decoder
is literally the one of the parent node; only the analysis changes.

**Corollary C_t' (seed form).** Under (Sep_kappa), List-Str_t follows from

* **(List-Seed_t)** every `H` with `val_G(H) >= 1/2 + gamma` has a t-list of
  defect `r` with `beta(H, Lambda) + t r + kappa_t <= gamma - gamma'`.

On Grassmann tests this needs `t < (gamma - gamma')(2^l - 1)`, and it is
**vacuous for `t >= 2^l - 1`** (the bound on `D` becomes `>= 1`).

## What it does (impact types 2 and 3)

* **Part (b) of need 4a85435f is settled.** The list-decoding rerun of Theorem
  C holds with loss `t^(-2)` in the outer value, hence `2^(-O(l))` for
  `t = 2^(O(l))`, entering only through (S_t). The single-reference theorem is
  the case `t = 1`.
* **Part (a) splits sharply.** In ev-form, (List-Str_t) with `t = 2^(O(l))`
  is the one remaining selector-free prerequisite of the kill of the
  constant-bias cell (together with (S_t), a pure outer-soundness condition).
  In seed form, the collision term `kappa_t` is exactly `t/(2^l - 1)`, so the
  class of seed-only list statements with `t >= gamma 2^l` is dead: every
  member dies at the counting step of Lemma F_t, because `t` references whose
  restrictions to `L` are the `t` partners `sigma + psi_j` of an A-label
  `sigma` make `sigma` satisfied and ev-dishonest on exactly the `t`
  hyperplanes `ker psi_j`. **Invariant:** the number of distinct list
  restrictions at an A-vertex, against `2^l - 1`.
* **Window.** Combined with Theorem LS of
  `dkkms-list-seed-needs-lists-exponential-in-l` (lists `t >= 2^(l-6)`, and
  `t_min ~ 0.026 2^l` at `gamma ~ 0.11`), the seed route to the constant-bias
  kill survives only for list sizes in `[2^(l-6), gamma 2^l)`: a window of
  constant multiplicative width `64 gamma` around `2^l`. On LS's own family the
  `2^s = 2^l` covering references are exactly at the vacuous end, so LS's
  labelling must be handled in ev-form. Its A-labels are honest unfoldings of
  branch assignments from the same list (Theorem LS item 1), which suggests
  that it satisfies (List-Str_(2^l)) with small `D`; this is not checked here.
* **Reference defect.** The term `t r` needs references of defect below
  `gamma/t`, i.e. honest encodings with inner incompleteness and outer
  violation `o(2^(-l))` when `t ~ 2^l`. Whether DKKMS parameters permit this
  (outer completeness slack `eps` chosen after `l`) is not checked here.

This neither proves nor refutes UGC.
