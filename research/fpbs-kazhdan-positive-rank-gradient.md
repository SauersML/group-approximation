---
rg: 2
id: fpbs-kazhdan-positive-rank-gradient
kind: claim
title: An infinite Kazhdan group has a Farber chain of positive rank gradient
root: true
---

OPEN counterexample-construction target. No such group or chain is constructed. It is kept separate from the positive universal fixed-price claim.

## Attempts

* **Build the certificate from mod-`l` homology.** Section 4 of
  `research/artifacts/fpbs/creative-branches.md` records a sufficient
  condition: a prime `l` and a Farber chain `Gamma_n` with
  `liminf_n dim_(F_l) H_1(Gamma_n;F_l)/[Gamma:Gamma_n] > 0`, since
  `d(Gamma_n)` is at least that dimension. Abert--Nikolov then makes the
  profinite boundary action have cost `1+lim_n (d(Gamma_n)-1)/[Gamma:Gamma_n]`,
  strictly above one, and `fpbs-kazhdan-groups-have-cost-one` supplies a
  cheaper action, so `fpbs-kazhdan-rankgradient-counterexample-reduction`
  closes. The certificate is stated with mod-`l` coefficients, not rational
  ones. **Where it dies:** no group and no chain are constructed. A candidate
  must hold three properties at once -- property (T), essential freeness of
  the profinite boundary action (for instance a normal chain with trivial
  intersection), and a genuinely positive asymptotic lower bound -- and the
  note states that large homology at finitely many levels, a chain that is not
  Farber, or a weighted presentation deficiency supplies none of the three.
* **Weaken the attainment requirement.** An earlier worry was that
  Hutchcroft--Pete give an infimum rather than a minimum. **Resolved, and it
  does not help:** infimal cost one already produces an action strictly
  cheaper than a positive-gradient boundary action, so no attainment theorem
  is needed. The difficulty is entirely in the construction, not in the
  comparison.
* **Look inside the known Kazhdan groups of this repository.** The property
  (T) region here is built for operator-algebraic questions and records
  finite generation (`discrete-kazhdan-groups-are-finitely-generated`) and
  residual-finiteness obstructions, not rank gradients of Farber chains.
  Nothing in it supplies a chain with the required asymptotic lower bound.
