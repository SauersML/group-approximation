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
* **Force the gradient with a presentation of positive power p-deficiency**
  (Schlage-Puchta, Osin). Such a presentation gives positive `p`-gradient even
  with infinitely many relators or with torsion, and the residual pro-`p`
  image of a Kazhdan example would satisfy this claim
  (`fpbs-kazhdan-gradient-via-power-p-deficiency`). **Dead:**
  `fpbs-power-p-deficiency-excludes-property-t` proves that no such group is
  Kazhdan. Openness of (T) gives a Kazhdan finitely presented truncation of
  positive power deficiency, and Lackenby makes that truncation `p`-large.
  Weighted Golod-Shafarevich presentations are not excluded, since Kazhdan
  Golod-Shafarevich groups exist, but they give no lower bound on ordinary
  rank.
* **Necessary condition for the mod-`l` certificate: exponential subgroup
  growth.** Suppose `dim H_1(Gamma_n;F_l) >= c[Gamma:Gamma_n]`. The index-`l`
  normal subgroups of `Gamma_n` give at least `(l^(c m_n)-1)/(l-1)` subgroups
  of index `l m_n` in `Gamma`, where `m_n=[Gamma:Gamma_n]`. So
  `limsup_N log s_N(Gamma)/N >= c log(l)/l > 0`. Any candidate must therefore
  be a Kazhdan group of at least exponential subgroup growth. Ershov's survey
  (IJAC 2012, Section 14, discussion of Problem 6) records that no such
  Kazhdan group was known, and expects that the Kazhdan Golod-Shafarevich
  groups have subexponential growth. The status after 2012 was not rechecked
  here.
* **Where a candidate can still come from.** It must be residually finite and
  infinitely presented whenever the chain is a cofinal `p`-chain: for a
  finitely presented Kazhdan group, positive `p`-gradient contradicts Lackenby
  just as above. Non-cofinal chains and non-`p`-power chains are not excluded.
  Lackenby's (tau) dichotomy (arXiv:math/0509036) allows linear mod-`p` growth
  along a chain with respect to which (tau) holds.
