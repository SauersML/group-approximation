---
rg: 2
id: bowen-chapman-rbs-irs-surjunctivity-toolkit
kind: claim
title: Invariant random subgroups with maximal relative Rokhlin entropy of Bernoulli bundles are surjunctive, and cosofic ones have it
distinct_from:
  surjunctive-nonsofic-group-exists: that cites Bowen–Chapman only for Problem 1.1 and the group question; this imports their IRS definitions, the RBS criterion and the theorems RBS implies surjunctive and cosofic implies RBS.
  co-sofic-free-group-irs-carry-no-strict-design: that proves the co-sofic case by counting on finite Schreier graphs, with a linear bound; this imports an entropy criterion that covers the co-sofic IRS and some non-co-sofic ones, with no bound.
artifacts:
  - research/artifacts/rbs-irs-strict-design-bridge-2026-09-18.md
---

**ESTABLISHED (literature import).** The route is `bowen-chapman-rbs-irs-surjunctivity-citation`. The
quotes below come from L. Bowen and M. Chapman, *Surjunctivity does not characterize cosoficity of invariant
random subgroups*, arXiv:2511.06586v1. The HTML version was fetched on 2026-09-18, its tags were stripped, and
its MathML was replaced by its alttext. Here `\mathcal{F}` is a finitely generated free group.

- **Setting.** `sub(F, Sigma)` consists of the pairs `(K, c)` with `K <= F` and `c : F -> Sigma` satisfying
  `k.c = c` for `k in K`. `Dom(pi)` is the set of such pairs with `K in supp(pi)`, and `P` is the projection
  to the first coordinate. To sample `u_pi`, first sample `K ~ pi`, then colour each right coset `Kw`
  independently and uniformly.
- **Definition 1.5.** "A function $\Phi\colon{\rm Dom}(\pi)\to{\rm Dom}(\pi)$ is a cellular automaton on $\pi$
  (with color palette $\Sigma$ ) if it is continuous, conjugate invariant (i.e.,
  $w\Phi w^{-1}(K,c)=\Phi(K,c)$ for every $(K,c)\in{\rm Dom}(\pi)$ and $w\in\mathcal{F}$ ) and $P\circ\Phi=P$"
- **Definition 1.6.** "A $\pi\in{\rm IRS}(\mathcal{F})$ is surjunctive if every (almost everywhere) injective
  $\pi$ -cellular automaton must be surjective."
- **Remark 1.7.** "${\bf 1}_{N}$ is surjunctive as in Definition 1.6 if and only if
  $\nicefrac{{\mathcal{F}}}{{N}}$ is a surjunctive group."
- **Definition 3.5.** "Let $\pi$ be an IRS supported on infinite index subgroups . We say that $\pi$ satisfies
  the Rokhlin entropy of Bernoulli Shifts (RBS) criterion if
  $H_{\rm Rok}(\mathcal{F}{\curvearrowright}(\mathfrak{sub}(\mathcal{F},\Sigma),u_{\pi})|P)=H(u)=\log|\Sigma|$
  for every finite base $\Sigma$ equipped with the uniform probability distribution $u$ . We will say that a
  general IRS $\pi$ (not necessarily supported on infinite index subgroups) satisfies RBS if its infinite
  component $\pi_{\infty}$ (as in Fact 3.1 ) does."
- **Theorem 3.6.** "If an IRS satisfies the RBS criterion (Definition 3.5 ), then it is surjunctive
  (Definition 1.6 )."
  - Its proof ends: "Since $\Phi$ is continuous, its image agrees with
    ${\rm supp}(\mu)={\rm supp}(u_{\pi})={\rm Dom}(\pi)$ and it is thus surjective."
- **Fact 3.7 (1).** "Surjunctivity is preserved under convex combinations : If $\pi_{1}$ and $\pi_{2}$ are
  surjunctive (Definition 1.6 ), then every convex combination of $\pi_{1}$ and $\pi_{2}$ is also surjunctive."
- **Theorem 5.3 (excerpt).** "In particular, ${\rm IRS}_{\rm RBS}(\mathcal{F})$ is weak* closed."
- **Corollary 5.4.** "Every cosofic IRS (Definition 1.4 ) satisfies the RBS criterion (Definition 3.5 )."
- **Theorem 1.2.** "There exists a surjunctive non cosofic IRS of a finitely generated free group."
