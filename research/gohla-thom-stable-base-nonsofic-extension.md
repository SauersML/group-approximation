---
rg: 2
id: gohla-thom-stable-base-nonsofic-extension
kind: claim
title: Gohla--Thom — cosystolic base stable in finite actions forces a nonsofic central extension
distinct_from:
  kun-thom-nonsofic-wreath: that is the unconditional infranormal-compression theorem; this is a conditional stability-to-nonsoficity theorem with a cohomological engine and a cosystolic hypothesis
  literal-group-not-sofic: that asks whether this repository's literal group E is nonsofic; this is the external conditional theorem one route tried to invoke for it, and its hypotheses do not transfer
artifacts:
  - notes/LITERAL_GROUP_BLOCK_AMALGAM_STRUCTURE_2026-08-14.md
---

**Primary source, read from the PDF (2026-08-14):** Gohla--Thom,
*High-dimensional expansion and soficity of groups*, arXiv:2403.09582v2.
The main result is their **Theorem 3.13**, not "Theorem 1.5" (that number
belongs to the secondary source Chapman--Dikstein--Lubotzky,
arXiv:2410.02913, where it appears as a corollary specialized to the p-adic
Deligne extension).

> **Theorem 3.13.** Let `Gamma` be a countable discrete group and `A` be a
> finite abelian group.  Assume the following conditions:
> (i) `Gamma` is residually finite and of finite type,
> (ii) `Gamma` satisfies a co-systolic inequality for all finite transitive
> actions with coefficients in `A` and dimension 2,
> (iii) there exists a central extension `Gamma~` of `Gamma` by `A` which is
> not residually finite.
> Then, the following implication holds: If `Gamma` is stable in finite
> actions, then the group `Gamma~` is not sofic.

**The stability notion is their own and is very weak.**

> **Definition 3.7.** We say that a group `Gamma` is *stable in finite
> actions* if the limit action of any sofic approximation is weakly contained
> in the family of finite `Gamma`-actions.  Equivalently, the limit action of
> any sofic approximation of `Gamma` is contained in a metric ultraproduct of
> finite `Gamma`-actions.

They note that any weakly flexibly stable group is stable in finite actions
(Lemma 3.6 and the following remark), and describe the notion as "much weaker
than any other notion of stability that has been studied so far".  It is a
**permutation/Hamming** notion throughout — no Hilbert--Schmidt variant is
involved anywhere in the paper.

**Proof engine.** Let `alpha in H^2(Gamma,A)` classify `Gamma~`.  If `Gamma~`
is sofic with limit action `Q` and `P=Q^A` the induced limit `Gamma`-action,
then `theta_*^P(alpha)=0` by their Theorem 3.4; if `Gamma` is stable in finite
actions then `P` is weakly contained in finite actions and
`theta_*^P(alpha)!=0` by their Theorem 2.16.  Contradiction.  **Theorem 2.16
is where hypothesis (ii) is consumed** — the cosystolic inequality is what
makes the cohomological obstruction non-vanishing on finite actions.

**Hypothesis (ii) is the whole content and is not generic.** It is supplied
for torsionfree lattices in `PSp_(2d)(Q_p)`, `d>=4` and `p` large, by the
high-dimensional expansion results of Kaufman--Kazhdan--Lubotzky and
Evra--Kaufman for the quotient of the Bruhat--Tits building; hypothesis (iii)
is Deligne's non-residually-finite central extension.  A group with no such
geometry has no reason to satisfy (ii).

## The tempting general statement is FALSE

Chapman--Dikstein--Lubotzky, arXiv:2410.02913, state and refute it directly:

> "It is very tempting to try to prove that in a situation like (1.1), if
> `Gamma` is stable, then also its finite central extension `Gamma~`.  This
> would imply immediately that `Gamma~` is non-sofic, as sofic stable groups
> are residually finite [GR09].  In Section 4, we will show that this does not
> hold in general: We present an exact sequence similar to (1.1), where
> `Gamma` is replaced by some other group (the lamplighter group), which is
> stable [LL22], but the central extension there is non-stable.  The example
> there is finitely generated but infinitely presented — see Section 4.  We do
> not know if this is possible with finitely presented groups."

So **stability does not pass from a base to its central extension**, and the
finitely presented case is explicitly open.  That gap is precisely why
Gohla--Thom need the cohomological machinery at all.
