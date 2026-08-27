---
rg: 2
id: sofic-semidirect-product-closure-fails
kind: claim
title: Soficity is not closed under semidirect products of sofic groups
invalidates: [linton-shell-sofic-via-generic-semidirect-closure]
distinct_from:
  kun-thom-nonsofic-wreath: that records the external theorem and its explicit Kazhdan pair, with the infranormality hypothesis and the realizing family; this is the one permanence consequence drawn from it — a closure property of the class of sofic groups — stated so that routes assuming that closure can be killed by reference rather than by re-deriving the counterexample.
  relative-soficity-extension-theorem-withdrawn: that is a bibliographic fact about an unavailable claimed theorem; this is a refutation, with counterexamples in hand. A route killed by that one might still be true; a route killed by this one is false.
  sofic-radical-soficization: that concerns the sofic radical construction and what soficization does to a group; this is a bare closure-failure statement about semidirect products and involves no radical.
artifacts:
  - research/artifacts/one-relator-soficity-audit-2026-08-17.md
---

ESTABLISHED, as a corollary of [[kun-thom-nonsofic-wreath]].  There exist
groups `N` and `Q`, both sofic, and an action `α : Q → Aut(N)`, with

    N ⋊_α Q   not sofic .

Indeed one may take `N` **amenable** and `Q` **residually finite**: Kun--Thom's
Theorem A gives an infranormal non-normal Kazhdan pair `Γ < G` for which

    ( ⊕_{G/Γ} Z/2Z ) ⋊ G

is not sofic, and by their Theorem E the acting group `G = EL_r(R) ⋊ SL_d(Z)` is
residually finite, hence sofic, while the lamp group `⊕ Z/2Z` is abelian, hence
sofic.  ∎

So there is no blanket theorem "`N` sofic and `Q` sofic implies `N ⋊ Q` sofic",
and none is coming: the failure is not marginal but sits at the strongest
available hypotheses on both factors.

## Why it is stated separately from the source theorem

Because it is the form the rest of this graph consumes, and because the gap
between the two statements is where mistakes happen.  Reading Kun--Thom as "some
exotic wreath products are nonsofic" invites the thought that a *tame* semidirect
product — say, one with a **free** acting group — is safe by default.  It is
not safe by default; it is merely not refuted.  Any route that wants soficity of
a semidirect product must produce the models, or invoke a permanence theorem
whose hypotheses are checked, not assume closure.

That is exactly the discipline the Linton shell needs.
[[one-relator-soficity-localizes-at-rational-derived-stage]] delivers
`E ≅ R ⋊_α F₀` with `F₀` free; the temptation is to declare `E` sofic the moment
`R` is, and this claim is the reason that is illegal.  The route it kills is
[[linton-shell-sofic-via-generic-semidirect-closure]].

## What is left standing

A theorem restricted to **free** acting groups is not excluded by anything
here — Kun--Thom's acting groups have property (T) and are about as far from
free as a group gets, and no counterexample with free `Q` is known.  Such a
theorem would settle [[linton-shell-sofic]] and hence, with the reduction, all
of Pestov's Question 4.9.  Note what that means: proving generic
"free-acting-group semidirect closure" is at least as hard as the whole
question, so it is a target and not a lemma.  The realistic conditional form is
the Alekseev--Bradford one — soficity of the *action*, not just of the factors —
which is what [[linton-radical-free-action-sofic]] asks for.
