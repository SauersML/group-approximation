---
rg: 2
id: amenable-free-actions-weakly-equivalent-to-bernoulli
kind: claim
title: For a countably infinite amenable group every free p.m.p. action is weakly equivalent to the Bernoulli shift
distinct_from:
  abert-weiss-free-actions-weakly-contain-bernoulli: that is one direction for every countable group, Bernoulli weakly contained in every free action; this is the reverse containment, which holds for amenable groups only.
  nontrivial-bernoulli-shifts-are-weakly-equivalent: that compares Bernoulli shifts with each other over any group; this says that over an amenable group every free action lies in the Bernoulli weak equivalence class.
---

**ESTABLISHED (import)** by [[amenable-free-actions-weakly-equivalent-to-bernoulli-citation]].

Let `Γ` be a countably infinite amenable group. Every free p.m.p. action of `Γ` on a standard probability space is
weakly equivalent to the Bernoulli shift `s_Γ = [0,1]^Γ`. Moreover every p.m.p. action of `Γ` on a non-atomic
standard probability space is weakly contained in `s_Γ`.

Source: Burton--Kechris, arXiv:1611.07921, Section 3, the paragraph after Theorem 3.6, which refers to Kechris,
*Global aspects of ergodic group actions*, page 91.

**Use here.** Over an amenable base, the quotient of any free action of a finite extension is a liftable free
action that is weakly equivalent to the Bernoulli shift. That settles the positive polarity of
`weakly-bernoulli-liftable-actions-force-virtual-splitting` without rigidity, as recorded in
`weakly-bernoulli-lifts-over-amenable-free-product-bases`.

**Model test.** The trivial group fails the hypothesis, and there the conclusion is false: the one-point space is
free but not weakly equivalent to anything nonatomic. For `Γ = F_2` the conclusion is false: an action whose
Koopman representation has almost invariant vectors is not weakly contained in `s_(F_2)`. So amenability is used.
