---
rg: 2
id: leavitt-unit-group-has-positive-rokhlin-entropy-action
kind: claim
title: The binary Leavitt unit group admits a free ergodic action of positive Rokhlin entropy
refuted_by:
  - leavitt-unit-group-nonsurjunctive
artifacts:
  - research/artifacts/rokhlin-entropy-self-copy-dichotomy-2026-09-12.md
---

**OPEN.** Let `U = L_(F_2)(1,2)^x`. Some free ergodic p.m.p. action of `U` on a standard probability space has positive Rokhlin entropy.

By `positive-rokhlin-entropy-makes-leavitt-units-surjunctive`, this would make `U` surjunctive and `K[U]` directly finite for every field `K`. It would also give `h^Rok(L^U, lambda^U) = H(L, lambda)` for every base. It is equivalent to the Bernoulli 2-shift over `U` having positive Rokhlin entropy.

## Attempts

* **Sofic entropy.** Every known lower bound for Rokhlin entropy passes through sofic entropy (Seward, arXiv:1501.03367v4, introduction). `U` is not sofic (`openai-leavitt-unit-nonsofic`), so there is no sofic approximation to run it on.
* **Restriction to subgroups.** If `H <= U` is sofic and `X` is a free ergodic `U`-action, a generating partition for `H` also generates for `U`. So `h^Rok_U(X) <= h^Rok_H(X)`, and positive entropy of the restriction bounds nothing from below.
* **Co-induction.** Co-inducing a positive-entropy action of a sofic subgroup gives a free `U`-action with a generator of the base's entropy. That is again only an upper bound.
* **Small free factors.** Every free action has free factors of arbitrarily small Rokhlin entropy (Seward–Tucker-Drob). This is consistent with both answers.
* **The dichotomy.** `rokhlin-supremum-dichotomy-with-centralized-self-copies` makes entropy over `U` all or nothing, but it supplies no existence mechanism. Nonsoficity does not decide the question, since surjunctive nonsofic groups exist (`surjunctive-nonsofic-group-exists`).
