---
rg: 2
id: kl-via-acyclic-torus-amalgam-schur-injectivity
kind: route
title: Schur injectivity over acyclic torus amalgams turns any coefficient kill into a contradiction
target: kervaire-laudenbach-nonsingular-conjecture
requires: [acyclic-torus-amalgam-adjunctions-kill-no-schur-class, kl-counterexample-can-be-acyclic, kl-failure-yields-a-schur-kill]
---

Suppose the conjecture fails.

1. `kl-counterexample-can-be-acyclic` gives a countable acyclic `Y`, a
   nonsingular `w in Y * <t>`, and `1 != a in Y` dying in `Y_w`.
2. `kl-failure-yields-a-schur-kill`, applied with `G = Y`, gives a nonzero
   class of `H_2(Y *_(<a>) (<a> x Z))` that dies in the adjunction at the same
   `w`.
3. That contradicts `acyclic-torus-amalgam-adjunctions-kill-no-schur-class`.

This route has the same shape as `kl-via-universal-schur-injectivity`, but its
premise is equivalent to the conjecture rather than a possibly stronger
statement. The converse direction is recorded as the established theorem
`kl-iff-acyclic-torus-amalgam-schur-injectivity`, not as a route, so no new
dependency cycle through the root is created.
