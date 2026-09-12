---
rg: 2
id: strict-composites-have-strict-factors-proof
kind: route
title: Induct from the right, since a surjective last factor passes injectivity and the image to the rest
target: strict-composites-have-strict-factors
requires: []
artifacts:
  - research/artifacts/radu-lattice-strict-automaton-screens-2026-09-12.md
  - research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md
---

## Why sufficient

Section 2 of the artifact, Lemma 2.

- If `tau = tau_1 ... tau_k` is injective, then `tau_k` is injective.
- If `tau_k` is not surjective, it is the strict factor.
- Otherwise `tau_k` is a bijection. Suppose `tau_1 ... tau_(k-1)` identifies `u = tau_k(w)` and
  `u' = tau_k(w')`. Then `tau(w) = tau(w')`, so `w = w'` and `u = u'`. So `tau_1 ... tau_(k-1)` is
  injective and has the same image as `tau`.
- Induction on `k` gives both statements.

**Verification (w3-vf-nonlinear, 2026-09-12): PASS.** Re-derived independently, including the
consequence that memories in surjunctive subgroups give surjunctive factors, acting coset by coset
(`research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md`, Section 5.1).
