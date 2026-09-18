---
rg: 2
id: rbs-irs-strict-design-bridge-proof
kind: route
title: Run a strict design fibrewise as a Bowen–Chapman automaton, which is injective almost everywhere and misses an open set, and apply their RBS theorem
target: rbs-free-group-irs-carry-no-strict-design
requires:
  - bowen-chapman-rbs-irs-surjunctivity-toolkit
artifacts:
  - research/artifacts/rbs-irs-strict-design-bridge-2026-09-18.md
---

The complete proof is Lemma B and Theorem R of the artifact. Let `D = (tau, sigma)` have `eps_D(pi) = 0` and
`delta_D(pi) > 0`, and set `Phi(K, c) = (K, tau_K c)` on `Dom(pi)`.

1. **`Phi` is a Bowen–Chapman automaton.**
   - `Phi` is continuous: each output colour reads finitely many coordinates of `K` and of `c`.
   - `P o Phi = P` holds by construction.
   - `Phi` is conjugate invariant. The map `Kx -> wKx` is a label-preserving isomorphism from the Schreier
     graph of `K` to that of `wKw^-1`, carrying `c` to `w.c`, and shape-dependent automata commute with such
     isomorphisms.
2. **`Phi` is injective almost everywhere.** `eps_D(pi) = 0` gives `sigma_K tau_K = id` for `pi`-a.e. `K`.
3. **`Phi` is not surjective.**
   - Some root shape `s` of positive probability carries a reverse-bad pattern `p`. The set `O` of pairs with
     shape `s` and pattern `p` at the root is open and has positive `u_pi`-measure.
   - `Phi` hits `O` only over forward-bad `K`, a null set. `Phi^-1(O)` is open, and `supp(u_pi) = Dom(pi)`, so
     `Phi^-1(O)` is empty. Thus `Phi` misses `O`.
4. **Conclusion.** By Bowen–Chapman Theorem 3.6 an RBS IRS is surjunctive, and `Phi` contradicts that.
