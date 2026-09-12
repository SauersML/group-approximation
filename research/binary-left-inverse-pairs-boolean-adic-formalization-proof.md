---
rg: 2
id: binary-left-inverse-pairs-boolean-adic-formalization-proof
kind: route
title: Kill the Jacobian by Lemma C, then solve the correction equation one Boolean-adic degree at a time
target: binary-left-inverse-pairs-are-boolean-adically-formalizable
requires:
  - formalizability-is-a-boolean-ideal-cokernel-class
  - formalizability-conormal-obstruction-is-jacobian-cokernel
  - binary-left-inverse-pairs-need-not-be-formalizable
artifacts:
  - research/artifacts/formalizability-obstruction-class-2026-09-12.md
---

Section 5 of the artifact.

1. **Lemma C representative.** By item 5 of
   `formalizability-conormal-obstruction-is-jacobian-cokernel`, some encoder
   representative has `J_B = I`. Then `hat tau^*(u_h) == u_h` modulo `I^2`.
2. **Graded layers.** The `u_h` are a regular sequence in every finite set of variables,
   so `gr_I R = B[U_h]`. With `J_B = I`, `hat tau^*(u^alpha) == u^alpha` modulo
   `I^{k+1}` for every degree-`k` monomial, so `gr_k(hat tau^*)` sends `b [u^alpha]` to
   `tau^*(b) [u^alpha]`. `sigma o tau = id` makes `tau^*` onto; if `tau` is bijective,
   `tau^*` is bijective. This proves item 1.
3. **Iteration.** Put `eps_1 = eps in I`. Given `eps_k in I^k`, write its class at the
   base cell as a finite sum `sum_alpha b_alpha [u^alpha]` and take
   `delta_k = sum_alpha r_alpha u^alpha`, with `r_alpha` a finite-memory lift of
   `sigma^*(b_alpha)`, extended equivariantly. Since `tau^* sigma^* = id`,
   `eps_{k+1} := eps_k - hat tau^*(delta_k) in I^{k+1}`. `hat tau^*` preserves the
   `I`-adic filtration, hence is continuous, so
   `hat tau^*(sum_k delta_k) = sum_k (eps_k - eps_{k+1}) = eps`. If `tau` is bijective,
   `gr(hat tau^*)` is injective in each degree, so `hat tau^*` is injective on the
   completion of `I` and the solution is unique. This proves item 2.
4. **Termination.** By `formalizability-is-a-boolean-ideal-cokernel-class`, with this
   encoder representative the pair is formalizable iff a finite-memory polynomial
   solution exists. A polynomial solution is an `I`-adic solution, so item 3 follows.
5. **Marker involution.** It is bijective, so for each Lemma C representative the
   Boolean-adic solution is unique. By `binary-left-inverse-pairs-need-not-be-formalizable`
   no representatives formalize it, so that unique solution is not a finite-memory
   polynomial. This proves item 4.
