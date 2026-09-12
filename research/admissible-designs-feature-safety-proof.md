---
rg: 2
id: admissible-designs-feature-safety-proof
kind: route
title: Invert the feature-transparency lower bound against admissible-design soundness
target: admissible-pairing-designs-leak-no-easy-feature
requires: [noise-test-transparent-on-decodable-matching-features, noise-test-sound-on-smooth-design-rich-inputs]
---

`noise-test-sound-on-smooth-design-rich-inputs` shows that BKM's Section 5
soundness argument applies to admissible-design instances with `n >= n_0`. So
`val(Psi) <= eta` implies `val(R_(rho,m)(Psi)) <= epsilon`.

`noise-test-transparent-on-decodable-matching-features` gives
`val(R_(rho,m)(Psi)) >= 1/m + (1-1/m) rho^3 val(Psi_c)^2 - 2 e_c` for every
decodable feature `c`. Chaining the two,

```text
(1-1/m) rho^3 val(Psi_c)^2 <= epsilon - 1/m + 2 e_c <= epsilon + 2 e_c.
```

This is the stated bound. It holds for every `c`, so a feature with
`e_c = o(1)` and an easy split game on a low-value admissible instance would
contradict soundness. The statement about outer PCPs restates the hypothesis of
`ugc-from-smooth-design-rich-2to1`: after this corollary, no feature condition
remains beyond admissibility and 2-to-1 soundness.
