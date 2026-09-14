---
rg: 2
id: prime-field-stable-formalizability-specializes-to-binary
kind: route
title: Stable formalizability of every left-inverse pair at p = 2 gives a formal stabilized left inverse for every injective binary automaton
target: injective-binary-automata-are-stably-formalizable
requires:
  - prime-field-left-inverse-pairs-are-stably-formalizable
artifacts:
  - research/artifacts/formalizability-prime-fields-and-alphabet-bridge-2026-09-12.md
---

Let `tau` be injective on `(F_2^n)^G`.

1. By compactness `tau` has a left-inverse automaton `sigma`.
2. The prerequisite at `p = 2` gives `k` with `(tau (+) id_k, sigma (+) id_k)` formalizable.
3. So `tau x id` on `(F_2^(n+k))^G` has the left inverse `sigma (+) id_k` with a formal identity, which is
   the target with `m = k`.

The target allows any left inverse of the stabilized automaton, so it is the weaker statement. The binary
case lives on the target, owned by lane gk-free-neg; the prerequisite adds the odd primes.
