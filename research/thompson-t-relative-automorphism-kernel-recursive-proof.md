---
rg: 2
id: thompson-t-relative-automorphism-kernel-recursive-proof
kind: route
title: An automorphism acts trivially exactly when it changes each free generator by a mixed identity, which is decidable for T
target: thompson-t-relative-automorphism-actor-kernel-is-recursive
requires:
  - thompson-t-mixed-identity-problem-is-decidable
artifacts:
  - research/artifacts/solve-mixed-identity-undecidable-2026-09-13.md
---

**Step 1 (the kernel).** A homomorphism `φ in X` fixes `T` and is determined by
`(φ(x_1), ..., φ(x_n))`. Every tuple in `T^n` occurs. An automorphism `α in A`
fixes `T`, so `φ∘α = φ` iff `φ(α(x_i)) = φ(x_i)` for every `i`. As `φ` ranges
over all substitutions `x -> (g_1, ..., g_n) in T^n`:

```text
α in K   iff   α(x_i) x_i^-1 in J_n(T)   for i = 1, ..., n.              (KR1)
```

BFFHZ (arXiv:2503.21882v2, extracted text on MSI, l.465–467) state the same
description: the kernel "consists of all automorphisms α ... such that α sends
each x_i to itself times a mixed identity".

**Step 2 (computing images).** Take a word `u` in the finite generating set.
The images `α_u(x_i)` are words in `T * F_n`, computed by repeatedly
substituting the given generator images for the letters `x_j`. Letters from `T`
are left unchanged.

**Step 3 (deciding).** By `thompson-t-mixed-identity-problem-is-decidable`, with
`k = n`, decide whether each `α_u(x_i) x_i^-1` lies in `J_n(T)`. By (KR1), this
decides `α_u in K`, which is the word problem of `A/K` on the images of the
generators. `∎`

**Remark.** Finite generation is not an extra hypothesis. BFFHZ recall that
"Aut (G ∗ F ) itself is finitely presented" for their finitely presented simple
`G` (l.694–695). The procedure is uniform in the given generator images.
