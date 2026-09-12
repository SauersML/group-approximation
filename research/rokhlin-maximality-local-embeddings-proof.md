---
rg: 2
id: rokhlin-maximality-local-embeddings-proof
kind: route
title: Transport a deficit configuration along an injective partial multiplication table
target: rokhlin-maximality-closed-under-local-embeddings
requires: [bernoulli-rokhlin-deficit-has-a-finitary-witness]
artifacts:
  - research/artifacts/kun-thom-wreath-rokhlin-test-case-2026-09-12.md
---

Section 2 of the artifact.

1. **Pattern.** By the prerequisite, `Φ(k, E, F, ψ)` depends only on the map `(f, e) -> fe`, on which
   products coincide, and on which equal `1`.
2. **Table.** Put `S = {1} ∪ E ∪ F ∪ FE` and take an injective partial multiplication map `η: S -> K`.
   Then `η(1) = 1` because `η(1)^2 = η(1)`, and `η(f)η(e) = η(fe)`.
3. **Same pattern.** Injectivity makes `η(f)η(e) = η(f')η(e')` exactly when `fe = f'e'`, and
   `η(f)η(e) = 1` exactly when `fe = 1`. So the configuration `(k, η(E), η(F), ψ)`, with relabelled
   coordinates, has the same `Φ`.
4. **Conclusion.** A deficit over `H` gives a deficit over `K`. If every `K` in the class is maximal,
   `H` is maximal.
