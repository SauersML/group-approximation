---
rg: 2
id: self-similar-hilbert-cx-module-has-unit-section
kind: claim
title: A Hilbert C(X)-module isomorphic to its double, with nonzero fibres, has a unit section and a properly infinite projection
distinct_from:
  euler-class-protection-fails-for-o2-self-similar-modules: that assumes two orthonormal sections and kills Euler-class protection; this proves that a unit section always exists, so the assumption is automatic.
---

Let `X` be compact Hausdorff and `E` a Hilbert `C(X)`-module with `E ≅ E ⊕ E` and every fibre `E_x` nonzero.

1. `E` has a nowhere-vanishing section, hence a unit section `ξ`. The words `S_w ξ` with `|w| = k` then
   give `2^k` orthonormal sections for every `k`.
2. Let `E` be countably generated and `P_E` its projection in `M(C(X) ⊗ K)`, which exists by Kasparov
   stabilization. Then `P_E` is properly infinite.
3. `E ≅ H_X` iff `P_E ~ 1` iff `P_E` is full in `M(C(X) ⊗ K)`. In that case `K(E) ≅ C(X) ⊗ K` is stable,
   and the unitization of `K(E)` is K1-injective.

So the section hypothesis of `euler-class-protection-fails-for-o2-self-similar-modules` holds automatically.
A witness ideal `I = K(E)` over a commutative base for `o2-multiplier-ideal-with-non-k1-injective-unitization`
requires a properly infinite, non-full projection in `M(C(X) ⊗ K)` whose fibres are all nonzero.
- Whether such a projection exists is a converse to the corona factorization property question: CFP asks
  whether full projections are properly infinite.
- For finite-dimensional `X` no such projection exists, by Dixmier--Douady.
- For infinite-dimensional `X` the question is open here. It is now the open claim
  `properly-infinite-nonzero-fibre-projection-is-full` (lane ex2-k1-defect-ideal).
- `nonzero-fibre-projection-full-under-weak-omega-comparison` proves fullness whenever `Cu(C(X))` has
  weak ω-comparison. The proof uses Ortega--Perera--Rørdam arXiv:0903.2917v4, Propositions 4.5 and 4.8.
- So a counterexample needs a base such as `∏ S²`.
