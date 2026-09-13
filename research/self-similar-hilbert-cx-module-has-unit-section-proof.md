---
rg: 2
id: self-similar-hilbert-cx-module-has-unit-section-proof
kind: route
title: Finite intersection property of zero sets, and Cuntz's comparison of properly infinite projections
target: self-similar-hilbert-cx-module-has-unit-section
requires: []
---

**1.** For a section `η in E` let `Z(η) = {x : η(x) = 0}`, which is closed. Suppose `E` has no nowhere-vanishing
section. For every `n` pick `2^k >= n`. Then `E^{⊕n}` is a direct summand of `E^{⊕2^k} ≅ E`, and a
nowhere-vanishing section of `E^{⊕n}` would extend by zero to one of `E`. So `E^{⊕n}` has none either. A family `η_1, ..., η_n` gives
the section `(η_1, ..., η_n)` of `E^{⊕n}`, whose zero set is `∩ Z(η_i)`. So every finite intersection of zero
sets is nonempty. By compactness, some point `x_0` lies in `Z(η)` for every section `η`. Then `E_{x_0} = 0`,
a contradiction.

Now let `η` be nowhere vanishing. Then `|η|^2 = ⟨η, η⟩` is invertible in `C(X)`, and `ξ = η |η|^{-1}` is a
unit section. The Cuntz pair `S_1, S_2 in L(E)` implementing `E ≅ E ⊕ E` gives orthonormal sections
`S_w ξ`, `|w| = k`.

**2.** Kasparov gives `E ⊕ E' ≅ H_X`, so `E = P_E H_X` with `L(E) = P_E M(C(X)⊗K) P_E`. The isometries
`S_1, S_2 in L(E)` show `P_E = S_1S_1^* + S_2S_2^*` with `S_iS_i^* ~ P_E`, so `P_E` is properly infinite.

**3.**
- A partial isometry `V in M(C(X)⊗K)` with `V^*V = 1` and `VV^* = P_E` is the same thing as a unitary module
  map `H_X -> E`. So `P_E ~ 1` iff `E ≅ H_X`.
- `P_E` and `1` are properly infinite, and `[P_E] = [1] = 0` because `K_0(M(C(X)⊗K)) = 0`. Cuntz (BRR
  Proposition 2.3(i)) gives `P_E ~ 1` iff `P_E` is full. The forward direction is clear.
- If `E ≅ H_X`, then `K(E) ≅ K(H_X) = C(X) ⊗ K` is stable. Its unitization is then K1-injective by Lemma 2
  of `research/artifacts/k1-o2-ideal-finite-nuclear-dimension-2026-09-13.md`.
- Only these directions are claimed. The converse "`K(E)` stable implies `P_E` full" is not needed.
