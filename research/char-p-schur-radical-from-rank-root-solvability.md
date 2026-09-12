---
rg: 2
id: char-p-schur-radical-from-rank-root-solvability
kind: route
title: Extend projective rank models across the adjunction with rank roots, then cut to a central character and compare classes
target: schur-kernel-lies-in-char-p-linear-sofic-radical
requires:
  - rank-ultraproduct-unit-groups-solve-nonsingular-equations
artifacts:
  - research/artifacts/deligne-rank-projective-rigidity-2026-09-12.md
---

Artifact Lemmas 3.2 and 3.3 and Theorem 3.4.
1. **Extension.** Rank roots, solved coordinatewise with errors `1/n` and amplified, extend every homomorphism
   `Q -> T(R)` across `q : Q -> (Q * <t>)/<<w>>` into an amplified target. The amplification is injective on
   scalars.
2. **Classes.** By naturality of pullback and evaluation, every projective rank class `beta_phi` vanishes on
   `ker q_*`.
3. **Cut.** A homomorphism `psi : E -> G(R)` not killing `z_0 = alpha_H(x)` splits along the central idempotents of
   `Fbar[Z]`, which exist because `|Z|` is prime to `p`. Some corner has `psi(z) = chi(z) 1` with `chi(z_0) != 1`.
4. **Contradiction.** That corner is a morphism of central extensions, so `beta_phi = chi o alpha_H`, and step 2
   gives `chi(z_0) = 1`.

*Verification by `w4-vf-linear-b` (2026-09-12), Section 25.5 of `research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`: PASS as an implication. Re-derived independently:*
- *the amplification is injective on scalars, and lift choices change the word only by a central scalar;*
- *naturality of `ev` in both variables;*
- *the exact isotypic cut, with idempotent rounding `rank(x - e) <= rank(x^2 - x)`;*
- *`β_φ = χ ∘ α_H`.*

*The input `rank-ultraproduct-unit-groups-solve-nonsingular-equations` is OPEN.*
