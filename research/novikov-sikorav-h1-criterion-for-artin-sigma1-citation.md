---
rg: 2
id: novikov-sikorav-h1-criterion-for-artin-sigma1-citation
kind: route
title: Import the Novikov-Sikorav criterion and the Bieri-Renz kernel criterion for Sigma^1
target: novikov-sikorav-h1-criterion-for-artin-sigma1
requires: []
---

Citation import, not a reproof.

- **Item 1.** A. Suciu, *Sigma-invariants and tropical varieties*,
  arXiv:2010.07499, abstract, verbatim: "The Bieri-Neumann-Strebel-Renz
  invariants Σ^q(X,ℤ)⊂H^1(X,ℝ) of a connected, finite-type CW-complex X are the
  vanishing loci for Novikov-Sikorav homology in degrees up to q". For `q = 1`
  this goes back to J.-C. Sikorav's thesis. The same import is used in
  `bnsr-invariants-stabilize-at-cohomological-dimension-proof`, input 1, with the
  coefficient ring `\widehat{ZG}_{-χ}`.
  - `Σ^1(G; Z) = Σ^1(G)` is standard (Bieri–Renz), because `FP_1` means
    finitely generated.
  - The claim's statement "vanishing for `χ` and for `-χ`" is used only
    symmetrically, so it does not depend on the sign convention.
- **Item 2.** K. Almeida, *The Σ^1 invariant for some Artin groups of arbitrary
  circuit rank*, arXiv:1605.00271v1, §1.1, verbatim:
  - "Theorem 1.2 ([8]). Let G be a group of homological type FPm and H be a
    subgroup of G containing the commutator [G, G]. Then H is of type FPm if and
    only if S(G, H) := {[χ] ∈ S(G) | χ(H) = 0 } ⊂ Σ m(G, Z)."
    Here [8] is Bieri–Renz. With `m = 1` and `H = ker χ` we have
    `S(G, H) = {[χ], [-χ]}`.
  - "Lemma 1.3 ([2], Corollary 2.11). Let G be an Artin group and χ a discrete
    character of G. Then [χ] ∈ Σ 1(G) if and only if Ker (χ) is finitely
    generated." Here [2] is Almeida–Kochloukova, Forum Math. 27 (2015).

Read on 2026-09-19 from the arXiv PDF of 1605.00271v1, pages 1–3.
