---
rg: 2
id: power-two-legal-folded-certificates-reach-beyond-power-one-proof
kind: route
title: Exact Farkas infeasibility at power one, a checked 60-dart pairing at power two, and the index-two mapping torus
target: power-two-legal-folded-certificates-reach-beyond-power-one
requires:
  - legal-f-folded-fatgraphs-give-surface-subgroups
  - legal-folded-certificates-at-power-one-census
artifacts:
  - experiments/legal-f-folded-fatgraphs-2026-09-17/surface_phi300_m2.json
  - experiments/legal-f-folded-fatgraphs-2026-09-17/verify_surface_phi300_m2.log
  - experiments/legal-f-folded-fatgraphs-2026-09-17/verify_surface.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/validate_certificates.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/census_allwords_m1.log
---

Conventions follow `legal-f-folded-fatgraphs-give-surface-subgroups`. Upper case is inverse, and
`phi = phi_300 = (a -> abb, b -> caaa, c -> babb)`. Standard facts used, not re-read at source:
Bestvina--Handel, Brinkmann, and that free-by-cyclic groups with `n >= 2` are one-ended.

**Step 1: automorphism.** `phi(cA) = babb BBA = b` and `phi(aC) = abb BBAB = B`. So
`phi(aaCaC) = abb B B = a`, `phi(cAcAA) = phi(aaCaC)^-1 = A`, and
`phi(b (cAcAA)^3) = caaa AAA = c`. So `phi` is onto, hence an automorphism, with inverse
`psi = (a -> aaCaC, b -> cA, c -> b (cAcAA)^3)`. `verify_surface.py` checks
`phi o psi = psi o phi = id` by free reduction.

**Step 2: hyperbolic.** The transition matrix `M` has columns `(1,2,0)`, `(3,0,1)`, `(1,3,0)`.
So `det M = -1`, `M^3 > 0` and `chi_M = t^3 - t^2 - 9t + 1`. Its only possible rational roots
are `±1`, and `chi_M(1) = -8`, `chi_M(-1) = 8`. So `chi_M` is irreducible. The argument of
Step 2 of `hyperbolic-f3-by-z-with-genus-two-surface-certificates-proof` applies verbatim: `phi` is
fully irreducible and atoroidal, and `G_300` is one-ended and hyperbolic. It uses only that `chi_M`
is an irreducible cubic with no root `±1` and a Perron--Frobenius root `> 1`.

**Step 3: no power-one certificate.** Entry 300 of `census_allwords_m1.log` is `infeasible-exact`.
By part 1 of `legal-folded-certificates-at-power-one-census`, no legal `f`-folded fatgraph exists
for this `f`.

**Step 4: the power-two certificate.** `f^2` is the rose map of
`phi^2 = (a -> abbcaaacaaa, b -> babbabbabbabb, c -> caaaabbcaaacaaa)`. It is positive, so it
satisfies (TT). Its gates equal those of `f`: `{a}, {b}, {c}, {A, C}, {B}`.
`surface_phi300_m2.json` stores `phi0`, `power = 2`, `partial^- = {bc, CB}` and a pairing of the
60 boundary letters. `verify_surface.py` rebuilds everything else from these fields, as in Step 3
of `hyperbolic-f3-by-z-with-genus-two-surface-certificates-proof`, now with `f^2` in place of `f`.

- The boundary circles are `bc`, `f^2(bc)^-1`, `CB` and `f^2(CB)^-1`.
- The `f^2`-corners are the corners between blocks `f^2(x)^-1` in `partial^+`. There are 4.

The checker verifies:

- that `p` is a fixed-point-free involution with inverse labels;
- that every boundary word is cyclically reduced;
- (L), (2), (3) and (4);
- connectivity, `V = 22`, `E = 30` and `chi(X) = -8`.

Output: `CERTIFICATE OK` (`verify_surface_phi300_m2.log`). As a cross-check,
`validate_certificates.py` projects the pairing to a feasible point of the `m = 2` LP with
`chi = -8`.

**Step 5: conclusion.** By the criterion applied to `f^2`, `S*_{f^2}(X)` is `pi_1`-injective in
the mapping torus of `f^2`. Its fundamental group is `F x|_{phi^2} Z`, the subgroup `<F, t^2>` of
index 2 in `G_300`. The boundary circles of `X` are glued in pairs with opposite orientations, so
`S*_{f^2}(X)` is closed and orientable. It is connected, and `chi = chi(X) = -8`, so its genus is 5.
Hence `pi_1(S_5) <= G_300`.

For part 4 of the claim: `H_1(G_300) = Z ⊕ coker(M - I)`, and `|det(M - I)| = |chi_M(1)| = 8`. The
four power-one classes have `|chi_M(1)| = 4` or `6`. Since `b_1 = 1` in all cases, the torsion
subgroup of `H_1` is an isomorphism invariant, and it separates `G_300` from them. Relabelling
letters and reversing images give isomorphic mapping tori and carry certificates to certificates,
so the claim holds for the whole class of 12. `QED`
