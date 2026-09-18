---
rg: 2
id: abelianized-cover-nonzero-twist-proof
kind: route
title: Push the relation-module class into the kernel algebra and let the full radical kill any splitting
target: abelianized-cover-injective-corona-model-carries-nonzero-twist
requires: []
---

## Proof

The complete proof is the `## Proof` section of the target claim.
- **Item 1.**  Conjugation by `rho(E)` preserves `C*(rho(M))`, and `M` acts
  trivially on it because the algebra is commutative.
- **Item 2.**  Form the pushout `E' = (U(B) x| E)/N`, with `N` the antidiagonal
  copy of `M`.  The map `Psi(b,e) = b rho(e)` is a homomorphism to `U(Q)`.
  If `rho_* xi = 0`, a section `sigma` gives a corona homomorphism
  `Psi o sigma` of `G`.  It is trivial because `Rad_MF(G) = G`, so
  `rho(gt) in U(B)`.
- **Item 3.**  The Lyndon sequence shows `[E,M] != 1` for a nontrivial
  full-radical base.
- **Item 4.**  The nonabelian pushout over the relative commutant splits
  exactly when `rho([E,M]) = 1`.

Only the definition of `Rad_MF` and elementary group cohomology are used.
