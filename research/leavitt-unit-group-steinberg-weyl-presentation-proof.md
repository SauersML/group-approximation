---
rg: 2
id: leavitt-unit-group-steinberg-weyl-presentation-proof
kind: route
title: Collapse the rank-five Steinberg family by the Weyl symmetry of the roots and identify St_5 with the unit group
target: leavitt-unit-group-steinberg-weyl-presentation
requires: [atlas-steinberg-spare-index-independence, leavitt-steinberg-map-iso-from-rank-three]
artifacts:
  - research/artifacts/leavitt-unit-group-steinberg-weyl-presentation-2026-09-12.md
  - experiments/nonsofic-certificates/presentations/verify_st5_weyl_presentation.py
  - experiments/nonsofic-certificates/presentations/st5-weyl-presentation.json
---

The complete proof is Section 2 of the artifact. Its steps:

1. **Weyl relators.** HLT coset enumeration of `<c,t | t^2, c^5, (tc)^4, (tc^-1tc)^3,
   (tc^-2tc^2)^2>` closes at 120 cosets; `(12345), (12)` satisfy the relators and generate
   `S_5`. So `sigma -> p_sigma` is a homomorphism `S_5 -> P`.
2. **Symmetry lemma.** The (K) relators make every `y_a` commute with `p_(34), p_(45)`, which
   generate the pointwise stabilizer of `{1,2}`. So `X_ij(a) := p_sigma y_a p_sigma^-1`
   (`sigma(1)=i, sigma(2)=j`) is well defined and `p_rho X_ij(a) p_rho^-1 = X_rho(i)rho(j)(a)`.
   A relation among `X`'s at one injective index assignment holds at all of them.
3. **Families at every root.** The imposed representatives give, at every root: disjoint-root
   commutation for all 25 coefficient pairs, same-source and same-target commutation at `(1,1)`,
   the 13 reducing (St3) instances (unit letters and `e*e = f*f = 1`, `e*f = f*e = 0`), agreement
   of all three spare-index chains for the 12 irreducible pairs, the partition relator, and
   `X_ij(1)^2 = 1`.
4. **Derived commutations.** If `x` commutes with `y` and `z`, then it commutes with `[y,z]`.
   Writing `X_il(a) = [X_im(1), X_ml(a)]` or `X_ij(a) = [X_im(a), X_mj(1)]` with a spare `m`,
   same-source commutation follows at `(1,a)`, then `(a,1)`, then `(a,b)`. Same-target follows
   in the same order, and root commutativity from both. This is the whole (St2) family.
5. **Involutivity.** `X_ij(a) = [X_im(1), X_mj(a)]` commutes with `X_im(1)`, and
   `[alpha^2, beta] = alpha[alpha,beta]alpha^-1[alpha,beta]` gives `X_ij(a)^2 = 1`.
6. **Spare-index theorem.** With the least-spare-index chain as the anchored right-hand side,
   Steps 3-5 are exactly the relators of the group `G_0` that
   `atlas-steinberg-spare-index-independence` identifies with `St_5(L)`. That proof uses the
   anchored family only through chain agreement. So there is `psi : St_5(L) -> P`,
   `x_ij(a) -> X_ij(a)`.
7. **Isomorphism.** `psi` is onto: `(t y_1)^3 = t^2 = 1` gives
   `psi(x_12(1)x_21(1)x_12(1)) = t`; conjugation gives every `p_(ij)`, and
   `c = p_(12)p_(23)p_(34)p_(45)`. All sixty relators hold in `L^x` (exact computation, MSI,
   verdict PASS), so `phi : P -> L^x` exists. `phi o psi` is the canonical map
   `St_5(L) -> GL_5(L)` followed by the prefix-code isomorphism `M_5(L) = L`, which is an
   isomorphism by Khanh Theorem 5.4. Hence `psi`, and so `phi`, are isomorphisms.

Verification: `verify_st5_weyl_presentation.py`, 2.4 s on MSI, dual mode (44,473 products
cross-checked). It checks the 60 relators, the coset enumeration (120, a permutation
representation), 600 conjugate-word identities `p_sigma y_a p_sigma^-1 = Theta(E_ij(a))`, the
full target family at every root as a control (8,160 instances), and six negative controls.
