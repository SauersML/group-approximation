---
rg: 2
id: deligne-multiplier-trivial-on-sl2xsl2-proof
kind: route
title: Commuting lifts plus the SL2(Z) amalgam kill the block class, and the Siegel and Klingen radicals lift homomorphically
target: deligne-multiplier-trivial-on-sl2xsl2-and-parabolics
requires: []
artifacts:
  - research/artifacts/sp4-mod3-twisted-fibre-f2xf2-calibration-2026-09-16.md
---

Full proofs are in the artifact, sections 2--6.  The argument uses only
covering-space topology, elementary matrix algebra, and a complete proof of
the presentation of `SL_2(Z)`.  No literature is imported.

1. **Covering lemmas (section 2).**
   - `ker p` is central: conjugation into a discrete normal subgroup of a
     connected group is constant.
   - Over a connected subgroup `Q <= Sp_4(R)`, a continuous homomorphic
     section is unique.  It is equivariant under every lift of an element
     normalizing `Q`.  It exists when `pi_1(Q) -> pi_1(Sp_4(R))` is zero, by
     the lifting criterion.
   - Preimages of commuting connected subgroups commute elementwise.  The
     commutator map is well defined, continuous, and takes values in the
     discrete `ker p`.
2. **`S = SL_2(Z) x SL_2(Z)` (sections 3--4).**
   - The preimages `S~_1`, `S~_2` commute, and `S~_1 cap S~_2 = <z>`.
   - Lemma 3.2P proves `SL_2(Z) = < A, B | A^4, A^2 B^{-3} >` in full.
     Generation is the Euclidean algorithm.  Faithfulness is ping-pong of
     `x -> -1/x` and `x -> -1/(x+1)` on the positive and negative
     irrationals.
   - So each `S~_i` has the presentation
     `< A, B, Z | Z^3, [Z,A], [Z,B], A^4 Z^{-i}, A^2 B^{-3} Z^{-j} >`.
     The character `A -> c`, `B -> d`, `Z -> omega`, with `c^4 = omega^i`
     and `d^3 = c^2 omega^{-j}`, kills every relator.
   - The product of the two factor characters is well defined on
     `S~_1 S~_2`.
   - Free subgroups lift homomorphically, and the lifts of `F` and `F'`
     commute.  So the extension splits over `F x F'`.  This case does not use
     the presentation.
3. **Siegel parabolic (section 5).**
   - `P_S(R)_0 = {m(A) n(S) : det A > 0}` is homeomorphic to
     `Sym_2(R) x SO(2) x T^+` (Gram--Schmidt).  Its `pi_1 = Z` is generated
     by `m(R_theta)`.
   - `rho(X + iY) = [[X, -Y],[Y, X]]` maps `U(2)` into `Sp_4(R)`, with
     `J = rho(-i I)`, and `m(R_theta) = rho(R_theta)` with
     `R_theta in SU(2) = S^3`.  So the generator dies in `Sp_4(R)`, and a
     homomorphic section `s` exists over `P_S(R)_0`.
   - `epsilon = m(diag(1,-1))` has a lift of order two,
     `epsilon~ = epsilon~_0 z^k`.  Equivariance makes
     `sigma_S(y epsilon^j) = s(y) epsilon~^j` a homomorphism.
4. **Klingen parabolic (section 6).**
   - `N(R) = {n(x,y,u)}` is homeomorphic to `R^3`.  The symplectic
     conditions force the displayed form.  So `N(R)` has a homomorphic
     section `s_N`.
   - `P_K(Z) = N(Z) L(Z)` uniquely, with `L(Z) = {+-1 on <e_1,f_1>} x S_2(Z)`
     contained in `S`.
   - Every `x in p^{-1}(P_K(Z))` is uniquely `s_N(n) y` with
     `y in p^{-1}(L(Z))`.  By equivariance of `s_N`,
     `phi_K(s_N(n) y) = phi_S(y)` is a homomorphism with `phi_K(z) = omega`.

The matrix identities are machine-checked in exact arithmetic by
`experiments/sp4-mod3-twisted-fibres-have-llp-2026-09-16/check_matrix_identities.py`.
That check is a sanity check, not part of the proof.
