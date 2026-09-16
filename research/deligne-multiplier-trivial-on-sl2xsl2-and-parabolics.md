---
rg: 2
id: deligne-multiplier-trivial-on-sl2xsl2-and-parabolics
kind: claim
title: Deligne's mod-three multiplier is a circle coboundary on SL2(Z) x SL2(Z) and on both maximal parabolics of Sp4(Z)
distinct_from:
  c2-root-commuting-cycle-is-maslov-trivial: that is the holonomy of one commuting cycle of root subgroups; this is triviality of the whole multiplier, with circle coefficients, on three infinite subgroups that contain non-unipotent Levi factors.
  isw-scalar-cocycle-obstruction-dies-on-sp4-parabolic-radicals: that bounds the Levi-invariant scalar cohomology of the parabolic radicals, to rule out the ISW convergent sequence; this evaluates one class, Deligne's, on the whole parabolics and shows it vanishes.
  deligne-triple-cover-fd-central-invisibility: that says z dies in every finite-dimensional unitary representation of E_3; this says z survives in a one-dimensional character of the preimage of each of three infinite-index subgroups, and (DTC2) forces every such subgroup to have infinite index.
artifacts:
  - research/artifacts/sp4-mod3-twisted-fibre-f2xf2-calibration-2026-09-16.md
---

**CLAIM.**  Let `p : G_3 -> Sp_4(R)` be the connected three-fold covering
group, `E_3 = p^{-1}(Sp_4(Z))`, `ker p = <z>`, and let `alpha` be the
mod-three multiplier of `1 -> <z> -> E_3 -> Sp_4(Z) -> 1`
(`deligne-triple-cover-fd-central-invisibility`).  Use the symplectic basis
`e_1, f_1, e_2, f_2` of `Z^4`.  Let `H` be one of the following subgroups:

1. `S = S_1(Z) x S_2(Z) = SL_2(Z) x SL_2(Z)`, block diagonal on the orthogonal
   hyperbolic planes `<e_1, f_1>` and `<e_2, f_2>`;
2. the Siegel parabolic `P_S(Z)`, the stabilizer of `Z e_1 + Z e_2`, which is
   `Sym_2(Z) x| GL_2(Z)`;
3. the Klingen parabolic `P_K(Z)`, the stabilizer of `Z e_1`, which is
   `N(Z) x| ({+-1} x SL_2(Z))`.  Here `N(Z) = {n(x,y,u)}` with law
   `n(x,y,u) n(x',y',u') = n(x+x', y+y', u+u'+xy'-x'y)`.

Then there is a homomorphism `phi : p^{-1}(H) -> T` with
`phi(z) = omega = e^{2 pi i/3}`.  Equivalently, `alpha|_H` is a `T`-valued
coboundary.  Moreover the `Z/3`-extension splits over `P_S(Z)`, and over
`F x F'` for free subgroups `F <= S_1(Z)` and `F' <= S_2(Z)`.  No splitting
is claimed over `SL_2(Z)` itself.

**Consequences.**  Let `K` be a subgroup of such an `H`.

- The twisted group C*-algebra `C^*(K; alpha|_K)` is isomorphic to the
  untwisted `C^*(K)` (artifact, Lemmas 7.1 and 7.3).
- `alpha` evaluates to zero on the image of `H_2(K; Z)` in
  `H_2(Sp_4(Z); Z)`, since the evaluation factors through the class of
  `alpha|_K` in `H^2(K; T)`.
- By (DTC2), `K` has infinite index in `Sp_4(Z)`.  Inducing `phi` to `E_3`
  would give a finite-dimensional representation with `rho(z) = omega`
  (artifact, remark 9.3).

The operator-algebra use is `mod3-twisted-fibre-llp-forces-f2xf2-llp`.
