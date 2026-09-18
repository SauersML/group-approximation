---
rg: 2
id: deligne-multiplier-survives-on-bernoulli-times-profinite-actions
kind: claim
title: The Deligne mod-three multiplier is not a measurable circle coboundary on any profinite, Bernoulli, or Bernoulli-times-profinite action of Sp4(Z)
distinct_from:
  sp4-maslov-circle-survives-in-bernoulli-l0-cohomology: that uses Jiang on the plain Bernoulli shift for the small real Maslov classes; this covers the torsion Deligne classes on every ergodic profinite action and on Bernoulli times profinite, which are not Bernoulli and where Jiang's lemma is silent.
  central-bernoulli-lifts-force-splitting: that has finite coefficients A and a Bernoulli lift of the extension; this has circle coefficients and a phase field that is only required to exist on the product with a profinite factor.
  gohla-thom-lattices-no-weakly-bernoulli-liftable-action: that is about liftability of actions to the central extension; this is about untwisting the multiplier in L^0 cohomology, which is weaker than lifting, since a measurable coboundary need not come from an E_3-action.
  kazhdan-profinite-untwisting-is-virtual-splitting: that is the general profinite theorem for Kazhdan groups; this is its Deligne instance plus the Bernoulli-times-profinite extension through Popa.
---

**ESTABLISHED** by `deligne-multiplier-bernoulli-profinite-survival-proof`.

**Setting.**
- `Gamma = Sp_4(Z)`, and `alpha in Z^2(Gamma, mu_3)` is a normalized cocycle of Deligne's triple cover
  `E_3 = mu_3 x_alpha Gamma`, as in `deligne-triple-cover-fd-central-invisibility`.
- Let `X` be an ergodic profinite action of `Gamma`, or a point.
- Let `B = (Y_0, nu)^Gamma` be a Bernoulli shift of `Gamma` with any standard base.

**Claim.** For `beta in {alpha, alpha^2}`, no measurable `c : Gamma x Z -> T` satisfies
`c(g, hz) c(h, z) = beta(g,h) c(gh, z)` for a.e. `z`, when

```text
Z = X        or        Z = B x X   (diagonal action).                    (DM1)
```

Equivalently, the classes of `alpha` and `alpha^2` survive in `H^2(Gamma, L^0(Z, T))`, and
`L^infty(Z) x|_beta Gamma` is not isomorphic to the untwisted crossed product by an isomorphism of the
form `u_g -> a_g u_g` with `a_g` in `U(L^infty(Z))`.

**What this kills.**
- `E_3` is hyperlinear exactly when `L_alpha(Gamma)` is Connes-embeddable, because
  `L(E_3) = L(Gamma) + L_alpha(Gamma) + L_{alpha^2}(Gamma)` and `Gamma` is residually finite.
- Hyperlinearity would follow from any action `Z` on which `alpha` is a measurable coboundary and whose
  untwisted crossed product is Connes-embeddable. Then
  `L_alpha(Gamma) ⊂ L^infty(Z) x|_alpha Gamma = L^infty(Z) x| Gamma`.
- For the residually finite `Gamma`, the profinite and Bernoulli crossed products, and their products, are the
  standard Connes-embeddable ones. By (DM1), none of them can serve as such an untwisting witness.
- So measurable untwisting over these actions cannot refute `maslov-mod3-projective-defect-gap`.

**Survivors.**
1. **The quotient of the Bernoulli shift of `E_3` by `mu_3`.**
   - Let `B' = [0,1]^{E_3}` and `X' = B'/mu_3`, which is a mixing `Gamma`-action, since `mu_3` acts freely a.e.
   - A measurable section `s` of `B' -> X'` defines `z(g,x)` in `mu_3` by `(1,g) s(x) = z(g,x) s(gx)`.
     Then `z(g,hx) z(h,x) = alpha(g,h) z(gh,x)`, so `alpha` is a coboundary on `X'`.
   - By (DM1), `X'` is neither profinite nor Bernoulli times profinite. Popa's theorem is not known to apply to it
     as a `Gamma`-action.
   - If its crossed product is Connes-embeddable, then `E_3` is already hyperlinear. So this witness is circular
     and is not excluded here.
2. **Incoherent finite-level voltage towers.**
   - These are phase fields on the Schreier graphs `Gamma/Gamma_n` with frustration tending to zero that do not
     come from one measurable field on the limit.
   - They escape `kazhdan-profinite-untwisting-is-virtual-splitting` (see "Where the argument needs coherence"
     there). They remain governed by `deligne-class-finite-action-norms-vanish` and
     `deligne-class-congruence-cosystole-bounded-below`.
