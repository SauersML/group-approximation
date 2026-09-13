---
rg: 2
id: amenable-hnn-seams-break-bernoulli-degree-one-expansion
kind: claim
title: An HNN seam over Z or Z^2 with an incompatible Z/2-character kills degree-one cocycle expansion of a superrigid Bernoulli shift
distinct_from:
  degree-one-bernoulli-expansion-excludes-weak-lifts: that derives consequences from degree-one expansion; this gives a structural condition under which expansion fails outright.
  bernoulli-expansion-iff-ultrapower-cocycle-superrigidity: that proves expansion is equivalent to ultrapower superrigidity; this exhibits failure of both for groups with amenable HNN seams.
artifacts:
  - research/artifacts/bernoulli-degree-one-expansion-amenable-seam-2026-09-13.md
---

**ESTABLISHED (unreviewed)** by `amenable-hnn-seams-break-bernoulli-degree-one-expansion-proof`.

**Setting.**
- `A_0 = <S_0 | R_0>` is finitely presented and nonamenable.
- `C <= A_0` is free abelian of rank 1 or 2, and `theta : C -> A_0` is injective.
- `Gamma = <S_0, t | R_0, t c t^-1 = theta(c)>` is the HNN extension.
- `X = [0,1]^Gamma` is the Bernoulli shift.

**Statement.** Assume:
- some `chi in Hom(A_0, Z/2)` has `chi o theta != chi|_C`;
- every measurable cocycle `Gamma x X -> Z/2` is cohomologous to a homomorphism.

Let `kappa` be a Kesten constant of `(A_0, S_0)` and `theta_0 = kappa/(kappa + 4|S_0|)`. Then for every `delta > 0`
there is a measurable `c : (S_0 u {t}) x X -> Z/2` with relator defects on measure at most `delta` whose distance to
every exact 1-cocycle, on some generator of `S_0`, is at least `theta_0`. So `X` has **no** degree-one cocycle
expansion with Z/2 coefficients, at any rate.

**Construction.**
- On `S_0`, `c` is the constant `chi`.
- On `t`, `c` is a marker-built approximate eigenfunction of the seam `C` for the character `chi o theta - chi|_C`.
  Its defects lie on sparse marker membranes.
- Every homomorphism of `Gamma` is compatible with `theta`, so `chi` does not extend. Superrigidity plus the spectral
  gap of `A_0` on `L^2_0(X)` then keeps every exact cocycle `theta_0`-far from `c`.

**Model test.**
- **Hypothesis side.** If `chi o theta = chi|_C`, then `chi` extends and `c = chi` is exact, so the incompatibility
  hypothesis is needed.
- **Nonamenable seam.** If `C` were nonamenable, approximate eigenfunctions for a nonzero character would not exist,
  and the construction dies.
- **Conclusion side.** The distance bound is uniform in `delta`, so no rate function exists.
