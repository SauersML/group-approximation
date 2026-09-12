---
rg: 2
id: hs-stable-hyperlinear-kazhdan-hyperbolic-persistent-class-proof
kind: route
title: Residual finiteness from Malcev, non-residually-finite truncation from Dogon--Vigdorovich, prime central reduction
target: hs-stable-hyperlinear-kazhdan-hyperbolic-forces-persistent-class
requires: [hyperlinear-flexibly-hs-stable-group-is-residually-finite, kazhdan-hyperbolic-hs-stability-kills-hyperlinearity, finite-kernel-nonrf-has-central-prime-reduction, finite-central-extension-rf-iff-virtually-splits]
---

## Direct proof

1. `Γ` is finitely generated, hyperlinear and flexibly HS-stable, so it is
   residually finite (`hyperlinear-flexibly-hs-stable-group-is-residually-finite`).
2. By `kazhdan-hyperbolic-hs-stability-kills-hyperlinearity`, some finite central
   extension `1 -> Z/N -> Γ_N -> Γ -> 1` is not hyperlinear. Finitely generated
   residually finite groups are sofic, hence hyperlinear, so `Γ_N` is not residually finite.
3. Apply `finite-kernel-nonrf-has-central-prime-reduction` with `K = Z/N`,
   `H = Γ`, `E = Γ_N`. It gives a finite-index `L <= Γ_N` with image `H_0`, a prime `p`,
   and a central extension `1 -> C_p -> L/B -> H_0 -> 1` whose finite residual is the
   whole kernel `C_p`. So `L/B` is not residually finite.
4. `H_0` has finite index in `Γ`, so it is residually finite and hyperbolic. By
   `finite-central-extension-rf-iff-virtually-splits` (with `A = C_p`), the class
   `α` of `L/B` restricts nontrivially to every finite-index subgroup of `H_0`.
5. **Not good.** For a good group every class in `H^2(-;C_p)` is inflated from a
   finite quotient, and so dies on the kernel of that quotient. Step 4 excludes this for `H_0`,
   and goodness passes to finite-index subgroups, so `Γ` is not good.

∎
