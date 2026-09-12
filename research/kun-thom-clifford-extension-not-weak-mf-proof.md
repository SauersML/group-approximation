---
rg: 2
id: kun-thom-clifford-extension-not-weak-mf-proof
kind: route
title: Cut the negative central corner and anticommute two Clifford lamps
target: kun-thom-clifford-extension-not-weak-mf
requires: []
artifacts:
  - notes/FALSE_CLIFFORD_NORM_MF_STERILITY.md
---

# Cut the negative central corner and anticommute two Clifford lamps

Internal proof, transcribed from `notes/FALSE_CLIFFORD_NORM_MF_STERILITY.md`
(2026-08-12), sections 2 and 3. `requires: []` is a proof commitment: the
argument uses only property `(T)` of `Gamma`, strictness of the compressor,
stable finiteness of a norm matrix quotient, and the Clifford relations.

## Step 1 — cut to the negative central corner

Suppose `Theta(z) != 1` and put `e = (1-Theta(z))/2`, a nonzero central
projection.

> Projections lift through the norm matrix quotient, so after restricting to a
> subsequence and cutting by nonzero lifts `e_n`, the corner is again a norm
> matrix quotient
>
> `e A e = product_n M_(r_n) / directSum_n M_(r_n),`
>
> with unit `e`, and the corner representation sends `z` to `-e`.  No lower
> bound on `r_n/d_n` is required.

The absence of a rank hypothesis is what makes the argument work against an
arbitrary model: the corner may be vanishingly thin.

## Step 2 — pass to the adjoint representation

> Choose unitary lifts `U_(g,n)` for the corner images.  On
> `K_n = L2(M_(r_n), tr_(r_n))` form the adjoint maps
> `beta_n(g)(x) = U_(g,n) x U_(g,n)^*`.
> Operator-norm multiplicative defect for the lifts gives operator-norm
> multiplicative defect for the adjoint maps.  Hence they define an honest
> representation of `G` in the corresponding norm quotient of the `B(K_n)`.

Passing to `Ad` is what removes the lift ambiguity: scalar phase errors in the
`U_(g,n)` cancel, so `beta` is a genuine representation even though the lifts
are only approximately multiplicative.

## Step 3 — property (T) forces the compression to be an equality

> Let `p_Gamma` be the Kazhdan projection of `Gamma`, and let `P = beta(p_Gamma)`.
> The inclusion `t Gamma t^(-1) <= Gamma` gives
> `P <= beta(t) P beta(t)^*.`
> The two projections are unitarily equivalent.  A norm quotient of finite
> matrix algebras is stably finite, so the inequality is equality:
> `P = beta(t) P beta(t)^*.`
> Therefore `beta(t)` preserves the `Gamma`-fixed subspace.

This is the one-sided Kazhdan transport step, in its operator-norm form: a
one-sided containment between unitarily equivalent projections in a finite
algebra is forced to be an equality.

## Step 4 — the contradiction from two distinct lamps

> Let `o=Gamma`.  The matrix vector represented by the lamp `c_o` is
> `Gamma`-fixed.  Consequently the vector represented by `c_(t o)` is also
> `Gamma`-fixed.  Choose
> `gamma in Gamma with gamma t Gamma != t Gamma,`
> which exists because the compression is strict.  Fixedness gives
> `||Theta_-(c_(gamma t Gamma))-Theta_-(c_(t Gamma))||_(2,omega)=0.`
> But the two sites are distinct, and `Theta_-(z)=-e`, so the two
> self-adjoint lamp unitaries anticommute.  In the normalized corner trace,
>
> `||C_x-C_y||_2^2 = tr(2-C_x C_y-C_y C_x) = 2.`
>
> This is a contradiction.  Hence `Theta(z)=1`.

The two halves of the contradiction are exactly the two hypotheses: strictness
of the compressor supplies a `gamma` moving the coset `tGamma`, so the sites
are distinct and the lamps anticommute in the `z=-1` sector, giving squared
distance `2`; while Kazhdan fixedness forces distance `0`.

## Scope

The conclusion is about the **operator-norm** corona only. It says nothing
about normalized-Hilbert--Schmidt models, and in particular it does not bear on
`kun-thom-clifford-crossed-product-ce`, where the sign is required to survive
in a *tracial* ultraproduct — a different category in which no analogous
sterility is known. Confusing the two would misread a negative operator-norm
result as evidence against the tracial program.
