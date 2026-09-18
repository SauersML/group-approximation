---
rg: 2
id: left-right-group-strategies-intersection-proof
kind: route
title: Split l^2 into double cosets, trivialize each as coset spaces around the intersection's standard form, truncate, and apply the amplified standard-form lemma
target: left-right-group-strategies-see-only-intersection-subgroups
requires:
  - ce-standard-form-strategies-are-quantum-approximable
---

Notation as in the target.

**(LRP1) Double cosets.** `l^2(Lambda)` is the orthogonal sum of the
`l^2(D)` over `D in S_A \ Lambda / T`. Each summand is invariant under
`lambda(S_A)` and `rho(T)`, hence under the von Neumann algebras they
generate. So `P_(x,a)` and `Q_(y,b)` are block diagonal, and
`p = sum_D ||xi_D||^2 p_D` is a countable convex combination of the
correlations of the normalized components. Since `C_qa` is closed and
convex, it suffices to treat one `D = S_A gamma T`.

The unitary `(V zeta)(w) = zeta(w gamma)` maps `l^2(S_A gamma T)` onto
`l^2(S_A T')` with `T' = gamma T gamma^(-1)`, and satisfies
`V lambda(s) = lambda(s) V` and `V rho(t) V^* = rho(gamma t gamma^(-1))`.
So we may assume `gamma = e` and `I = S_A cap T` hyperlinear.

**(LRP2) Coordinates.** Choose transversals `sigma` of `S_A/I` in `S_A` and
`kappa` of `I\T` in `T`. The map `(c,u,d) -> sigma(c) u kappa(d)` is a
bijection `S_A/I x I x I\T -> S_A T`.

For uniqueness, suppose `s u t = s' u' t'` with `s,s'` in the image of
`sigma`, `t,t'` in the image of `kappa`, and `u,u' in I`. Then
`s'^(-1) s u = u' t' t^(-1)` lies in `S_A cap T = I`, so `s' = s`. Then
`u'^(-1) u = t' t^(-1)` lies in `I`, so `t' = t` and `u' = u`.

Write `s sigma(c) = sigma(sc) alpha(s,c)` and
`kappa(d) t = beta(d,t) kappa(dt)`, with `alpha, beta` in `I`. Under the
resulting unitary
`W : l^2(S_A/I) (x) l^2(I) (x) l^2(I\T) -> l^2(S_A T)`,

```text
W^* lambda(s) W = sum_c |sc><c| (x) lambda_I(alpha(s,c)) (x) 1,
W^* rho(t) W    = block operator described below,
```

More precisely, since `sigma(c) u kappa(d) t = sigma(c) (u beta(d,t)) kappa(dt)`,
`W^* rho(t) W` is the block operator which, on the summand indexed by `d`,
acts as `1 (x) rho_I(beta(d,t))` on the first two legs and moves the third
leg by the permutation `d <-> dt` of `I\T`. Every block is right
multiplication by an element of `I` on `l^2(I)`, tensored with a partial
permutation matrix on `l^2(I\T)`. Hence
Alice's operators lie in `B(l^2(S_A/I)) (x)bar L(I) (x) 1`, and Bob's lie in
`1 (x) R(I) (x)bar B(l^2(I\T))`, with `R(I) = L(I)'` on `l^2(I) = L^2(L(I))`.

**(LRP3) Truncation.** Approximate `xi` within `delta` by a unit vector `xi'`
in `C^F (x) l^2(I) (x) C^G`, where `F,G` are finite sets of cosets with
coordinate projections `E_F, E_G`. Since `Q` acts trivially on the first leg
and `P` on the third,

```text
<P Q xi', xi'> = <(E_F P E_F) Q xi', xi'> = <(E_F P E_F)(E_G Q E_G) xi', xi'>.
```

The compressions are positive operator-valued measures in `M_F(L(I))` and in
`R(I) (x) M_G`, summing to the identities of `C^F (x) l^2(I)` and
`l^2(I) (x) C^G`. Because `I` is hyperlinear, `L(I)` is Connes embeddable.
The amplified form of `ce-standard-form-strategies-are-quantum-approximable`
puts the correlation of `xi'` in `C_qa`. Let `delta -> 0` and use closedness.
