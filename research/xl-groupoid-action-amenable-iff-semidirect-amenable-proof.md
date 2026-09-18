---
rg: 2
id: xl-groupoid-action-amenable-iff-semidirect-amenable-proof
kind: route
title: Pushing Reiter functions of the semidirect groupoid along its G-cocycle gives quasi-central witnesses; nuclearity gives the converse
target: xl-groupoid-action-amenable-iff-semidirect-amenable
requires: []
---

Notation as in the claim; `K = H x| G`, `c : K -> G`, `c(eta, g) = g`, a
continuous groupoid homomorphism into a discrete group.  For a unit `x`, the
arrow `(x, g)` goes from `g^-1 x` to `x`; the arrow `(eta, e)` is `eta`.

**Well-definedness.**  For `g in G` the map `f -> f o g^-1` preserves
`C_c(H)`, is a `*`-homomorphism for convolution and involution (as `g` is a
groupoid automorphism of an étale groupoid, it maps bisections to bisections
and counting measures on fibres to counting measures), and commutes with the
regular representations up to the unitary `delta_eta -> delta_{g eta}` on
`l^2` of fibres.  So it extends to `A = C*_r(H)` and preserves `C(X)`.

**(<=).**  Topological amenability of the étale groupoid `K` gives, for each
compact `L subset K` and `epsilon > 0`, a nonnegative `m in C_c(K)` with
`sum_{lambda in K^x} m(lambda) = 1` for all `x` and

```text
sup_{theta in L} || m^{r(theta)} - theta . m^{s(theta)} ||_1 < epsilon,
(theta . p)(lambda) = p(theta^-1 lambda)
```

(Anantharaman-Delaroche--Renault, Prop. 2.2.13; Brown--Ozawa Lemma 5.6.14).
Put `n_x(h) = sum { m(lambda) : lambda in K^x, c(lambda) = h }`.  Since
`supp m` is compact and `c` is continuous into a discrete group, `c(supp m)`
is a finite set `F`; each `n_x in Prob(F)`, and `x -> n_x(h)` is continuous
(locally a finite sum over bisections).  Because `c` is a homomorphism,
`c_*(theta . p) = c(theta) . c_* p`, so

```text
sup_{theta in L} || n_{r(theta)} - c(theta) . n_{s(theta)} ||_1 < epsilon.
```

Taking `L` to contain the arrows `(x, g)`, `x in X`, `g in S` (a compact set)
and a compact `L_0 subset H` gives

```text
(i)  sup_x || n_x - g . n_{g^-1 x} ||_1 < epsilon      (g in S),
(ii) sup_{eta in L_0} || n_{r(eta)} - n_{s(eta)} ||_1 < epsilon.
```

Define `xi in C_c(G, A)`, `xi(h) = n_.(h)^{1/2} in C(X)`.  Then
`<xi, xi> = sum_h xi(h)^* xi(h) = 1`.  With `(g.xi)(h) = alpha_g(xi(g^-1 h))`
and `||p^{1/2} - q^{1/2}||_2^2 <= ||p - q||_1`,

```text
|| xi - g.xi ||^2 = sup_x sum_h | n_x(h)^{1/2} - n_{g^-1 x}(g^-1 h)^{1/2} |^2
                 <= sup_x || n_x - g . n_{g^-1 x} ||_1 < epsilon.
```

*Commutators.*  Let `f in C_c(H)` be supported in an open bisection `U` with
`supp f subset L_0`.  For `d in C(X)`, `(f * d)(eta) = f(eta) d(s eta)` and
`(d * f)(eta) = d(r eta) f(eta)`, so `d f - f d = w f` with
`w(eta) = d(r eta) - d(s eta)`.  For a function `F` supported on a bisection,
`F^* F` is the unit-space function `x -> |F(eta_x)|^2` (`eta_x in U`,
`s(eta_x) = x`), whose norm is its sup norm.  Hence

```text
|| xi f - f xi ||^2 = || sum_h (w_h f)^*(w_h f) ||
   <= ||f||_inf^2 sup_{eta in supp f} sum_h |n_{r eta}(h)^{1/2} - n_{s eta}(h)^{1/2}|^2
   <= ||f||_inf^2 epsilon.
```

Finite sums of such `f` are dense in `A`, and `||xi|| = 1`, so for any finite
set of `a in A` and `delta > 0` a suitable `(S, L_0, epsilon)` makes
`||xi a - a xi|| < delta` and `||xi - g.xi|| < delta` (`g in S`).  This net is
a quasi-central approximation net: `<xi, xi> = 1`, approximately central,
approximately invariant.  By Buss--Echterhoff--Willett this implies that
`alpha` is amenable (Ozawa--Suzuki: amenability is equivalent to it).

**(=>).**  `A` is nuclear since `H` is amenable, and an amenable action on a
nuclear algebra has nuclear reduced crossed product.  The reduced crossed
product `C*_r(H) x|_r G` is the reduced groupoid algebra of `K`: both are the
completion of `C_c(K) = C_c(G, C_c(H))` in the regular representations on
`l^2(K_x) = l^2(G, l^2(H_x))`, which match under the evident unitary.  A
second countable Hausdorff étale groupoid whose reduced algebra is nuclear is
amenable (Anantharaman-Delaroche--Renault, Cor. 6.2.14 and Thm. 5.6.18 of
Brown--Ozawa, stated there for étale groupoids).  So `K` is amenable.  QED.

**Converse direction for XL (Cartan witnesses).**  If `A` is unital simple
classifiable with a `G`-invariant Cartan subalgebra `C(X)` of trivial twist,
Renault's theorem gives `A = C*_r(H)` for the effective étale Weyl groupoid
`H`; `A` simple forces `H` minimal, `A` nuclear forces `H` amenable (same
citation).  If `alpha` acts through automorphisms of `H` and is amenable, the
theorem gives `H x| G` amenable, i.e. (GSA_G) holds.

**Calibration.**  (a) `H = X` (trivial groupoid): `K = X x| G`, and the
theorem reduces to the known fact that `G acting on C(X)` is amenable iff
`G acts on X` topologically amenably.  (b) `H` = pair
groupoid of a finite set on which `G` acts transitively: `A = M_k` with a
nonamenable `G` permuting the matrix units; `K` is transitive with isotropy
groups isomorphic to `G`, hence not amenable, and `alpha` is not amenable (it fixes
the trace), consistent.  (c) Commuting `Gamma`: `K = X x| (Gamma x G)`,
amenable iff `G` acts amenably on `X` (as `Gamma` is amenable), recovering
`xl-commuting-minimal-action-gives-classifiable-witness` (up to the
classifiability hypotheses, which depend on `H` only).
