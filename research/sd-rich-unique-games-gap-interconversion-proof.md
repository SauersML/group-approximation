---
rg: 2
id: sd-rich-unique-games-gap-interconversion-proof
kind: route
title: Right-merge unique constraints, apply the noise test, and push pseudo-distributions through the linear label maps
target: sd-rich-and-unique-games-sos-gaps-interconvert
requires: [noise-test-sound-on-smooth-design-rich-inputs]
---

**(a)** Fix a left labeling `a`. For each right vertex `v` let `p_v` be the law of
`phi_(uv)(a(u))` over its neighbours. `U` with the best right labels has value
`E_v max_b p_v(b)`. `Psi(U)` with the best right labels has value
`E_v E_sigma max_j p_v(sigma^(-1)(j))`. A fiber has two elements, so the second
is at most twice the first, and taking `b = phi(a(u))` shows the reverse
inequality. As `sigma` ranges over all 2-to-1 maps, `sigma o phi` induces every
pairing equally often, so every left vertex is fully rich.

For SoS, substitute `y'_((v,sigma),j) = sum_(b in sigma^(-1)(j)) y_(v,b)`:

- one-hotness and Booleanity hold modulo the constraints of `U`;
- each edge indicator of `Psi(U)` equals the corresponding indicator of `U` plus
  a sum of products `x y`;
- each such product is a square modulo Booleanity.

So pseudo-value does not drop.

**(b)** Substitute `z_((u,x),s) = sum_a x_(u,a) 1[x_a = s]`. This is folded,
one-hot and Boolean. The test's pseudo-acceptance is

```text
E sum_(a,a') x_(u,a) x_(w,a') Pr[x_a = y_(a')] >= (1-3 epsilon) E[sat_uv sat_wv].
```

Here `sat_e = sum_a x_(u,a) y_(v,pi_e(a))` is Boolean. Modulo Booleanity,
`sat sat' >= sat + sat' - 1` is the degree-4 square `((1-sat)(1-sat'))^2`.
Regularity gives `>= (1-3 epsilon)(1-2 eta)`. Soundness of the actual value is
the prerequisite.

**Algorithms.** `Psi(U)` has `|R| (2k)!/2^k` right vertices, and `R(Psi)` has
`|L| m^(2n)` variables. Both are constant factors when the alphabets are
constants. The two SoS substitutions add no degree, so nothing beyond `k >= 4`
is needed. Literature statements are recorded in the cited source artifact.
