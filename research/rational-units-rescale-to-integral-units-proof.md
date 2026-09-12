---
rg: 2
id: rational-units-rescale-to-integral-units-proof
kind: route
title: Gauss's lemma for group rings whose reductions modulo every prime are domains
target: rational-units-rescale-to-integral-units
requires: []
---

Call `w in Z[G]` *primitive* if the gcd of its coefficients is `1`,
equivalently `w mod p != 0` in `F_p[G]` for every prime `p`. Every nonzero
`w in Q[G]` is `q w'` with `q in Q^x` and `w'` primitive, and
`supp(w') = supp(w)`.

**Item 1.** Let `u in Q[G]^x` with inverse `v`. Write `u = q u'` and
`v = r v'` with `u'`, `v'` primitive. Then `u' v' = (qr)^(-1)`. The left
side lies in `Z[G]`, so `N := (qr)^(-1)` is a nonzero integer, and likewise
`v' u' = N`.

Suppose a prime `p` divides `N`. Reducing modulo `p` gives
`(u' mod p)(v' mod p) = 0` in `F_p[G]`. Both factors are nonzero because
`u'` and `v'` are primitive. This contradicts the hypothesis that `F_p[G]`
is a domain. So `N = +-1`, `u' v' = v' u' = +-1`, `u'` is a unit of `Z[G]`,
and `u = q u'`.

**Item 3.** `supp(u) = supp(u')`. The inverse of `u'` is `+-v'`, and
`supp(v') = supp(v)`.

**Item 2.** If `Z[G]` has a nontrivial unit `w`, then `|supp(w)| >= 2`, and
`w` is a unit of `Q[G]` with the same support, so it is not `lambda g`.
Conversely, let `u in Q[G]^x` be nontrivial. Then `|supp(u)| >= 2`, and by
items 1 and 3 `u = q u'` with `u' in Z[G]^x` and `|supp(u')| >= 2`, so `u'`
is not `+-g`.

**The Promislow group.** The hypothesis holds for every torsion-free
elementary amenable group over every field, by Kropholler--Linnell--Moody
(1988). This is the same import already used in
`unit-conjecture-fails-over-complex-numbers` and listed among the known cases
of `kaplansky-zero-divisor-conjecture`. `P` is torsion-free and virtually
`Z^3`, hence elementary amenable. QED
