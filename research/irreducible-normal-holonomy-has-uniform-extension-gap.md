---
rg: 2
id: irreducible-normal-holonomy-has-uniform-extension-gap
kind: claim
title: Irreducible normal-subgroup holonomy has a uniform extension gap
distinct_from:
  moving-subgroup-schreier-correction-has-no-index-loss: that permits arbitrary subgroup holonomy and small relative padding; normality and irreducibility here force zero padding below a dimension-independent threshold and imply extension of the subgroup representation.
---

Use the notation and Kazhdan-constant convention of
`moving-subgroup-schreier-correction-has-no-index-loss`. Suppose additionally
that `N` is normal in `G` and `pi:N->U(d)` is irreducible. For every choice
of gauges `V_t` and generator tuple `U_s`, define

```text
beta^2=max_s avg_t ||U_s V_t-V_(t') pi(n(s,t))||_(2,d)^2,
s t=t' n(s,t).
```

If `beta<kappa/2`, there is a genuine representation `alpha:G->U(d)`
in the original matrix dimension such that

```text
max_s ||alpha(s)-U_s||_(2,d) <= (1+4/kappa) beta,
alpha|_N is unitarily equivalent to pi.                 (ING1)
```

Thus `pi` extends to `G` after conjugating `alpha` by one unitary. The
generator estimate in `(ING1)` is in the original `U_s` basis; equality
`alpha|_N=pi` is not asserted in that same basis.

Consequently, if `pi` does not extend to a `d`-dimensional representation
of `G`, every tuple and every gauge choice satisfy

```text
beta >= kappa/2.                                       (ING2)
```

The bound is independent of `d` and `[G:N]`, which may vary. It is an
obstruction to a proposed exact irreducible holonomy certificate. It does
not construct such a certificate for arbitrary almost representations,
prove Hilbert--Schmidt stability, or establish nonhyperlinearity.

DERIVATION
irreducible-normal-holonomy-extension-proof
