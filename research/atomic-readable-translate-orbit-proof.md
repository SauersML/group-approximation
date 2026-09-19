---
rg: 2
id: atomic-readable-translate-orbit-proof
kind: route
title: Equal trace makes an atom orbit finite and minimality makes every orbit point profile-pure
target: atomic-readable-translate-algebra-groupifies-zpc-gap
requires:
  - profile-pure-finite-projection-orbit-groupifies-zpc-gap
---

Conjugation by every `pi(g)`, `g in Q_G`, preserves `D_infinity` and its
faithful normalized negative-corner trace. It therefore sends atoms to
atoms of the same positive trace. If `p` is an atom and

```text
delta=tau_-(p)>0,
```

then distinct conjugates of `p` are distinct atoms of the abelian algebra
and hence orthogonal. Any `N` distinct orbit points have total trace
`N delta<=1`; consequently the orbit has at most `floor(1/delta)` points.

The finite-dimensional algebra `D_0` is contained in `D_infinity`. If
`(E_l)_l` are its nonzero joint readable atoms, then for every orbit atom
`p_t` each `p_tE_l` is a projection of `D_infinity` below the minimal
projection `p_t`. Thus `p_tE_l` is either `0` or `p_t`. Since
`sum_l E_l=q_-`, exactly one `E_l` contains `p_t`. This is the required
profile-purity condition.

The orbit therefore satisfies `(PPO2)--(PPO4)`, and
`profile-pure-finite-projection-orbit-groupifies-zpc-gap` gives the stated
finitely presented nonhyperlinear stabilizer quotient. The diffuse
complement of the finite orbit is never used.
