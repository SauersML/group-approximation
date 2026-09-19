---
rg: 2
id: close-normalized-characters-do-not-force-equivalence-proof
kind: route
title: Perturb an invariant representation by one small non-invariant irreducible
target: close-normalized-characters-do-not-force-equivalence
requires: []
---

With `pi_m = pi_0 (+) tau_m` as in the claim, for every `q in Q_m`

```text
| chi_(pi_m)(q) - chi_(pi_m o Ad(g))(q) | / d_m
  = | chi_(tau_m)(q) - chi_(tau_m o Ad(g))(q) | / d_m
  <= 2 dim tau_m / d_m <= 2 eps_m,
```

since `pi_0 o Ad(g) = pi_0` by invariance and characters are bounded by
the dimension.  The two representations have the same kernel (`Ad(g)` of
a normal subgroup of `SL_3(Z)` contained in `Lambda_0` is again such a
subgroup, and the kernel of `pi_m` is the congruence kernel, which is
`Ad(g)`-stable).  They are inequivalent because the multiplicity of
`tau_m` is `1` in `pi_m` and `0` in `pi_m o Ad(g)` when the orbit of
`tau_m` under `Ad(g-bar)` is nontrivial and `pi_0` contains `tau_m`
and `tau_m o Ad(g)` with equal multiplicity (true for a multiple of the
regular representation).  Such `tau_m` exist for every `m` whenever the
outer action of `g-bar` on `Irr(Q_m)` is nontrivial, and their dimension
is at most `|Q_m|^(1/2) = o(d_m)` once `d_m / |Q_m|^(1/2) -> infinity`,
which holds for any tower in which the multiplicity of the regular
representation tends to infinity; for towers where it does not, take
`eps_m` of order `dim tau_m / d_m`, still a counterexample to the lemma
as a general statement.  Integrality of the multiplicity vector cannot
rescue the lemma: the difference of multiplicities is `1` on two
constituents, which is "eventually zero" for no `m`.
