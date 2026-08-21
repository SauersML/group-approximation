---
rg: 2
id: odd-congruence-exact-sector-inner-action-proof
kind: route
title: Superrigidity pins the levels, innerness mod odd n inertizes the exact slot, and the corrector absorbs the rest
target: odd-congruence-exact-sector-is-one-inner-action
requires: []
---

**Exact restrictions factor through odd congruence quotients.**  A
finite-dimensional unitary representation of `Lambda = SL_3(Z)` has
precompact image; by Margulis superrigidity for higher-rank lattices
mapping to compact groups the image is finite (Margulis, Discrete
Subgroups of Semisimple Lie Groups, Ch. VII; the ambient
`SL_3(R)` has no nontrivial compact quotient), and by the congruence
subgroup property (Bass--Milnor--Serre) every finite quotient of
`SL_3(Z)` factors through some `SL_3(Z/n)`.  The sector hypothesis
takes all `n_m` odd and coprime to `p`.

**Part 1.**  With `p` invertible mod `n_m`, the reduction
`Gamma = SL_3(Z[1/p]) -> SL_3(Z/n_m)` is defined and extends the map
on `Lambda`; `V'_m := sigma_m(h mod n_m)`.  Since `Lambda ->
SL_3(Z/n_m)` is onto (strong approximation / elementary generation),
there is `lambda_h in Lambda` with `lambda_h = h mod n_m`, so
`V'_m = sigma_m(lambda_h)` lies in the group image; every element of
`sigma_m(Lambda)'` commutes with it by definition of the commutant.
This is the inertness of the exact slot.  (It is also the finite-level
mechanism of co-density: `sigma_m(Lambda)'' = sigma_m(SL_3(Z/n_m))''
ni V'_m`.)

**Part 2.**  For `lambda in Lambda_- = Lambda cap h^(-1) Lambda h`
the relation `h lambda h^(-1) in Lambda` holds in `Gamma`, so in `M`
(where `pi` is a genuine homomorphism) `V pi(lambda) V^* =
pi(h lambda h^(-1))`; and levelwise `V'_m sigma_m(lambda) V'^*_m =
sigma_m(h lambda h^(-1) mod n_m)`, so in the ultraproduct
`V' pi(lambda) V'^* = pi(h lambda h^(-1))` as well.  Hence
`W = V'^* V` commutes with `pi(lambda)` for every
`lambda in Lambda_-`: `W in pi(Lambda_-)' cap M`.  For
`k in pi(Lambda)' cap M`, part 1 gives `[k, V'] = 0` (the commutant
of `pi(Lambda)` in `M` is the ultraproduct of the levelwise
commutants, on which conjugation by `V'_m` is trivial; equivalently
`V' in pi(Lambda)''`), so

```text
k V = k V' W = V' k W,   V k = V' W k,
[k, V] = V' [k, W],
```

which is `(OI1)`.  Therefore `[k, V] = 0` for all `k` iff `[k, W] =
0` for all `k`, i.e. iff `Ad(W)` is trivial on `pi(Lambda)' cap M`;
and since `Gamma = < Lambda, h >`, triviality for every admissible
`W` is exactly `(RC3)` restricted to the sector.

**Part 3.**  `pi(Lambda)' cap M = prod_U sigma_m(Lambda)'` and
likewise for `Lambda_-` (commutants of finite groups of unitaries
pass through tracial ultraproducts: almost-commuting with the finite
image projects to the exact commutant by averaging over the finite
image group, a trace-preserving conditional expectation).  Levelwise,
`sigma_m(Lambda)' = ⊕_rho 1 otimes M_(m_rho)` over the irreducible
`rho` of `SL_3(Z/n_m)` occurring with multiplicity `m_rho`, and
`sigma_m(Lambda_-)'` refines it along the branching of restrictions
to the image of `Lambda_-` -- the stated Bratteli data.  The
regular-trace hypothesis on `Lambda` forces `sum over rho of
(dim rho . m_rho / d_m) . |chi_rho(lambda)| / dim rho -> 0` for
`lambda != e`, the level-spreading statement.  The `h`-tower trace
condition displayed in the claim is the case `gamma = h^j` of
regularity of `tau compose pi` on `Gamma`.
