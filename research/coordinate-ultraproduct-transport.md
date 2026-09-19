---
rg: 2
id: coordinate-ultraproduct-transport
kind: claim
title: The compression defect is trivial on the Kazhdan-invariant subspace, in operator norm
distinct_from:
  kazhdan-asymptotic-commutant-transport: that theorem transports asymptotic commutants and concludes in normalized Hilbert--Schmidt norm on the adjoint Hilbert-space ultraproduct; this one works on the coordinate Hilbert-space ultraproduct and concludes an exact operator-norm identity on a subspace that may be zero.
artifacts:
  - non_mf_groups_exist.tex
---

Let `Gamma` have property (T), `iota: Gamma -> H`,
`t iota(Gamma) t^-1 <= iota(Gamma)`, `[c, iota(Gamma)] = 1`,
`d = t c t^-1`, `u = [d, iota(a)]`, and put `H_0 = <iota(Gamma), c, t>`.
Let `U_n: H -> U(d_n)` be an operator-norm asymptotic representation, let
`H_omega = prod_omega C^{d_n}` be the Hilbert-space ultraproduct, and let
`tilde U` be the induced map.  Then:

1. `tilde U` is an **honest** unitary representation of `H` on `H_omega`,
   and `‖tilde U(h) - 1‖ = ‖Theta(h) - 1‖` for the associated corona
   representation `Theta`;
2. the projection `P` onto the `iota(Gamma)`-invariant vectors lies in the
   finite algebra `A_omega = prod_omega M_{d_n}`, commutes with
   `tilde U(H_0)`, and satisfies `P = tilde U(t) P tilde U(t)^*`;
3. every element of the normal closure of `u` **in `H_0`** — in particular
   `eps = u^2` — acts as the identity on the range of `P`, exactly, in
   operator norm.

The conclusion is an operator-norm statement, not a `2`-norm statement, and
this is the only route out of `hs-invisibility-inflation-no-go` that does
not go through a corner of the corona.  Its price is that `P` may be zero:
the coordinate ultraproduct has no canonical invariant vector, whereas on
the adjoint side the unitary `U_n(c)` itself is one, which is what makes
the manuscript's transport unconditional and simultaneously confines it to
the `2`-norm.
