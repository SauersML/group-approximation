---
rg: 2
id: flat-gain-multipartite-green-proof
kind: route
title: Gauge every flat multipartite gain to the trivial cover
target: flat-gain-multipartite-covers-have-uniform-green-bound
requires:
  - multipartite-triangle-curl-has-uniform-infinity-green-bound
---

The clique complex of a complete `r`-partite graph with `r>=3` is simply
connected.  Backtracking and triangle flatness therefore make path gain
homotopy invariant.  If `t_x` is the gain from a fixed basepoint to `x`, then
`g_(xy)=t_x^(-1)t_y`.

The coordinate permutation `(x,k)|->(x,t_xk)` gauges the regular cover to
`X_(r,m) times K` and preserves both counting `L^2` and infinity norms.
Triangle curl and its Moore--Penrose inverse consequently become `|K|`
direct copies of the base operators.  Applying a unitary representation of
`K` gives the same conclusion by the vertexwise unitary gauge.  The base
Green estimate therefore transfers with exactly the same constant,
independently of the deck group and gains.
