---
rg: 2
id: bounded-rank-corners-excluded-proof
kind: route
title: A bounded-rank corner is a genuine finite-dimensional representation
target: bounded-rank-corners-excluded
requires: [coordinate-ultraproduct-transport]
---

## Why sufficient

Work on the coordinate ultraproduct `H_omega = prod_omega C^{d_n}`, where by
`coordinate-ultraproduct-transport` clause 1 the models assemble into an
honest unitary representation `tilde U` of `H` with the corona operator
norms.

**The corner is a finite-dimensional subrepresentation.**  Write
`q = [q_n]` with `rank q_n = r` along the ultrafilter (bounded ranks may be
thinned to a constant one).  Choose orthonormal bases
`e_n^1, ..., e_n^r` of `ran q_n`.  Any `x = [x_n]` with `q x = x` has
`x_n = sum_i c_n^i e_n^i` with `|c_n^i| <= ‖x_n‖`, so
`x = sum_i (lim_omega c_n^i) [e^i]`.  Hence `ran q` is exactly the
`r`-dimensional span of the `[e^i]`.  Since `q` lies in the relative
commutant, `tilde U(h) q tilde U(h)^* = q` for every `h in H`, so `tilde U`
restricts to a genuine unitary representation `H -> U(ran q) = U(r)`.

**The Kazhdan source acts trivially on it.**  Restrict that representation
to `iota(Gamma)`.  It has dimension at most `r`, so by hypothesis it is
trivial: every vector of `ran q` is fixed by `iota(Gamma)`.  Therefore
`ran q` is contained in the range of the Kazhdan projection `P` onto the
`iota(Gamma)`-invariant vectors.

**Contradiction.**  By `coordinate-ultraproduct-transport` clause 3, every
element of the normal closure of `u` in `H_0` — in particular `eps` — acts
as the identity on `ran P`, hence on `ran q`.  But
`‖(Theta(eps) - lambda) q‖ = 0` says `tilde U(eps)` acts on `ran q` as the
scalar `lambda`.  So `lambda = 1`, contrary to hypothesis.  Hence no such
`q` exists.

Note which hypothesis does the work: not property (T), but the absence of
low-dimensional representations of the Kazhdan source.  Property (T) enters
only through `coordinate-ultraproduct-transport`, in the Kazhdan projection
and the finiteness cancellation.
