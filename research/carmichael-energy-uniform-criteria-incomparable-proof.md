---
rg: 2
id: carmichael-energy-uniform-criteria-incomparable-proof
kind: route
title: Separate the two Carmichael criteria with a constant packet and a sparsely perturbed packet
target: carmichael-energy-uniform-criteria-incomparable
requires: []
---

Both directions are settled by explicit permutation matrices; the claim body
carries the computations and this route records the two verifications and the
one arithmetic identity they share.

For a permutation matrix `P in U(d)` with `f` fixed points,

```text
||P-I||_2^2 = (1/d)tr(2I-P-P^*) = (2d-2f)/d.                  (PM)
```

**Direction one.**  `d=3`, `B` the `3`-cycle, constant packet `X_i=B`.  Then
`B^3=I` so the cube relators are exact, and `(X_iX_j)^2=B^4=B` for every pair,
so by `(PM)` with `f=0` each edge defect is `sqrt2` — a uniform bound
independent of `M`.  Summing over `C(M,2)` pairs gives `E_M=M(M-1)`, which is
`Theta(M^2)`.  So `(UNI)`-shaped data at a fixed scale does not give `(ACE)`.

The general statement needs no example: `(UNI)` controls each edge separately,
and `M(M-1)/2` edges each of size `C def_R(U)` sum to `Theta(M^2)` unless the
defect is zero.

**Direction two.**  `d=4`, `B` the `4`-cycle `(1 2 3 4)` acting by
`Be_k=e_(k+1)`, `W` the transposition matrix of `(1 2)`.  Conjugation gives
`WBW^*` the permutation `(1 2)(1 2 3 4)(1 2) = (1 3 4 2)`, and composing,
`B` after `(1 3 4 2)` sends `1|->4, 2|->2, 3|->1, 4|->3`, i.e. the `3`-cycle
`(1 4 3)`.  Its square is `(1 3 4)`, a `3`-cycle with `f=1`, so by `(PM)`

```text
||(B WBW^*)^2-I||_2^2 = (2*4-2)/4 = 3/2.
```

Since `B^4=I`, any two packet members drawn from the same conjugate give
`(X_iX_j)^2=I` exactly.  Placing the perturbed conjugate on a set of size
`ceil(sqrt M)` therefore leaves only the mixed nonzero
edges (at most `M^(3/2)+M` of them), each of squared defect `3/2`, so
`E_M = O(M^(3/2)) = o(M^2)` while the
maximum edge defect stays `sqrt(3/2)`.

Reading the same tuple as a model of `<x|x^4>` with `U(x)=B` makes the
presentation defect exactly `0`, so any bound of the form
`||(X_iX_j)^2-I||_2 <= C def_R(U)` is violated.  Hence `(ACE)` does not give
`(UNI)`.

Both packets have `B^3` equal to `I` or to `B^*`, so `(SCE)` is satisfied in
each case (with equality in direction two), confirming that neither example
contradicts `subquadratic-carmichael-energy-collapse`.
