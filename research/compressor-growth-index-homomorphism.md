---
rg: 2
id: compressor-growth-index-homomorphism
kind: claim
title: The commutant growth index is multiplicative on the compressor semigroup
distinct_from:
  relative-wall-commutant-growth: That claim decides existence of a wall by a yes/no properness question at a single compressor; this one is a quantitative invariant defined on the whole compressor semigroup and asserts its algebraic law, which is what makes the tower and infinite-index consequences available.
  invariant-size-collapse: That is the general principle that a conjugation-invariant strictly monotone size forces a compression to be an equality, and it records the II_1 trace as failing the monotonicity hypothesis; this supplies the invariant that survives on that branch, namely the Pimsner--Popa index, which is invariant and strictly monotone but may be infinite, and states the multiplicative law that makes it usable.
artifacts:
  - notes/TRUE_RELATIVE_WALL_IS_COMMUTANT_GROWTH.md
---

For `pi:G->U(M)` into a finite tracial algebra, `N=M cap pi(Gamma)'`, and
`s` in the compressor semigroup `P_Gamma={s : s Gamma s^(-1)<=Gamma}`, put

```text
lambda(s)=[Ad pi(s)(N):N] in [1,infinity]
```

(Pimsner--Popa index for the trace-preserving expectation).  Then `lambda`
is submultiplicative on `P_Gamma`, multiplicative wherever finite, equal to
`1` exactly when `Ad pi(s)(N)=N`, and equal to `1` on `N_G(Gamma)`.

Consequence: a wall forces `lambda(t)>1`, a strictly increasing tower
`N<Ad pi(t)(N)<Ad pi(t)^2(N)<...` with constant index, and `[M:N]=infinity`.
Finite-index -- in particular finite-dimensional -- relative commutants
admit no wall.

**Two scope notes.**  Whether the `[M:N]=infinity` consequence is
informative is **open**: an earlier note here claimed it was generic, on the
ground that diffuse limiting commutants force infinite index, and that ground
was retracted -- a diffuse algebra has no minimal projections and a
finite-index subfactor of a II_1 factor is diffuse.  The correct narrow
statement, diffuse *abelian* implies infinite index, does not apply here since
the relevant `N` is not abelian.  Either way the content of this claim is in
`lambda(s)`, which diffuseness does not force: `lambda(s)=1` whenever
`Ad pi(s)(N)=N`, however diffuse `N` is.

Second, the index is **not** a metric invariant: refining one atom of trace
`t` into pieces `t-epsilon` and `epsilon` moves the subalgebra by
`O(sqrt epsilon)` in `||.||_2` while sending the index to at least
`t/epsilon`.  So it applies only to exact inclusions in a fixed algebra, as
used here, and is not available to arguments about almost-invariant or
approximately defined subalgebras.
