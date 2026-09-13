---
rg: 2
id: subexponential-complexity-zd-subshift-rings-have-rank-models
kind: claim
title: A minimal Z^d subshift of polynomial pattern complexity gives a crossed product with a unital rank model, with no towers and no invariant measure
distinct_from:
  free-minimal-crossed-products-are-simple-with-rank-models: that already gives a faithful unital Følner rank model for every free minimal Z^d Cantor system over a finite field, with no complexity hypothesis; this reaches the rank model of the subshift case by a growth bound alone.
---

**ESTABLISHED (unreviewed; scope repaired at review).** Let `X ⊆ A^(Z^d)` be an infinite minimal subshift on which
`Z^d` acts **freely** (for a minimal action of the abelian group `Z^d` this is the same as topologically free, since
each `Fix(g)` is closed and invariant), whose pattern complexity `p(n)` (the number of patterns on the cube
`[−n, n]^d`) grows polynomially in `n`, and let `R = LC(X, F_q) ⋊ Z^d`. Then `R` is simple, has polynomial growth,
hence a unital rank model over `F_q`, hence is stably finite and carries a faithful Sylvester matrix rank function.
For `N ≥ 3` the Kazhdan groups `EL_N(R)` are `F_q`-linear sofic, hence weakly sofic, by
`rank-modelled-simple-rings-give-linear-sofic-projective-el`.

The same conclusion holds under the weaker hypothesis that `m ↦ |B_m(Z^d)| · p(2m+1)` grows
subexponentially.

**Why this is worth having.** For `d ≥ 2` the exact matricial (tower) route can fail: a free minimal `Z^2`
SFT is matricial only if covariant quantum tilings exist at every scale
(`matricial-z2-sft-crossed-products-give-quantum-tilings`), and quantum-rigid shifts have none. The measure
route to a rank function is open in characteristic `p`
(`invariant-measure-gives-rank-function-any-field`, Kaplansky-hard), which is the only characteristic where
the Kazhdan groups exist. This claim supplies the rank model regardless, from complexity alone.

**Consequence for the middle rung.** `rank-modelled-simple-algebra-with-non-lef-kazhdan-el-group` names
Labbé's `LC(Ω_U, F_q) ⋊ Z^2` as its test case and currently *assumes* the rank model. That assumption is
discharged by this claim as soon as Labbé's Wang shift is known to have polynomial pattern complexity, which
is the expected behaviour of a primitive self-similar (substitutive) shift but is recorded here as a
separate input: `labbe-wang-shift-has-polynomial-pattern-complexity`. Under that input the middle rung
reduces entirely to the non-matriciality half, which is `un-labbe-ring`'s quantum-tiling question.

**Review (un-verify-open, 2026-09-13, `research/artifacts/un-review-open-2026-09-13-part1.md` §2.4): PASS after scope
repair; subsumed in the free case.** The ball bound `dim R_m ≤ |B_m(Z^d)|·p(2m+1)` was checked. The first version
asserted the rank model for every infinite minimal subshift; Theorem 1 needs `R` simple for injectivity, and a minimal
`Z^d`-subshift need not be free (a `Z`-subshift extended trivially in `e_2` is minimal and not effective), so freeness
was added. In the free case the conclusion already follows from `free-minimal-crossed-products-are-simple-with-rank-models`.
