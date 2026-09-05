---
rg: 2
id: compressed-intertwiner-gap-and-rank-integrality-proof
kind: route
title: Apply the Kazhdan gap to rectangular intertwiners and use integral exceptional rank
target: compressed-irreducibles-require-all-deleted-dimensions
requires:
  - two-kazhdan-correction-has-quadratic-rank-curvature
artifacts:
  - research/artifacts/compressed-representation-quadratic-curvature-2026-09-05.md
---

Let `W:C^d->C^N` be the inclusion and `B_s=W^*rho(s)W`. The positive
contraction `I-B_s^*B_s` has rank at most k. All but at most k singular
values c_i of B_s equal one. For a unitary polar completion U_s,

```text
R_s=rho(s)W-WU_s,
rank(R_s)<=k,
||R_s||_HS^2=2 sum_i(1-c_i)<=2k.
```

Here HS is unnormalized. On a singular direction with c_i=1, there is
no leakage and the intertwining error is zero. Inverse polar completions
can be chosen consistently; a self-inverse generator has a self-adjoint
compression and admits a self-adjoint unitary sign completion.
Telescoping each defining word gives `(CID1)`.

Extend W to an isometry `J:C^D->C^N`, where `d<=D<N`. On its original
d columns the preceding error bound applies; on the new D-d columns
the difference of two unit vectors has norm at most two. Therefore

```text
||rho(s)J-J(U_s direct_sum I)||_HS^2<=2k+4(D-d).
```

The genuine unitary action on rectangular Hilbert--Schmidt operators
given by `X -> rho(g)X sigma(g)^*` has no invariant vector: a nonzero
intertwiner would have invariant nonzero range in irreducible rho,
hence would surject from dimension D onto the larger dimension N.
Applying the Kazhdan inequality to J of HS norm sqrt(D) gives

```text
kappa sqrt(D)<=sqrt(2k+4(D-d))
 +sqrt(D) max_s||sigma(s)-(U_s direct_sum I)||_(2,D).
```

This proves `(CID2)`. The same column estimate with D=N gives the
claimed sufficient correction by rho. If k=o(N), `(CID2)` is bounded
away from zero at every smaller D, proving `(CID3)` for asymptotically
accurate corrections.

For `(CID4)` we use a valid iteration consequence of the required
theorem. Fix its `(QRC5)` parameter epsilon=1 and constants A,C,delta_0.
Whenever `0<delta<delta_0` and `C d delta^2<1`, the exceptional
projection has integral rank less than one and is zero. Its two-sided
complementary bound then gives full defining defect at most delta/2.
The correction costs at most A delta. Repeat with the same constants;
the threshold persists and the corrections sum to at most 2A delta.
In fixed dimension the tuple converges to an exact representation.
An exact intermediate tuple instead ends the procedure immediately.

Now take k=1 and let N tend to infinity. The compressed tuples satisfy
delta->0, whereas `(CID2)` at D=d gives distance from every exact
same-dimensional representation at least `kappa-sqrt(2/d)`. They
therefore cannot satisfy `C d delta^2<1` infinitely often: the previous
iteration would give distances at most 2A delta->0. Thus eventually
`1/C<=d delta^2<=2 ell^2`, proving `(CID4)`. This argument deliberately
does not claim an iteration above the integral-rank threshold.

For the concrete arithmetic examples, reduction of `SL_5(Z)` onto
`SL_5(F_p)` is surjective by elementary generation. The latter acts
doubly transitively on projective points: send two independent vectors
to the desired pair and adjust determinant on a complementary direction.
The permutation representation has commutant dimension two, counting
orbits on ordered pairs; the constants occur once, so their orthogonal
complement is irreducible. Its dimension is
`(p^5-1)/(p-1)-1=p^4+p^3+p^2+p`. The all-Hilbert-H2 input is
Bader--Sauer's Theorems A and C and equation (1), as recorded with its
primary source in the artifact. These are actual unbounded-dimensional
irreducibles of a fixed Kazhdan group satisfying the conditional
cohomology hypothesis, not irreducibles of changing ambient groups.
