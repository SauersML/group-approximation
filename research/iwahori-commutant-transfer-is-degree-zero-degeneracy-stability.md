---
rg: 2
id: iwahori-commutant-transfer-is-degree-zero-degeneracy-stability
kind: claim
title: Iwahori commutant transfer is the uniform degree-zero degeneracy problem, not a consequence of the degree-one Deligne gap
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
distinct_from:
  iwahori-uniform-infinitesimal-rigidity: that proves a degree-one Mayer--Vietoris mismatch gap at congruence representations; this identifies the degree-zero invariant-subspace estimate needed by the weaker HNN commutant route.
  iwahori-unitary-commutant-transfer: that is the desired quantitative conclusion; this is its cohomological normal form and the exact obstruction to importing the degree-one proof.
---

Let `rho_+,rho_-:C=SL_2(Z)->U(d)` be exact vertex representations with
Iwahori edge defect `delta_B`, and let `M=M_d(C)` carry the conjugation
representations.  Then

```text
M^(C,+)=rho_+(C)',            M^(C,-)=rho_-(C)'.
```

After identifying the two almost-equal edge actions, the estimate required by
`iwahori-unitary-commutant-transfer` is precisely the dimension-uniform
degree-zero statement

```text
dist_2(v,M^(C,-)) <= f(delta_B)
for every unitary v in M^(C,+).                         (D0-1)
```

At `delta_B=0` the pair is a finite-dimensional representation of the
amalgam `A=SL_2(Z[1/2])`.  Finite-dimensional co-density gives

```text
M^(C,+)=M^A=M^(C,-),                                   (D0-2)
```

so the zero set is correct.  Uniformity in `(D0-1)` is the entire issue.

This is **not** supplied by `iwahori-uniform-infinitesimal-rigidity`.  That
theorem concerns the degree-one restriction mismatch on cocycles.  Here the
two spaces are degree-zero invariant spaces.  In the tracial matrix
ultraproduct, failure of `(D0-1)` produces a genuine unitary representation
of `A` on the Hilbert ultraproduct of the matrix spaces with a nonzero vector
fixed by the first `C` but not by `A`.  Such infinite-dimensional
representations are not excluded by finite-dimensional co-density: the
quasi-regular representation on `l2(A/C)` already has a `C`-fixed vector.

Consequently a valid proof must use the **finite-coordinate origin** of this
Hilbert-ultraproduct representation.  It cannot merely quote co-density or
the degree-one Deligne gap.  Equivalently, it must prove the relative
commutant equality in `hnn-route-is-relative-commutant-collapse`.

## Attempts

- **Reuse the degree-one Hecke gap.**  Invalid without an additional bridge:
  the `H^1` cuspidal Gram operator has the Deligne gap, while `(D0-1)` concerns
  `H^0` and contains the spherical top mode.
- **Use exact co-density.**  This proves only `(D0-2)` in each fixed matrix
  dimension.  Compactness does not make the modulus uniform as `d` grows.
- **Pass to the Hilbert ultraproduct.**  This identifies the obstruction but
  does not remove it, because infinite-dimensional `C`-fixed non-`A`-fixed
  vectors exist abstractly.  The missing theorem must distinguish those from
  vectors represented by uniformly operator-bounded matrix coordinates.
