# STW LXXXVII: Z2 boundary and limit-operator audit

## Result

The translation action of `Z^2` on its Stone--Cech compactification is free.
For each nonzero translation, a finite residue partition along a nonzero
integer coordinate is cyclically permuted; a fixed ultrafilter would have to
contain two disjoint cells.  Consequently there are no finite boundary
orbits and no equivariant coefficient maps onto finite periodic systems.

This excludes two proposed lower-bound routes for
`C*_u(Z^2)=ell^infinity(Z^2) crossed_product_r Z^2`:

1. no periodic coefficient quotient yields a crossed-product quotient onto
   a matrix algebra over `C(T^2)`;
2. no star-homomorphic retraction onto the canonical `C*_r(Z^2)=C(T^2)` can
   fix the group unitaries.  Such a retraction would give a
   translation-invariant character of `ell^infinity(Z^2)`, hence a fixed
   Stone--Cech point.

## Limit operators retain rather than isolate the torus

The limit diagonal map at `omega` evaluates a coefficient along the orbit
`Z^2 omega`.  Every finite-index coset partition is sent to another full
coset partition.  The integrated limit representation therefore contains

```text
C(Z^2/H) crossed_product_r Z^2
 ~= M_[Z^2:H](C(T^2))
```

for every finite-index `H`.  For boundary ultrafilters the representation
factors through the uniform Roe corona, so these two-dimensional periodic
blocks survive at infinity.

This is not a nuclear-dimension lower bound.  The blocks are arbitrary
subalgebras of the limit image, and nuclear dimension is not monotone under
arbitrary subalgebras.  The Stone--Cech freeness theorem simultaneously
prevents promoting them to the natural finite-orbit quotients.

## Mechanism audit

- **Crossed product / invariant mean.**  An invariant mean gives only the
  previously audited ucp expectation, not a homomorphic retraction.  The new
  freeness argument proves that no homomorphic retraction fixing the group
  algebra exists.
- **Limit operators.**  They fix the translation unitaries but retain every
  periodic diagonal packet, so their ranges do not collapse to the torus.
- **K-theory.**  Each periodic block carries the Bott class of `T^2`, but an
  inclusion of a subalgebra does not transfer either K-theoretic dimension or
  nuclear dimension upward.  No periodic quotient is available to reverse
  the variance.
- **Dynamic asymptotic dimension.**  The rank-two obstruction is visible for
  the diagonal pair and its periodic crossed products.  Ordinary nuclear
  dimension permits approximations that ignore the diagonal; without a
  diagonal-recovery theorem, dynamic asymptotic dimension remains an upper
  bound mechanism rather than the missing lower bound.

## Trust boundary

All Stone--Cech, covariance, and limit-map assertions are proved directly in
the attached route.  The standard transitive-groupoid identification gives
the matrix algebra over `C*_r(H)`.  No lower bound for
`dim_nuc(C*_u(Z^2))` and no two-colour construction is claimed.
