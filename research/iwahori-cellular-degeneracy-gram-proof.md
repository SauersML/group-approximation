---
rg: 2
id: iwahori-cellular-degeneracy-gram-proof
kind: route
title: Covering pullback and transfer realize the spherical Hecke star algebra on cellular harmonic cochains
target: iwahori-cuspidal-cellular-hecke-angle
requires: []
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
---

Use the Bass--Serre orbifold graph of
`PSL_2(Z)=C_2*C_3`.  Give each lifted cell the usual reciprocal-stabilizer
weight.  Choose the Bass--Serre cell structure on the second modular vertex
by transporting the first one through `diag(2,1)`.  The two inclusions of the
Iwahori group are then degree-three cellular orbifold coverings of these two
copies of the same weighted complex; this is a choice of cellular models,
not a claim that `diag(2,1)` acts on one fixed Bass--Serre tree.

For a unitary local system, pullback `p^*` along a finite orbifold cover and
cellular transfer `p_*` are adjoint.  Both commute with the cellular
differential.  Consequently pullback also commutes with the codifferential:
for cochains `c,e`,

```text
<d^* p^* c,e>=<p^*c,de>=<c,p_*de>
              =<c,dp_*e>=<p^*d^*c,e>.
```

Thus pullback carries minimum-norm harmonic representatives to harmonic
representatives.  Transfer after pullback is multiplication by the covering
degree.  For either degree-three map from the Iwahori cover this gives

```text
res_i^* res_i=3 I.                                      (1)
```

After identifying the two transported vertex complexes, the
cross-correspondence is the unnormalised double-coset Hecke correspondence at
`2`:

```text
res_1^* res_2=T_2.                                      (2)
```

These are identities of finite cellular cochain correspondences, before any
analytic realization.  Reversing a double coset gives its cellular adjoint
because pullback and transfer are adjoint in the weighted cellular norm.  The
unramified spherical Hecke algebra at `2` is commutative and closed under this
involution; its action here is therefore a genuine star representation.
Consequently `T_2` commutes with `T_2^*` and is normal for the cellular Hodge
inner product.  This is the point that permits an eigenvalue bound to become
an operator-norm bound without changing to the Petersson metric.

Pass to an odd principal congruence kernel on which the coefficient module
is trivial.  With the induced weighted inner product, cellular Shapiro is
unitary and identifies coefficient cohomology with the appropriate
deck-group isotypic component of scalar cohomology.  All the correspondences
above commute with the deck action.  The cuspidal subspace is invariant under
both `T_2` and `T_2^*`, hence reducing.  Its algebraic eigenvalues are the
weight-two Hecke eigenvalues (and their conjugates).  Deligne's bound
therefore gives, now using cellular normality rather than a change of norm,

```text
||T_2||_cell <= 2 sqrt(2).                              (3)
```

Finally `(1)`--`(3)` imply

```text
||res_1 f-res_2 g||_cell^2
 =3||f||_cell^2+3||g||_cell^2-2 Re<f,T_2g>_cell
 >=(3-2sqrt(2))(||f||_cell^2+||g||_cell^2),
```

which is `(CCH1)`.
