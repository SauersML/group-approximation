---
rg: 2
id: companion-parabolic-compression-defect-is-trivial-proof
kind: route
title: Compute the affine centralizer and use the Laurent determinant to eliminate stable-letter centralizers
target: companion-parabolic-compression-defect-is-trivial
requires:
  - torsion-free-lef-kazhdan-non-rf-seed
  - compression-defect-dies-in-finite-dimensions
  - mapping-torus-mf-radical-lies-in-finite-residual
---

## 1. The descended automorphism and strict compression

Conjugation by `D=diag(qP,I_3,q)` gives exactly `(CP2)`.  Since
`P(S^m)=S^m`, it preserves the central subgroup being killed and its inverse
does as well.  It therefore descends to an automorphism, not merely an
endomorphism, of `J_m`.

On `A_m(S)` the Levi block is fixed and the row module is sent to

```text
qP Mat_(m x 3)(S)=q Mat_(m x 3)(S).
```

This is properly contained in the original row module because `q=t^d` is not
a unit of `S`.  Property `(T)` of `A_m(S)` is the standard universal-lattice
affine argument: `EL_3(S)` has property `(T)`, the pair with one natural row
module has relative property `(T)`, and a finite direct sum of row modules is
handled by finitely many applications of the extension criterion.

If `K` is invariant and finite index, then `L=K intersect A_m(S)` is finite
index in `A_m(S)` and remains Kazhdan.  The compression remains strict.  Its
intersection with the pure row group is a finite-index additive subgroup
`Lambda` of `Mat_(m x 3)(S)`.  Such a subgroup cannot be contained in
`t Mat_(m x 3)(S)`, since the latter has infinite index.  On the other hand,
the pure-row part of `phi(L)` is contained there.

## 2. The centralizer inside the parabolic quotient

First compute the centralizer of `L` in `J_m`.  A finite-index subgroup of
`EL_3(S)` contains a nonzero integral power `e_ij(N_ij)` of each elementary
matrix `e_ij(1)`.  If a representative `x=(U,h,v,c)` centralizes `L`, its
image modulo the full centre centralizes all these elementary matrices.

The centralizer in `Mat_3(R)` of the six matrices `e_ij(N_ij)` is the scalar
matrices: the usual entry-by-entry computation works because every `N_ij` is
nonzero and `R` is a domain.  Since `h in EL_3(R)` has determinant one, its
scalar is a unit `lambda` with `lambda^3=1`; the only such Laurent unit is
`1`.  The same commutation equations say that the row part `U` and column
part `v` are fixed by all the elementary powers, hence both vanish.  Therefore

```text
C_(J_m)(L)=Z(J_m)=C(R)/C(S^m).                         (CP7)
```

Central errors caused by passing from `H_m` to `J_m` do not affect this
argument: all equations used above are read first in the centre-free quotient
`H_m/C(R)`.

## 3. No centralizer can carry a stable-letter exponent

Write an arbitrary element of `G` as `x s^n`, where `s` is the positive
stable letter and `x in K`.  Suppose it centralizes `L`.  Apply the equality

```text
(x s^n) u (x s^n)^(-1)=u                               (CP8)
```

to every pure row `u in Lambda`.  If `h_x` is the middle `EL_3(R)` block of
`x`, comparison of the row coordinates gives

```text
q^n P^n u h_x^(-1)=u             for every u in Lambda. (CP9)
```

The finite-index subgroup `Lambda` spans
`Mat_(m x 3)(Q(t))`, so `(CP9)` says that the corresponding linear map on
this `3m`-dimensional vector space is the identity.  Its determinant is

```text
det(q^n P^n)^3 det(h_x^(-1))^m
  = q^(3mn) det(P)^(3n).                               (CP10)
```

Here `det(h_x)=1` and `det(P)=+-1`.  Since `q=t^d`, `(CP10)` can equal `1`
only when `n=0`.  Equation `(CP7)` now puts `x` in `Z(J_m)`.  This proves
`(CP4)`.

## 4. Every defect vanishes

The subgroup `K` is normal in `G`, and conjugation by every element of `G`
restricts to an automorphism of `K` induced by an inner automorphism and a
power of `phi`.  Both preserve `K intersect Z(J_m)`.  Thus if a root `c`
centralizes `L`, `(CP4)` says it lies in this central subgroup, and its
transport by any proposed compressor is still central in `J_m`.  It therefore
commutes with every element of `L`.  All pointwise commutators defining the
compression defect are the identity, proving `(CP5)`.

## 5. Every other compression defect is still trapped in the central tail

Pass from `J_m` to the quotient by its full centre.  As in the
Kida--Tucker-Drob parabolic calculation, this quotient is the semidirect
product

```text
Gamma_m = EL_3(R) semidirect
          (Mat_(m x 3)(R) directProduct R^3).           (CP11)
```

Over `F=Q(t)`, the additive factor is finite-dimensional and the displayed
semidirect product has its faithful affine representation.  The automorphism
induced by `phi` acts on that additive factor by

```text
T(U,v)=(qPU,q^(-1)v).
```

This `T` commutes with the `EL_3` action.  Therefore conjugation by
`diag(T,1)` in the affine representation implements `phi`, and the affine
representation extends to a finite-dimensional representation

```text
Pi : G -> GL_N(F).                                     (CP12)
```

The kernel of `Pi` on `K` is exactly the surviving central tail
`K intersect (C(R)/C(S^m))`; in particular `Pi` is nontrivial on `K`.

By `compression-defect-dies-in-finite-dimensions`, the intrinsic
compression--centralizer defect of every subgroup of `G` lies in `ker Pi`.
The single-core `defectNormal` is contained in that intrinsic defect.  Hence
every core in `G` satisfies `(CP5')`.  Since the image of `K` in `Gamma_m` is
a nontrivial finite-index subgroup, the central tail is proper in `K`; no
core in this mapping torus can have `defectNormal=K`.

## 6. The companion calculation

For the matrix in `(CP6)`, direct multiplication gives

```text
P^(-1) = [ 0  1 ],            P+P^(-1)=t I_2.
          [-1  t ]
```

It follows that `e_2=-P^(-1)e_1`, while multiplication by `t` is the Laurent
polynomial `P+P^(-1)` in the cyclic actor.  Induction gives every
`t^k e_i`, proving the final module assertion in the claim.
