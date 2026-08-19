# The paired Fourier fold is functorial on finite tangent modules

Date: 2026-08-11

## 1. Outcome

The paired Fourier--`Q` cell does not depend on the special module
`(Z/p^nZ)^3`.  It is a functorial construction for every finite abelian
tangent module with a perfect pairing and every finite group acting on that
module.

This matters for the radical construction because the acting finite group
can include the entire finite base elementary group, not only the
coefficient `SL_3`.  Once a finite Frobenius quotient of the full
square-zero tangent module has been selected, all of the following become
exact automatically:

1. additive tangent relations;
2. coefficient-`Q` covariance;
3. base-elementary conjugation covariance;
4. the common positive Fourier wall; and
5. the marked macroscopic fold.

Thus the remaining globalization problem has only one algebraic input:
construct finite paired tangent modules which realize every fixed positive
and Laurent coefficient window and for which the strict compressor is the
displayed Fourier interface.  Separate optimization of base elementary
matrices is unnecessary.

## 2. Finite paired module data

Let `W` be a finite abelian group with a chosen perfect biadditive
self-pairing

`beta:W times W -> Q/Z`.                              `(PFM1)`

Let a finite group `F` act on `W`.  Write `f^vee` for the adjoint action on
the second copy of `W`, characterized by

`beta(f^vee y,x)=beta(y,fx)`.                         `(PFM2)`

Fix a central scalar automorphism `q` of `W`, and fix `c in F`.
Put

`K=q^(-1)c^vee in Aut(W)`.                            `(PFM3)`

On

`H=ell^2(F times W times W)`                          `(PFM4)`

define, for `w in W`,

`A(w)delta_(g,x,y)=delta_(g,x+g^(-1)w,y)`,            `(PFM5)`

`D(w)delta_(g,x,y)`
` =exp(2 pi i beta(y,g^(-1)w))delta_(g,x,y)`.         `(PFM6)`

Let the acting group use left translation:

`L(f)delta_(g,x,y)=delta_(fg,x,y)`.                  `(PFM7)`

Then

`A(w+w')=A(w)A(w')`, `D(w+w')=D(w)D(w')`,            `(PFM8)`

and

`L(f)A(w)L(f)^(-1)=A(fw)`,
`L(f)D(w)L(f)^(-1)=D(fw)`.                           `(PFM9)`

No invariance assumption on `beta` is needed in `(PFM9)`: the group
coordinate `g^(-1)w` carries the covariance.

## 3. Fourier exchange and the right gauge

Let `Fourier_W:ell^2(W)->ell^2(W)` be the finite Fourier transform from the
chosen self-pairing `beta`, and let `J` swap the two finite module factors.
Put

`U=1_(ell^2(F)) tensor J(Fourier_W tensor 1)`.         `(PFM10)`

Finite Fourier duality gives

`U A(w) U^(-1)=D(w)`                                  `(PFM11)`

for every `w`.  Since `U` is constant on the `F` coordinate,

`[U,L(f)]=1`.                                         `(PFM12)`

Define the permutation unitary

`T delta_(g,x,y)=delta_(gc,c^(-1)x,Ky)`.              `(PFM13)`

It commutes with every left `F` operator.  Conjugating `(PFM5)` by `T`
changes the translation vector by

`c^(-1)(c g^(-1)w)=g^(-1)w`,                         `(PFM14)`

so

`T A(w)T^(-1)=A(w)`.                                  `(PFM15)`

For the multiplier family, `(PFM2)--(PFM3)` give

`beta(K^(-1)y,c g^(-1)w)=q beta(y,g^(-1)w)`.          `(PFM16)`

Hence

`T D(w)T^(-1)=D(w)^q`.                                `(PFM17)`

All identities are exact.

## 4. The common-positive paired cell

Set

`S_0=U^(-1)`, `S_1=U^(-1)T^(-1)`.                   `(PFM18)`

Equations `(PFM11)` and `(PFM15)` imply

`S_0 A(w)S_0^(-1)=S_1 A(w)S_1^(-1)`                 `(PFM19)`

for every `w in W`.  In the inverse direction,

`S_0^(-1)A(w)S_0=D(w)`,
`S_1^(-1)A(w)S_1=D(w)^q`.                            `(PFM20)`

Thus the two sectors agree literally on the whole common positive additive
module and on its common forward compressor image.  Their inverse images
differ by

`D(w)^(q-1)`.                                         `(PFM21)`

Suppose `q=1+p` and choose a marked `a in W` with `pa!=0`.  Perfectness of
`beta` makes the average of the nontrivial character
`y |-> exp(2 pi i beta(y,g^(-1)pa))` zero for every `g`.  Therefore

`tr_H(D(a)^p)=0`,
`||D(a)^p-1||_2^2=2`.                                 `(PFM22)`

If in addition `ca=qa`, the left operator `L(c)` scales both additive
models by `q`, commutes with `U,T`, and gives the exact coefficient part of
the Baumslag--Solitar stable-letter relation.

This proves the functorial paired-cell theorem.

## 5. Application to a full finite square-zero tangent layer

Let `B` be a finite Frobenius ring and let `I` be a finite square-zero
`B`-bimodule carrying the coefficient action of a finite quotient `Q_0`.
Assume the chosen Frobenius functional gives a perfect pairing on `I`.
Choose an elementary rank `r` for which the matrix trace pairing is
nondegenerate on the relative tangent module; over characteristic `p`, it
is enough in the split model to take `p` not dividing `r`.

The additive kernel

`W=ker(E_r(B directSum I)->E_r(B))`                   `(PFM23)`

is the finite tangent group (equivalently the appropriate trace-zero
matrix module in the stable split range).  The Frobenius functional and
matrix trace give a perfect duality `(PFM1)`.

Let

`F=<E_r(B),Q_0>`                                      `(PFM24)`

act on `W` by base conjugation and coefficient covariance.  It is a finite
group.  Applying Sections 2--4 with this `F` incorporates every base
elementary and coefficient-group relation in `(PFM9)`.  Nothing about the
proof distinguishes a coefficient generator from a base elementary
generator.

Consequently the open part is not extension of the marked three-dimensional
clock through separately optimized base matrices.  It is the construction
of a sequence

`(B_n,I_n,j_(+,n),j_(-,n))`                           `(PFM25)`

where `j_+` and `j_-` realize the tested positive and Laurent tangent
windows in one paired finite Frobenius module and identify the strict
compressor with `(PFM18)--(PFM20)` away from vanishing bad corners.

The fixed-base square-zero jet rings in `notes/NOTEPAD.md` supply exact local
candidates for `(B_n,I_n)`: mixed monomials survive, chamber matrices act by
automorphisms, and the Frobenius annihilator flags are explicit.  What is
not yet proved is a simultaneous positive/Laurent incidence and fusion
theorem for the selected finite word exhaustion.  The present functorial
theorem shows that proving that one module statement automatically closes
the base-elementary and coefficient-covariance parts of the FALSE endpoint.

## 6. Computational consequence

A finite search should now operate on module and incidence data, not dense
unitary matrices.  At one stage it should output:

1. a finite Frobenius module and its exact pairing matrix;
2. the positive and Laurent window maps `j_+,j_-`;
3. the finite automorphism matrices for the tested base and substitution
   generators;
4. the rank of every prefix-good intersection; and
5. exact verification of `(PFM19)--(PFM20)` on that intersection.

The unitary realization is then canonical Fourier/regular representation
theory.  A sequence with bad-rank fraction tending to zero triggers the
marked compatible-pair endpoint from
`FALSE_RADICAL_BS_PAIRED_FOURIER_Q_CELL.md`.  Conversely, a uniform rank
loss in these finite module problems would isolate the remaining
obstruction without another high-dimensional matrix optimization.
