# Circle-cocycle repair is exactly an integral carry transversality problem

Date: 2026-08-11

## 1. Purpose

`TRUE_PROPERTY_T_LINEAR_COCYCLE_GAP.md` proves a uniform real-linear
degree-one repair bound for every exact unitary action of a finitely
presented property-`(T)` group.  This note identifies, without approximation
or computation, the additional datum needed to upgrade that theorem to
circle-valued cocycles.

For a finite exact permutation chart, let `A=d1` be the real relator map.
Its circle version is the torus homomorphism induced by the same integral
matrix.  Approximate circle cocycles are points `x` for which `Ax` is close
to an integer vector.  Exact circle cocycles are points for which `Ax` is
an integer vector.  The only difference is therefore whether a nearby
integer carry is close to an integer carry lying in the real range of `A`.

The theorem below makes this statement quantitative and reversible.  In the
property-`(T)` setting, qualitative circle stability on exact charts is
equivalent to one uniform lattice-transversality bound.

## 2. Finite integral setup

Let `E` and `F` be finite-dimensional real Hilbert spaces equipped with
full lattices `E_Z` and `F_Z`.  Let

`A:E -> F`, `A(E_Z) subset F_Z`.                       `(ICT1)`

Put

`W=ran(A)`, `L_A=W intersect F_Z`,                    `(ICT2)`

and let `sigma_+(A)` be the least positive singular value of `A`, namely

`sigma_+(A)=inf{||Au||:u perpendicular ker(A), ||u||=1}`. `(ICT3)`

For the zero map the assertions below are immediate; otherwise
`sigma_+(A)>0`.

The induced torus homomorphism is

`bar(A):E/E_Z -> F/F_Z`.                              `(ICT4)`

For a lift `x in E`, define its additive circle defect and repair distance
by

`def_A(x)=dist(Ax,F_Z)`,                              `(ICT5)`

`rep_A(x)=dist(x,A^(-1)(F_Z))`.                       `(ICT6)`

These depend only on the class of `x` modulo `E_Z`.  The exact circle
cocycle locus is `ker(bar(A))=A^(-1)(F_Z)/E_Z`.

Define the integral carry transversality constant

`Theta(A)=sup_(z in F_Z minus L_A)`
`             dist(z,L_A)/dist(z,W)`.                 `(ICT7)`

Use the value zero if the supremum is over the empty set.  Because `W` is a
rational subspace, projection of `F_Z` to `W^perp` is a lattice and
`Theta(A)<infinity` for each fixed finite matrix.  Uniform boundedness over
a growing family is the substantive condition.

## 3. Exact factorization theorem

**Theorem 1 (linear gap times carry transversality).**  For every `x in E`,

`rep_A(x) <= (1+Theta(A))/sigma_+(A) * def_A(x)`.      `(ICT8)`

Conversely, suppose a constant `C` satisfies

`rep_A(x) <= C def_A(x)` for every `x in E`.           `(ICT9)`

Then

`Theta(A) <= 1+||A|| C`.                              `(ICT10)`

Thus, for a family `(A_n)` with

`inf_n sigma_+(A_n)>0`, `sup_n ||A_n||<infinity`,     `(ICT11)`

the circle repair constants are uniformly bounded if and only if

`sup_n Theta(A_n)<infinity`.                          `(ICT12)`

**Proof of `(ICT8)`.**  Choose `z in F_Z` nearest to `Ax`.  Since `Ax` lies
in `W`,

`dist(z,W) <= ||z-Ax||=def_A(x)`.                    `(ICT13)`

Choose `ell in L_A` nearest to `z`.  By `(ICT7)`,

`||z-ell|| <= Theta(A) dist(z,W)`.                   `(ICT14)`

Consequently

`||Ax-ell|| <= (1+Theta(A)) def_A(x)`.               `(ICT15)`

The vector `Ax-ell` belongs to `W`.  There is a unique
`u perpendicular ker(A)` with

`Au=Ax-ell`,
`||u|| <= sigma_+(A)^(-1)||Ax-ell||`.                `(ICT16)`

Set `y=x-u`.  Then `Ay=ell in F_Z`, so `y` is an exact circle cocycle.
Equations `(ICT15)--(ICT16)` give `(ICT8)`.  End proof.

**Proof of `(ICT10)`.**  Fix `z in F_Z` and let `w` be its orthogonal
projection onto `W`.  Choose `x perpendicular ker(A)` with `Ax=w`.  Then

`def_A(x)=dist(w,F_Z) <= ||w-z||=dist(z,W)`.          `(ICT17)`

By `(ICT9)`, choose `y in A^(-1)(F_Z)` with

`||x-y|| <= C dist(z,W)+epsilon`.                    `(ICT18)`

The carry `ell=Ay` belongs to `W intersect F_Z=L_A`.  Therefore

`dist(z,L_A) <= ||z-ell||`
` <= ||z-w||+||A(x-y)||`
` <= (1+||A||C)dist(z,W)+||A||epsilon`.              `(ICT19)`

Let `epsilon` tend to zero and take the supremum over `z`.  This proves
`(ICT10)`.  End proof.

The use of additive geodesic distance on `R/Z` is harmless.  On the
principal interval it is uniformly bi-Lipschitz equivalent to chordal
distance in `T`, so the same theorem holds for the normalized `L2` chordal
defect used in the monomial model, with universal changes of constants.

## 4. Application to exact property-`(T)` charts

Fix a finite presentation `G=<S|R>` of a property-`(T)` group.  For every
finite exact `G`-set `V`, the permutation coefficient module gives an
integral relator matrix

`A_V=d1_V:C^1(V,R) -> C^2(V,R)`.                     `(ICT20)`

With normalized counting norms, the fixed presentation gives

`sup_V ||A_V||<infinity`.                             `(ICT21)`

Theorem 1 of `TRUE_PROPERTY_T_LINEAR_COCYCLE_GAP.md` gives

`inf_V sigma_+(A_V)>0`.                               `(ICT22)`

The kernel of the induced torus map is exactly the set of exact
`T`-valued phase cocycles on the chart.  Combining `(ICT8)--(ICT12)` gives:

**Corollary 2 (exact-chart circle criterion).**  The following are
equivalent.

1. There is a uniform `C` such that every circle-valued phase table on every
   finite exact `G`-set is within `C` times its relator defect of an exact
   circle cocycle.
2. The integral carry constants `Theta(d1_V)` are uniformly bounded over all
   finite exact `G`-sets `V`.

This criterion allows every exact cohomology sector.  In particular, a
nontrivial stabilizer character already lies in `ker(bar(A_V))` and has zero
repair distance.  The obstruction measured by `Theta` is instead an
integer carry lying very close to the real relator range but far from the
attainable carry lattice

`ran(d1_V) intersect C^2(V,Z)`.                       `(ICT23)`

## 5. What remains for the main problem

The vague instruction "control logarithmic carries" can now be replaced by
two precise questions.

1. **Exact charts.**  Prove `(ICT12)` for a suitable property-`(T)` model
   family, or construct integer carries showing that `Theta(d1_V)` diverges.
   Real or character-block spectra alone cannot decide this lattice
   condition.
2. **Approximate charts.**  Transfer the selected exact-chart statement to
   the approximately multiplicative permutation models carrying the
   prescribed relatively-Haar joining.  The exact identities used in
   `(ICT20)--(ICT22)` are not available on arbitrary sofic charts.

The first item is the complete nonlinear residue after the property-`(T)`
linear gap.  It is also visibly distinct from Popa model-surjectivity:
nonzero exact cohomology classes cause no problem, whereas a divergent
`Theta` records near-integral relator data with no nearby attainable exact
carry.
