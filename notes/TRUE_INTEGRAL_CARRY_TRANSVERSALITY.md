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

The exact nonlinear formula in
`TRUE_NONLINEAR_DISCRIMINANT_REPAIR_FORMULA.md` sharpens `(ICT8)` to
`rep_A<=Theta(A)/sigma_+(A) def_A` and sharpens `(ICT10)` to
`Theta(A)<=sqrt(1+(||A||C)^2)`.  More strongly, it writes the optimal repair
constant itself as a finite paired-discriminant envelope.

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

## 5. Real expansion alone cannot bound the carries

The extra lattice condition is not a disguised consequence of a real
spectral gap, even for uniformly sparse integral matrices.

Let `Gamma_n` be connected `d`-regular graphs with `|V_n|=n` and a uniform
unnormalized Laplacian gap `lambda_2(Gamma_n)>=lambda>0`.  Orient the edges
arbitrarily and let

`B_n:R^(E_n) -> R^(V_n)`                              `(ICT24)`

be the signed incidence matrix.  Then

`ran(B_n)=1^perp`,
`sigma_+(B_n)=sqrt(lambda_2(Gamma_n))>=sqrt(lambda)`,
`||B_n||<=sqrt(2d)`.                                  `(ICT25)`

Thus this family has exactly the uniform real gap and operator-norm bound in
`(ICT11)`.  Nevertheless

`Theta(B_n)>=sqrt(n)`.                                `(ICT26)`

Indeed, fix a vertex `v` and take `z=e_v in Z^(V_n)`.  Its distance to the
zero-sum real hyperplane is

`dist(e_v,1^perp)=1/sqrt(n)`.                         `(ICT27)`

On the other hand,

`1^perp intersect Z^(V_n)={ell in Z^(V_n):sum ell=0}`. `(ICT28)`

The zero vector is at distance one from `e_v`, and every nonzero vector in
the lattice `(ICT28)` has an integer coordinate pattern forcing distance at
least one.  Hence `dist(e_v,L_(B_n))=1`, proving `(ICT26)`.

There is also a direct near-cocycle witness.  Let

`w=e_v-(1/n)1`,                                       `(ICT29)`

and choose `x perpendicular ker(B_n)` with `B_n x=w`.  The nearest integer
vector to `w` is `e_v`, so

`def_(B_n)(x)=1/sqrt(n)`.                             `(ICT30)`

For every exact point `y`, the vector `B_n y` belongs to the lattice
`(ICT28)`, and `w` has distance `sqrt(1-1/n)` from that lattice.  Therefore

`||x-y|| >= ||B_n(x-y)||/||B_n||`
`          >= sqrt(1-1/n)/sqrt(2d)`.                 `(ICT31)`

Consequently the optimal circle repair constant is at least

`sqrt(n-1)/sqrt(2d)`.                                 `(ICT32)`

This example is degree zero rather than the relator map of the target group,
so it is a calibration, not a counterexample to the selected-chart program.
It proves that bounded degree, expansion, and the property-`(T)`-type real
gap cannot by themselves supply the nonlinear step.  Some integral
cosystolic or carry-lattice input is logically necessary.

## 6. A fixed integral generalized inverse is sufficient

There is a purely algebraic condition which supplies both missing estimates
at once.

**Proposition 3 (integral splitting criterion).**  Let `A:E->F` preserve the
integer lattices.  Suppose there is an integer-lattice-preserving map
`B:F->E` such that

`A B A=A`.                                             `(ICT33)`

Put `P=A B`.  Then

`Theta(A)<=||1-P||`                                   `(ICT34)`

and, for every `x`,

`rep_A(x)<=||B|| ||P|| def_A(x)`.                     `(ICT35)`

**Proof.**  Equation `(ICT33)` makes `P` a projection onto `W=ran(A)`.
It preserves the integer lattice, so `Pz` belongs to `L_A` for every
`z in F_Z`.  For any `w in W`,

`||z-Pz||=||(1-P)(z-w)||<=||1-P|| ||z-w||`.           `(ICT36)`

Taking the infimum over `w` proves `(ICT34)`.

For `(ICT35)`, choose `z in F_Z` nearest to `Ax` and put `ell=Pz`.  Then

`Ax-ell=P(Ax-z)`.                                     `(ICT37)`

Set `u=B(Ax-ell)`.  Since `Ax-ell` lies in `W`,

`Au=P(Ax-ell)=Ax-ell`.                                `(ICT38)`

Thus `y=x-u` satisfies `Ay=ell in F_Z`, while

`||x-y||=||u||<=||B|| ||P|| def_A(x)`.                `(ICT39)`

End proof.

Now let `D` be a fixed presentation relator matrix over `Z[G]`.  If there is
a matrix `B` over `Z[G]` with

`D B D=D`,                                             `(ICT40)`

then every finite permutation specialization of `D` and `B` satisfies
`(ICT33)`.  Their operator norms are bounded uniformly by the fixed
group-ring coefficient `l1` norms.  Proposition 3 therefore proves uniform
circle-cocycle repair on all those exact charts, with no separate appeal to
property `(T)`.

Condition `(ICT40)` is intentionally strong: it says that the universal
relator range has a fixed integral splitting.  The present argument does not
show that the property-`(T)` presentations relevant to the main problem have
such a splitting.  Its value is to identify an algebraic certificate that
would settle the carry problem immediately, and to separate that certificate
from real closed-range statements.

### The universal integral splitting is impossible for one-ended groups

There is a structural obstruction to using `(ICT40)` for the present
property-`(T)` group.

**Proposition 4.**  Let `G` be infinite, finitely presented, and one-ended,
and let `D=d1` be the relator matrix of any finite presentation over
`Z[G]`.  There is no matrix `B` over `Z[G]` satisfying

`D B D=D`.                                             `(ICT41)`

**Proof.**  The beginning of the presentation resolution computes
`H^1(G,Z[G])` as

`ker(d1)/im(d0)`.                                     `(ICT42)`

The Specker--Houghton ends theorem gives
`H^1(G,Z[G])=0` for an infinite one-ended finitely generated group.  Hence

`ker(D)=im(d0)`.                                      `(ICT43)`

If `(ICT41)` held, then

`P=1-BD`                                              `(ICT44)`

would be a `Z[G]`-module projection onto `ker(D)`: one has `DP=0`, while
`P` is the identity on `ker(D)`.  Thus `im(d0)` would be a direct summand.

Because `G` is infinite, the regular module has no nonzero invariant vector,
so `d0:Z[G]->Z[G]^S` is injective.  A splitting of its image would therefore
give a module row `L` with

`L d0=1`.                                             `(ICT45)`

Every entry of `d0(1)` is `s-1` (up to the left/right convention).  Applying
the augmentation `epsilon:Z[G]->Z` to `(ICT45)` gives `0=1`, a
contradiction.  End proof.

In particular, `SL_3(Z)` is one-ended: property `(T)` implies property
`(FA)`, while Stallings' theorem would give a nontrivial tree action if it
had more than one end.  Thus an autonomous search for one fixed group-ring
matrix `B` in `(ICT40)` is mathematically dead.

This does not rule out uniformly bounded chart-dependent splittings over
the finite permutation lattices, nor does it rule out `(ICT12)`.  Those
finite lattices can split even though the universal regular module does not.
The compute target must therefore measure or construct the finite-chart
carry lattice itself rather than solve one universal `DBD=D` equation.

References for the only external input in the proof are W. H. Houghton,
[*Ends of Groups and the Associated First Cohomology
Groups*](https://doi.org/10.1112/jlms/s2-6.1.81), and the standard
property-`(T)` to property-`(FA)` implication recorded in
Bekka--de la Harpe--Valette, *Kazhdan's Property (T)*, Theorem 2.3.6.

## 7. Calibration against coefficient-independent cosystolic expansion

Oppenheim--Valentiner-Branth prove that suitable Kac--Moody--Steinberg
complexes are cosystolic expanders, with constants that work for every
finitely generated abelian coefficient group.  This removes one apparent
coefficient-cardinality objection: the coordinates of any cochain on one
finite chart generate a finitely generated subgroup of `T`.

The theorem cannot be substituted directly for `(ICT12)`, because its norm
is the support/Hamming norm.  A curvature which is nonzero but
infinitesimal on every cell has full Hamming support and arbitrarily small
chordal `L2` norm.  The latter is the norm occurring in a normalized
Hilbert--Schmidt phase model.  Thus coefficient-independent Hamming
cosystolic expansion does not, as a black box, bound the carry
transversality constant.

The constructive part of that work is nevertheless relevant: its link
expansion is obtained from integral cone functions.  The useful next audit
is whether those cone operators assemble into a generalized inverse or a
uniformly bounded integral projection of the form `(ICT33)--(ICT40)` for the
global degree-one relator maps.  Such an operator would give chordal `L2`
repair by Proposition 3, independently of the support metric.

Primary sources:

* Izhar Oppenheim and Inga Valentiner-Branth,
  [*New cosystolic high-dimensional expanders from KMS groups*](https://arxiv.org/abs/2504.05823),
  Theorems 1.1 and 1.2.
* Lukas Gohla and Andreas Thom,
  [*High-dimensional expansion and soficity of groups*](https://arxiv.org/abs/2403.09582),
  for the earlier arbitrary-finite-abelian coefficient construction and its
  explicitly conditional application to soficity.

## 8. What remains for the main problem

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
