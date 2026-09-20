# Stable Sym4 amplifications are excluded by associativity

2026-09-20. The non-residually-finite hyperbolic-group target remains OPEN.
This artifact proves a uniform representation-family obstruction, not
persistence of a central twist in all finite quotients.

## 1. Result and scope

Let `S=PSL_2(F_19)` and use the pinned triangle edge generators

```
x12=[[2,11],[16,3]], x13=[[5,11],[4,9]], x23=[[6,15],[12,8]].
```

Let `rho=Sym^4` of the natural two-dimensional representation, which
descends from `SL_2(F_19)` to `S`. For a nonzero triple `d in F_5^3`,
form the central five-twisted triangle with relations
`s_i(xij)=Z^(dij)s_j(xij)`, `Z^5=1`, and `Z` central.

**Theorem.** For every algebraically closed field `K` of characteristic
19 and every integer `m>=1`, there is no representation of this twisted
triangle in `GL_(5m)(K)` taking `Z` to a nontrivial scalar and taking
each canonical vertex representation to a conjugate of `rho tensor I_m`.

In particular no finite extension of `F_19` supplies such a detector.
All multiplicities, including those divisible by 19, are excluded.
No assumption that the multiplicity-space intertwiners commute is made.
The argument actually gives inconsistency of the normalized equations
over every nonzero unital associative algebra over the specified field
of 361 elements. Mixed vertex constituents, other characteristics, and
arbitrary finite detectors are outside this theorem.

The earlier `hrf-break-sym4-five-twists-have-no-detectors` result only
settled `m=1` using commutative polynomial identities. Those identities
were not evaluated on noncommuting matrices here. The new certificates
are linear elimination and ordered-product associativity identities.

## 2. Exact edge equations and the noncommutative gauge

Set `k=F_19[z]/(z^2-4z+1)`; `z` is a primitive fifth root. Write
`A=rho(x12)`, `B=rho(x13)`, `C=rho(x23)`. Column `i` of `rho(g)`,
for `g=[[a,b],[c,d]]`, contains the coefficients of
`(aX+cY)^(4-i)(bX+dY)^i` in the ordered degree-four monomials.

Fix vertex one by a simultaneous conjugation. The three vertex maps
are `rho tensor I_m`, `U(rho tensor I_m)U^-1`, and
`V(rho tensor I_m)V^-1`. Put `W=V^-1 U`. If `Z` maps to `zI`,
the three edge equations are exactly

```
UA=z^a AU, VB=z^b BV, WC=z^c CW, U=VW,
(a,b,c)=(-d12,-d13,d23),                         (1)
```

where scalar matrices are implicitly tensored with `I_m`. Any other
nontrivial scalar image of `Z` changes the nonzero exponent triple.
All 124 nonzero triples are treated individually.

Choose eigenbases `P_B,P_C` with the ordered eigenvalues
`1,z,z^2,z^3,z^4`, and let `T_e e_j=e_(j-e mod5)`. Distinctness of
these eigenvalues shows that all invertible edge intertwiners are

```
V=(P_B tensor I_m)(T_b tensor I_m)diag(V0,...,V4)(P_B^-1 tensor I_m),
W=(P_C tensor I_m)(T_c tensor I_m)diag(W0,...,W4)(P_C^-1 tensor I_m),
```

with every `Vj,Wj` invertible in `Mat_m(K)`. This follows from the
individual eigenspace equations; each eigenspace has dimension `m`.

The normalization `V0=W0=I_m` requires a genuine vertex gauge, not
independent scalar rescaling. Multiplicity operators commute with
every `rho(g) tensor I_m`. Thus replacing `U` by `U(I tensor R)`
and `V` by `V(I tensor S)` leaves both vertex maps unchanged and gives

```
W'=(I tensor S^-1)W(I tensor R),
Vj'=Vj S, Wj'=S^-1 Wj R.
```

Take `S=V0^-1` and `R=W0^-1 V0^-1`. Then `V0'=I` and
`W0'=V0 W0 W0^-1 V0^-1=I`. The first edge equation is preserved
because `R` commutes with `A tensor I_m`. No interchange of the
noncommuting factors `V0,W0` occurs. The root lane independently
reviewed this gauge and returned PASS.

It is now sufficient to rule out the normalized equations even without
requiring the remaining eight blocks to be invertible. That stronger
normalized inconsistency is what the certificates prove.

## 3. A finite-dimensional ordered-product reduction

For each triple define the scalar matrices

```
E_i=P_B T_b e_ii P_B^-1, F_j=P_C T_c e_jj P_C^-1.
```

Then `V=sum E_i tensor Vi`, `W=sum F_j tensor Wj`. Form a matrix
`L` with 25 rows and 25 columns: column `5i+j` is the flattened
matrix `E_i F_j A-z^a A E_i F_j`. Thus the remaining equation is

```
L (Vi Wj)_(i,j)=0,                              (2)
```

with the multiplication order precisely `Vi Wj`. In particular
this linear identity is valid with coefficients in any associative
`k`-algebra; it does not identify `Vi Wj` with `Wj Vi`.

The boundary columns, in order, are
`[0,1,2,3,4,5,10,15,20]`, representing
`1,W1,W2,W3,W4,V1,V2,V3,V4`. The other sixteen columns are interior.
Each certificate contains a matrix `H` of size `4x25` with

```
H L_interior=0.
```

Consequently `R=H L_boundary` gives four linear relations on those
nine boundary terms. The certificate specifies four free variables
among the eight nonconstant ones and their affine expressions in
`1,x1,x2,x3,x4`. Verification checks that the other four coefficient
columns of `R` are invertible, that the four free expressions are
exactly `x1,...,x4`, and that all four relations vanish after this
substitution. These conditions prove that every normalized solution
has the supplied affine form; there is no unsupported elimination.

Substitution in all 25 equations (2), without commuting letters,
gives a coefficient matrix `Q` in the ordered words

```
1,x1,x2,x3,x4, x1x1,x1x2,...,x4x4.
```

Write `Q=[Q_low | Q_quad]`. For all 124 triples, `Q_quad` has rank
16. Each certificate selects an invertible sixteen-row minor and
supplies a `16x5` table `M` satisfying

```
Q_quad M + Q_low = 0.                           (3)
```

The verifier checks (3) for all 25 rows, and independently inverts
the selected minor. Therefore the original substituted equations
imply all sixteen identities

```
x_i x_j = sum_(h=0)^4 M_(4(i-1)+j-1,h) e_h,
e_0=1, e_h=x_h for h>0.                         (4)
```

This is a scalar row-operation consequence of the original equations,
not a guess at a multiplication table. No inverse-block equations
are used after the legitimate normalization.

## 4. Associativity gives an explicit unit contradiction

On the five-dimensional vector space with basis `e0,...,e4`, make
`e0` a two-sided identity and prescribe `e_i * e_j` by the table `M`
for `i,j>0`, extending bilinearly. This product need not be associative.

Any associative-algebra solution of (4) defines a linear map `phi`
from this space by `e0 -> 1`, `ei -> xi`. Equation (4) and unitality
give `phi(u*v)=phi(u)phi(v)` for all vectors `u,v`. It follows that
every vector

```
r_ijh=(e_i*e_j)*e_h-e_i*(e_j*e_h),  1<=i,j,h<=4,
```

lies in `ker(phi)`. These are sixty-four explicitly computable vectors.
For every nonzero twist the certificate selects five of them and
coefficients `lambda_l in k` such that

```
sum_(l=1)^5 lambda_l r_(i_l,j_l,h_l) = e0.       (5)
```

The independent verifier recomputes these associators from the table
and checks (5) by exact field arithmetic. Applying `phi` yields
`0=1`. This is impossible in `Mat_m(K)` for every positive `m`.
All operations used scalar linear combinations and ordered associative
products, so the proof is uniform in `m` and extension field.

This proof does not need a claim that a nonassociative multiplication
table itself describes an associative algebra. Its failure of
associativity is exactly the contradiction: an associative solution
would annihilate all associators, and they explicitly span the unit.

## 5. Certificate, independent verification, and resource receipt

Files in this directory:

- `hrf-amplified-linear-probe.py`: exact Sage construction and certificate extraction.
- `hrf-amplified-certificates.json`: pinned edge matrices/eigenbases and all 124 certificates.
- `hrf-amplified-verify.py`: independent standard-library arithmetic verifier.
- `hrf-amplified-results.json`, `hrf-amplified-run.out`, `hrf-amplified-verify.out`: exact receipts.

The generator reads the prior pinned scalar-family input, never its
Groebner certificates. The bundle copies that input. The independent
verifier reconstructs the three Sym4 matrices directly from the
displayed two-by-two matrices, checks fifth powers, inverts `P_B,P_C`,
and verifies the ordered eigenvalue identities. It then reconstructs
every `E_i,F_j,L,Q`; checks the linear consequences, complete affine
parameterizations, table consequences of the actual equations, and
all 124 associator-unit identities. It checks exact coverage with
no repeated or omitted nonzero triple.

Field entries are encoded by the integer `a+19b` for `a+bz`. The
standard-library verifier builds exact addition/multiplication tables
using `z^2=4z-1`; those tables are accelerators, not external data.
Its Sym4 implementation uses repeated multiplication of binary linear
forms, independently of the original Sage binomial implementation.

The full certificate generation completed in **9.3046 seconds** and
the independent verifier returned **PASS in 1.2731 seconds**. Both
ran on MSI `acn112`, CPU affinity 0, nice level 19, with a 30-second
outer wall cap and 28-second CPU cap. All input, output, temporary
and Sage-cache storage was under

```
/projects/standard/hsiehph/sauer354/hrf-amplified-2026-09-20
```

The bounded five-case preliminary probe first found the five-dimensional
associator obstruction. One later five-case run failed only while
serializing Sage integers to JSON; after explicit conversion it passed.
The failed serialization is not counted as evidence. No local
computation ran, no packages were installed, no jobs remain running,
and no timeout required a retry. This is independently replayable
finite-arithmetic evidence, not a Lean formalization. Parent reviewed
the gauge. A separate sibling review subsequently checked the complete
written reduction and verifier source: the four-variable elimination,
rank-sixteen table implication from all original equations, ordered
associator calculation, and all-multiplicity scope. It returned PASS on
20 September 2026, using the existing MSI receipt without claiming a
second execution. This is internal review, not external human certification.

## 6. Prior work and non-duplication

Read the current wave-four audit, visibility, and class-two artifacts,
and searched the research graph for stable/amplified Sym4 claims.
Those lanes treat other quotient sectors, congruence images, or marked
nilpotent obstructions, not this noncommuting multiplicity problem.
The immediate prior scalar-family result is explicitly distinguished.

The general method of noncommutative reduction and overlap checks is
classical, not claimed as new: see Bergman's *The diamond lemma for
ring theory*, Advances in Mathematics 29 (1978), 178--218, and the
author's [corrections and historical credit](https://math.berkeley.edu/~gbergman/papers/updates/diamond.html).
Presenting algebras by generators, ordered relations, and multiplication
tables is also standard; compare Neeman--Ranicki--Schofield,
[*Representations of algebras as universal localizations*](https://www.maths.ed.ac.uk/~v1ranick/papers/reps.pdf),
Section 1. Neither source proves this pinned-triangle computation;
the present proof supplies its own complete elementary reduction and
certificates. No priority claim is made. No Liu or Thom approximation
theorem is used in this representation-family exclusion.
