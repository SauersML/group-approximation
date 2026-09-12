# LXI: a moving spectral threshold obstructs every unitary when one represented side is finite rank

Date: 2026-09-05. Complete proof, internally reviewed with no unresolved
gap found. This is not external peer review or formal verification.
This gives an unrestricted mixed-unitary theorem under a new
coefficient-representation hypothesis. It does not settle LXI.

## 1. The finite-rank-side theorem

Let D be a unital C*-algebra, p a projection, and suppose there
is a unital representation

```text
rho:D -> B(H)
```

on an infinite-dimensional separable Hilbert space such that
rho(p) or rho(1-p) is a nonzero finite-rank projection. The
representation need not be faithful. In the full unital free
product C=C(S^1)*_C D, with circle generator z, one has

```text
||[z,WpW*]||=1   for every W in U(C).
```

There is no restriction on the unitary W, its coefficient
letters, products, linear combinations, or functional calculus.
This theorem includes the whole one-isometry Toeplitz coefficient
algebra and its range projection, even though that algebra is
not MF and has no finite-dimensional representation detecting
both sides of the range projection.

A second consequence concerns the full two-isometry coefficient
algebra itself. For its defect e=1-s_1s_1*-s_2s_2*,

```text
||[z,W e W*]||=1
```

for every unitary W in C(S^1)*T_2. Here W is genuinely
unrestricted in the full free product. The defect e is not
full, so this does not establish the required obstruction or
construction for a pair of properly infinite full projections.

If the representation space is finite-dimensional instead,
the earlier projective theorem applies when both rho(p) and
rho(1-p) are nonzero. The new proof below specifically uses
an infinite-dimensional Hilbert space to obtain a strongly
continuous path of self-adjoint unitaries with endpoints +1
and -1.

## 2. A strongly continuous threshold path

Identify H unitarily with L^2([-1,1],dt), and let A be
multiplication by the coordinate t. For a in [-1,1], set

```text
E_a=1_(a,infinity)(A),
V_a=2E_a-1.
```

Each V_a is a self-adjoint unitary. The spectral measure has
no atoms, so

```text
V_(-1)=1,   V_1=-1,
```

and a |-> V_a is strongly continuous. Explicitly, for any
xi in L^2([-1,1]),

```text
||(E_a-E_b)xi||^2
  = integral_(min(a,b))^(max(a,b)) |xi(t)|^2 dt ->0
```

as b tends to a. As V_a is self-adjoint, the path is also
strong-* continuous. It is not asserted to be norm continuous.

For each a, the universal property of the full free product
gives a unital representation pi_a:C -> B(H) with

```text
pi_a(z)=V_a,   pi_a(d)=rho(d) for every d in D.
```

The coefficient representation is fixed throughout. No
commutation relation between V_a and rho(D) is imposed.

For every fixed x in C, a |-> pi_a(x) is strongly continuous,
and the same holds for its adjoint. To verify this, first
take a *-polynomial in z,z* and finitely many coefficient
elements. Its image is a finite sum of products of uniformly
bounded strongly continuous operator paths, so is strongly
continuous. Such polynomials are norm dense in the full free
product. The representations are all contractive, so a single
norm approximation works uniformly in a. This gives the
assertion for arbitrary x, including arbitrary unitary W.

## 3. Finite-dimensional compression forces a zero eigenvalue

It suffices to treat the case P=rho(p) has finite nonzero
rank r. The other case follows by replacing p by 1-p, which
does not change the commutator norm.

Fix W in U(C), and set U_a=pi_a(W). Compress to the fixed
finite-dimensional space PH:

```text
M(a)=P U_a* V_a U_a P |_PH.
```

This is a self-adjoint r-by-r matrix. It is norm continuous
in a. Indeed, in any fixed orthonormal basis xi_1,...,xi_r
of PH its entries are

```text
<V_a U_a xi_j,U_a xi_i>,
```

which are continuous by strong continuity and uniform
boundedness. Entrywise continuity is norm continuity in
this finite-dimensional matrix space.

At the endpoints the middle operator is scalar, irrespective
of the endpoint values of U_a:

```text
M(-1)=1_PH,   M(1)=-1_PH.
```

The smallest eigenvalue of a norm-continuous self-adjoint
matrix path is continuous. It therefore vanishes at some
a_0 in (-1,1). Choose a unit vector xi in PH with

```text
P U_(a_0)* V_(a_0) U_(a_0) P xi=0.
```

Let eta=U_(a_0)xi and Q=U_(a_0)P U_(a_0)*. Then eta lies
in QH, has norm one, and

```text
Q V_(a_0) eta=0.
```

Hence V_(a_0)eta is a unit vector orthogonal to QH, and

```text
||[V_(a_0),Q]||>=1.
```

For every unitary u and projection q, the commutator has
off-diagonal contraction blocks in the q decomposition;
thus ||[u,q]||<=1. Consequently

```text
||pi_(a_0)([z,WpW*])||=1.
```

Contractivity of pi_(a_0) and the same universal upper bound
give the claimed equality in C.

The parameter a_0 may depend on W. A single fixed threshold
or a single fixed representation is not claimed to detect
every W. The moving finite compression and its endpoint
sign change are precisely what removes the earlier
requirement that the image of W commute with the test
unitary.

## 4. Every mixed unitary over the one-isometry Toeplitz algebra

Let T=C*(S) be the classical Toeplitz algebra on l^2(N_0),
where S is the unilateral shift. Its defining representation
has

```text
1-SS*=E_0,
```

a rank-one projection. Therefore, in C(S^1)*T, for every
unitary W,

```text
||[z,W SS* W*]||=1.
```

This includes all occurrences of the distinguished range
projection SS*, arbitrary uses of the entire isometry S
and its adjoint, and arbitrary further unitary functional
calculus. It is not a result only about a proper algebra
generated by selected real parts.

In fact the same conclusion holds for every nontrivial
projection p in T. The Toeplitz extension is

```text
0 -> K(l^2(N_0)) -> T -> C(S^1) -> 0.
```

Since S^1 is connected, the image of a projection p in the
commutative quotient is either zero or one. Thus p or 1-p
is compact in the defining representation. A compact
projection has finite rank, and for 0<p<1 this finite-rank
side is nonzero. The theorem applies.

The primary source for the compact ideal and circle quotient
is Coburn, *The C*-algebra generated by an isometry*,
Theorems 1 and 2, Bull. Amer. Math. Soc. 73 (1967), 722--726,
[DOI](https://doi.org/10.1090/S0002-9904-1967-11845-7).
The complete primary text was checked in the
[author-uploaded copy](https://www.researchgate.net/publication/253055864_The_-algebra_generated_by_an_isometry).

## 5. Isometric transport to the original T_2 problem

Let s_1,s_2 be the generators of T_2. The unital coefficient
subalgebra C*(1,s_1) is a faithful copy of the classical
Toeplitz algebra. This can be seen directly in the standard
binary Fock representation: the isometry L_1 is a direct
sum of unilateral shifts, with multiplicity space
ker(L_1*). Its generated algebra is the corresponding
faithful amplification of C*(S).

The full unital free-product inclusion theorem gives an
isometric inclusion

```text
C(S^1)*C*(1,s_1) -> C(S^1)*T_2.
```

The precise source is Armstrong--Dykema--Exel--Li,
*On embeddings of full amalgamated free product C*-algebras*,
Proposition 2.2, keeping the common amalgamating algebra C
unchanged ([primary paper](https://arxiv.org/pdf/math/0210448)).

Consequently, in the original free product,

```text
||[z,W(s_1s_1*)W*]||=1
```

for every W in U(C*(z,s_1)). The one-isometry range projection
and all its mixed unitary expressions are allowed. Both
complementary projections are properly infinite and full
in the ambient C(S^1)*T_2, since 1-s_1s_1* contains s_2s_2*.

The multiplicity-one coefficient representation used in the
proof has a rank-one complement for SS*. It is not asserted
to extend to a representation of all of T_2: there is no
room in that complement for the range of a second isometry.
The isometric subalgebra inclusion, not an extension of that
representation, transports the norm conclusion.

The same inclusion argument transports this result to
C*(v,s_1) inside A*T_2 for any full-spectrum unitary v in A.

## 6. An unrestricted full-T_2 result for the defect projection

The entire T_2 has a unital Fock representation on the
infinite-dimensional binary Fock space, with

```text
rho(s_i)=L_i,
rho(e)=E_Omega,
e=1-s_1s_1*-s_2s_2*.
```

Its defect has rank one. Apply the general theorem with
D=T_2 and p=e. It yields

```text
||[z,W e W*]||=1
```

for every W in U(C(S^1)*T_2), without restricting the
allowed mixed unitary algebra at all. The same is true
with e replaced by 1-e, or by any nonzero projection of
the Toeplitz compact ideal in its faithful Fock realization.

These projections do not solve the BRR problem. In
particular e is not full even in the free product: the
nonzero quotient onto C(S^1)*O_2 kills e. Its unitary
conjugates remain nonfull. This consequence is an exact
obstruction for unrestricted mixed unitaries, but for
the wrong projection class to decide LXI.

## 7. The remaining simultaneous coefficient problem

This result crosses the distinguished-projection barrier
for the entire one-isometry coefficient algebra. Its proof
uses a moving spectral threshold and a finite compression,
rather than enlarging the earlier fixed commutant algebra.
It also treats completely unrestricted full-T_2 unitaries
when the initial projection has a finite-rank side in the
coefficient representation.

The unresolved case remains the simultaneous use of both
Toeplitz isometries with p=s_1s_1*. No unital representation
of T_2 can make either rho(p) or rho(1-p) nonzero finite
rank: rho(p) is the range of an isometry on the whole
representation space, while rho(1-p) contains the range
of the second such isometry. The space cannot be finite
dimensional because those two orthogonal isometries exist.

Therefore the new theorem does not apply to that full
coefficient/projection pair. It supplies neither a strict
universal commutator nor a null-homotopy or surviving
free-envelope component. LXI remains open.

## Internal review

The root reviewer accepted the proof after checking the moving
threshold construction, strong continuity for arbitrary represented
free-product unitaries, norm continuity of the finite compression,
its scalar endpoint signs, and the zero-eigenvalue argument giving
an off-diagonal block of norm one. The review also checked the
one-isometry transport and the distinction between the nonfull
Toeplitz defect and the properly infinite full projection pair
required by BRR. No unresolved mathematical gap was found.
This is an internal review, not external peer review or formal
proof verification.
