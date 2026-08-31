---
rg: 2
id: fd-radical-kazhdan-projection-ccr-proof
kind: route
title: Push finite-dimensional image collapse through the Kazhdan projection
target: kt-ccr-holds-on-the-fd-tempered-adjoint-sector
requires:
  - fd-invisibility-of-compression
  - el-r-polynomial-robust-spectral-gap
  - ccr-for-coordinate-collapsing-models
---

## Step 1: a dimension-free fixed-vector estimate in exact representations

Let `S` be a finite Kazhdan set for `Lambda` with constant
`kappa>0`.  Let `rho:G->U(V)` be finite-dimensional and let `P_rho`
be the orthogonal projection onto `Fix(rho(Lambda))`.  By hypothesis
`rho(Lambda)=rho(Gamma)`, so

~~~text
ran(P_rho)=Fix(rho(Lambda))=Fix(rho(Gamma)).             (FDP1)
~~~

For a unit vector `eta` put

~~~text
epsilon=max_(s in S)||rho(s)eta-eta||.
~~~

The Kazhdan inequality gives

~~~text
||eta-P_rho eta||<=epsilon/kappa.                        (FDP2)
~~~

For every `gamma in Gamma`, equation `(FDP1)` and unitary invariance give

~~~text
||rho(gamma)eta-eta||
 <=2||eta-P_rho eta||
 <=2epsilon/kappa.                                      (FDP3)
~~~

Thus finite-dimensional image collapse has a dimension-free vector form.  No
choice of an element of `Lambda` representing `rho(gamma)` is needed.

## Step 2: the finite-dimensional radical element

Property `(T)` supplies the Kazhdan projection `p_Lambda` in the maximal
group C-star algebra of `Lambda`: in every unitary representation it is the
orthogonal projection onto the `Lambda`-fixed vectors.  View it in
`C^*_max(G)` through the subgroup inclusion.  For `gamma in Gamma` define

~~~text
a_gamma=(u_gamma-1)p_Lambda.                             (FDP4)
~~~

If `rho` is finite-dimensional, `rho(p_Lambda)=P_rho`.  Equation
`(FDP1)` therefore implies

~~~text
rho(a_gamma)=(rho(gamma)-1)P_rho=0.                      (FDP5)
~~~

Consequently

~~~text
a_gamma in I_FD(G)
 :=intersection_(rho finite-dimensional) ker(rho).       (FDP6)
~~~

This is the exact C-star-algebraic location of the compressor obstruction.

## Step 3: weak containment kills the obstruction

Let `pi_FD` be the direct sum of a representative set of all
finite-dimensional unitary representations of `G`.  A representation
`theta` is weakly contained in `pi_FD` exactly when

~~~text
ker(pi_FD) subset ker(theta).                            (FDP7)
~~~

Equations `(FDP5)--(FDP7)` give `theta(a_gamma)=0` for every
`gamma in Gamma`.  If `xi` is `Lambda`-fixed, then
`theta(p_Lambda)xi=xi`, and hence

~~~text
theta(gamma)xi-xi
 =theta((u_gamma-1)p_Lambda)xi
 =theta(a_gamma)xi
 =0.                                                     (FDP8)
~~~

This proves

~~~text
Fix(theta(Lambda))=Fix(theta(Gamma)).
~~~

For completeness, the same passage can be seen directly from `(FDP3)`.
Fell approximation of the coefficient of a `Lambda`-fixed unit vector by a
finite direct sum of finite-dimensional coefficients makes the approximating
vector `sqrt(2 delta)`-invariant on `S`.  Equation `(FDP3)` makes its
`gamma`-displacement at most `2sqrt(2 delta)/kappa`.  Sending
`delta` to zero forces the original `gamma`-coefficient to be one.

## Step 4: application to a relative commutant

Let `sigma:G->U(M)` be a homomorphism into a finite tracial von Neumann
algebra and let `Theta=Ad(sigma)` on `L^2(M)`.  If

~~~text
x in sigma(Lambda)' cap M,
~~~

then `x` is a `Lambda`-fixed vector for `Theta`.  Its cyclic space

~~~text
H_x=closure span{Theta(g)x:g in G}
~~~

is reducing for `Theta`.  If `Theta|_(H_x)` is weakly contained in
`pi_FD`, Step 3 gives

~~~text
Theta(gamma)x=x for every gamma in Gamma,
~~~

which is exactly `x in sigma(Gamma)' cap M`.

Let `z_FD` denote the orthogonal projection onto the closed sum of all
reducing subrepresentations of `Theta` weakly contained in `pi_FD`.
Arbitrary direct sums and subrepresentations preserve weak containment, so
this is the maximal FD-tempered subrepresentation and `z_FD` commutes with
`Theta(G)`.  If `x` is `Lambda`-fixed, so is `z_FD x`; Step 3 makes
`z_FD x` `Gamma`-fixed.  Therefore `z_FD x` belongs to
`L^2(sigma(Gamma)' cap M)`, and

~~~text
dist_2(x,L^2(sigma(Gamma)' cap M))
 <=||x-z_FD x||_2.                                      (FDP8b)
~~~

This includes the compact adjoint sector as a special case: a direct sum of
finite-dimensional representations is weakly contained in `pi_FD`.
It is strictly broader, because weak containment permits noncompact limits
of finite-dimensional representations.

## Step 5: strict inclusion has a unitary non-FD-tempered witness

Write

~~~text
P=sigma(Lambda)' cap M,       Q=sigma(Gamma)' cap M.
~~~

Suppose `Q proper-subset P`.  Choose a self-adjoint contraction
`b in P minus Q`.  Functional calculus in `P` gives the unitary

~~~text
v=b+i sqrt(1-b^2).                                      (FDP9)
~~~

Let `E_Q` be the trace-preserving conditional expectation.  Since
`b=Re(v)` and `E_Q` preserves adjoints,

~~~text
dist_2(b,Q)=||b-E_Q(b)||_2
 <=||v-E_Q(v)||_2
 =dist_2(v,Q).                                          (FDP10)
~~~

Thus `v notin Q`, and `v` is an op-norm-one witness.  Step 4 shows that its
cyclic adjoint representation cannot be weakly contained in `pi_FD`.
Every failure of (CCR) is therefore carried by a genuinely non-FD-tempered
`Lambda`-spherical adjoint module.

## Step 6: the pointed adjoint-lift form in matrix microstates

Now let `M=prod_U M_(d_n)` and let
`sigma=[pi_n]` be trace-faithful.  Choose unitary lifts for each fixed
group element.  On the normalized Hilbert--Schmidt space `M_(d_n)` define

~~~text
beta_n(g)=Ad(pi_n(g)).
~~~

For unitaries `U,V in U(d)`,

~~~text
||Ad(U)-Ad(V)||_(2,d^2)^2
 =2-2|tr_d(U^*V)|^2.                                    (FDP11)
~~~

Hence the group defects of `pi_n` tending to zero imply the group defects
of `beta_n` tend to zero.  Moreover,

~~~text
tr_(d_n^2)(beta_n(g))=|tr_(d_n)(pi_n(g))|^2,             (FDP12)
~~~

so trace faithfulness of `pi_n` makes the adjoint microstates trace-faithful
as well.

Lift the unitary `v` of Step 5 to unitaries `v_n`.  Under normalized
vectorization, `xi_n=vec(v_n)` are unit vectors and

~~~text
||beta_n(g)xi_n-xi_n||
 =||pi_n(g)v_n pi_n(g)^*-v_n||_(2,d_n).                  (FDP13)
~~~

Thus `v in sigma(Lambda)'` means the left side tends to zero for every
`s in S`, while `v notin sigma(Gamma)'` gives some
`gamma in Gamma` for which it does not tend to zero.  Equations
`(FDP11)--(FDP13)` prove the pointed-adjoint assertion in the claim.

There is an important normalization fence.  Nonzero action on the vectors
`xi_n` does not imply that the superoperator sequence
`beta_n(a_gamma)` has nonzero normalized Hilbert--Schmidt norm in dimension
`d_n^2`.  A rank-one superoperator has vanishing normalized mass but may move
one chosen unit vector.  What distinguishes the present vectors is their
matricial origin: each is the vectorization of an op-norm-one unitary.

## Step 7: what robust spectral gap leaves open

The established property `(T;FD)_rob` applies to the approximate adjoint
representations `beta_n|_Lambda`.  It isolates the low-energy sector of the
`Lambda` generator Laplacian with a dimension-independent gap.  This is the
coordinate shadow of `p_Lambda` and controls arbitrary normalized
Hilbert-space vectors relative to that low sector.

It does not identify the action of `gamma` on the low sector.  In exact
finite-dimensional representations, `(FDP5)` says this action is the
identity.  Passing that identity to approximate adjoint lifts is precisely

~~~text
max_(s in S)||beta_n(s)vec(v_n)-vec(v_n)|| ->0
implies
||(beta_n(gamma)-I)vec(v_n)|| ->0                        (FDP14)
~~~

for every op-norm-one unitary sequence `v_n`.  This is the bounded-vector
finite-dimensional-radical continuity problem.  A normalized trace or
normalized-rank estimate for the whole low spectral projection cannot by
itself prove `(FDP14)`, because the distinguished vector may lie in a
vanishing-density exceptional sector.

For the Kun--Thom pair, `fd-invisibility-of-compression` supplies
`(FDP1)` for every genuine finite-dimensional representation, and
`el-r-polynomial-robust-spectral-gap` supplies the robust gap.  Therefore
`(FDP14)` is the exact remaining step on this route.  It is not proved here.
