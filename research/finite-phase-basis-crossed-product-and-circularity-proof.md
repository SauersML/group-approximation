---
rg: 2
id: finite-phase-basis-crossed-product-and-circularity-proof
kind: route
title: Compute the twisted semidirect basis and separate exact dilation from finite charts
target: finite-phase-pauli-basis-dilation-is-a-twisted-group-factor-compiler
requires:
  - group-basis-permutation-koopman-proof
  - unrestricted-algebraic-envelope-equals-nonhyperlinearity
  - lamp-charts-recover-set-action
  - sofic-action-gives-marked-pauli-central-product-microstates
---

# Finite-phase basis dilations are already group compilers

## 1. The crossed product has a projective group basis

Let `(v_k)_(k in K)` be the canonical projective orthonormal basis of
`L_omega(K)`:

~~~text
v_k v_l=omega(k,l)v_(kl),
tau(v_k)=0 for k!=1.                                    (1)
~~~

Let `u_g` be the canonical actor unitaries in the crossed product and
assume (PBD1).  For `a=(k,g) in H=K semidirect_theta G` put

~~~text
W_a=v_k u_g.                                             (2)
~~~

The family `(W_a)_(a in H)` is an orthonormal basis of the crossed-product
`L^2` space.  Indeed the usual Fourier decomposition makes different actor
grades orthogonal, and inside one grade the `v_k` are orthonormal.

Multiplication is

~~~text
W_(k,g) W_(l,h)
 =v_k beta_g(v_l) u_(gh)
 =c(g,l) omega(k,theta_g(l))
    v_(k theta_g(l)) u_(gh).                             (3)
~~~

Thus, with

~~~text
Omega((k,g),(l,h))
 =c(g,l) omega(k,theta_g(l)),                            (4)
~~~

equation (3) is the twisted group law on `H`.  Associativity of the crossed
product says exactly that `Omega` is a scalar two-cocycle.  Completeness and
the trace in (1) give the trace-preserving isomorphism (PBD2).

## 2. Finite phases give an honest central-extension group

Assume `Omega` takes values in `mu_m`.  Define

~~~text
Gamma_hat=mu_m times_Omega H
~~~

with multiplication

~~~text
(z,a)(w,b)=(zw Omega(a,b),ab).                           (5)
~~~

The first factor is a finite central subgroup.  For its defining character
`chi(z)=z`, the central spectral projection

~~~text
p_chi=(1/m) sum_(z in mu_m) chi(z)-bar lambda(z)          (6)
~~~

has canonical trace `1/m`.  Choosing the conjugate character if required by
the cocycle convention, the corner satisfies

~~~text
p_chi L(Gamma_hat) p_chi
 isomorphic to L_Omega(H).                               (7)
~~~

This is the standard finite central-character corner calculation: in the
corner, `lambda(z)` acts as the scalar `chi(z)`, so (5) becomes precisely
the projective multiplication (3).

Suppose now that `M crossed_product_alpha G` embeds trace preservingly in
the algebra in (7).  If `L(Gamma_hat)` were Connes embeddable, then its
positive corner and every tracial von Neumann subalgebra of that corner
would be Connes embeddable.  Hence non-embeddability of the source crossed
product forces `L(Gamma_hat)` non-embeddable.  Equivalently,
`Gamma_hat` is nonhyperlinear.

Finite phase is load-bearing for this literal corner compiler.  A
countably infinite scalar range gives a central extension by an infinite
amenable group, but a single character is generally a measure-zero fiber of
its diffuse central algebra and need not be a positive corner.

## 3. The unrestricted existence statement is circular

One direction of (PBD4) is Section 2.  Conversely, suppose a countable
nonhyperlinear group `Lambda` exists.  Let

~~~text
K=S_fin(N).
~~~

This is countable, amenable and ICC, so `L(K)` is the hyperfinite
`II_1` factor `R`.  Let `Lambda` act trivially on `R` and on its canonical
group basis.  Then

~~~text
R crossed_product Lambda
 =L(K) tensor L(Lambda)
 =L(K times Lambda).                                    (8)
~~~

It is not Connes embeddable because it contains `L(Lambda)`.  The action in
(8) already is its own phase-free group-basis dilation.  This proves the
reverse direction of (PBD4).

Thus an unrestricted theorem asking only for the existence of some non-CE
source with some basis dilation has exactly the logical strength of the
target.  A useful theorem must pin the source action independently and
construct its dilation with finite phases.

## 4. A strict equivariant dilation has a Koopman obstruction

Suppose `Phi:M->L_omega(K)` is strictly equivariant.  Trace preservation
extends `Phi` to an isometric intertwiner

~~~text
L^2(M) -> l^2(K).                                        (9)
~~~

Under (PBD1), the target Koopman representation is finite-phase monomial.
For one acting generator, decompose `K` into permutation orbits.

- On a finite orbit, a power of the monomial operator is multiplication by
  a phase in `mu_m`.  Every eigenvalue is therefore a root of unity.
- On an infinite orbit, gauge the weights away along the orbit.  The
  resulting operator is a bilateral shift and has no nonzero
  `l^2`-eigenvector.

Hence every point eigenvalue in the target of (9) is torsion.

There is an explicit obstruction inside `R`.  Realize `R` as the weak
closure of the irrational rotation algebra and choose unitaries

~~~text
UV=lambda VU,             lambda=exp(2 pi i theta),
theta irrational.                                          (10)
~~~

Let the generator of `Z` act by `alpha=Ad U`.  Then

~~~text
alpha(V)=lambda V,                                        (11)
~~~

so `V in L^2(R)` is an eigenvector with non-torsion eigenvalue.  Equations
(9)--(11) rule out every strict finite-phase basis dilation.

This is not a sofic obstruction.  The actor `Z` is amenable, its action has
an injective/Connes-embeddable crossed product, and amenable pmp actions have
sofic finite models.  Strict equivariant algebraization asks for more than
finite approximation.

The example is intentionally fenced: `Ad U` is inner and therefore cocycle
conjugate to the trivial action.  If arbitrary cocycle perturbation is
allowed, (11) is not an invariant and cannot be used as the obstruction.
For outer amenable actions on `R`, the relevant standardization theory is
Ocneanu's classification of amenable-group actions on injective factors.
That theory does not supply a universal nonamenable-actor algebraization,
which is the case needed for a non-CE crossed product.

## 5. Exact basis preservation is not soficity

The converse confusion is equally important.  Given any countable
`G`-set `X`, including a nonsofic one, the tensor action on

~~~text
R_X=tensor_(x in X) M_2
~~~

permutes the countable finite-support Pauli-word basis exactly.  In
particular the pinned Kun--Thom action already has an exact invariant Pauli
basis.  This says nothing about whether `R_X crossed_product G` is Connes
embeddable and supplies no finite action chart.

At the chart level the relation is sharp.  For the marked Pauli lamp:

1. a sofic set action gives finite marked Pauli charts and microstates; and
2. a common finite Pauli chart, restricted to one named site generator,
   recovers a sofic chart of the underlying set action.

These are `sofic-action-gives-marked-pauli-central-product-microstates` and
`lamp-charts-recover-set-action`.  Therefore charted Pauli approximation is
equivalent to the relevant set-action soficity, whereas exact invariant
basis structure is not.

## 6. The fixed-source residue

For a pinned action with non-CE crossed product, a finite-phase dilation
would solve the group problem by Sections 1--2.  There are only three ways
it could evade the strict Koopman obstruction:

1. change the action by a genuine cocycle conjugacy;
2. embed it non-equivariantly at the base level but equivariantly after
   crossing with the actor; or
3. realize it as a positive invariant corner of a larger basis action.

Each alternative must still provide the trace-preserving crossed-product
inclusion in clause 3 of the definition.  Producing that inclusion is the
source-specific algebraic-envelope problem, not a formal property of
hyperfinite `R`.

## Literature boundary

- A. Ocneanu, *Actions of discrete amenable groups on von Neumann
  algebras*, Lecture Notes in Mathematics 1138, Springer, 1985, develops the
  cocycle-conjugacy classification for amenable-group actions on injective
  factors.  Its amenability hypothesis is essential to the available
  standardization route.
- The project repository nodes
  `group-basis-actions-have-permutation-koopman-spectrum` and
  `haar-algebraic-actions-have-permutation-koopman-spectrum` record the
  exact permutation-spectrum obstruction for strict equivariant
  algebraization.
- The finite central-character step in (6)--(7) is the same standard twisted
  group-algebra corner used by `thom-central-corner-criterion`.

No cited theorem supplies the nonamenable fixed-source dilation required
above.
