---
rg: 2
id: monomial-central-sign-dichotomy-proof
kind: route
title: Little groups and twisted quotient modules force the central-sign dichotomy
target: monomial-central-sign-has-types-or-affine-returns
requires: []
---

We prove both finite-group assertions in the target.

## The split monomial case

Let `H=D semidirect K`, with `D` finite abelian, and let `pi` be an
irreducible representation of `H`.  The restriction of `pi` to `D` is a
direct sum of character weight spaces.  The set of occurring weights is
`K`-invariant, and irreducibility makes it one `K`-orbit.  Choose an
occurring weight `chi`.  Its weight space is invariant under `K_chi`; the
action there is an irreducible representation `sigma` of `K_chi`, while
`D` acts by `chi`.  Conversely, the translates of this weight space give
the coset model

```text
Ind_(D semidirect K_chi)^H(chi tensor sigma).
```

Any invariant subspace of this induced representation is a sum of weight
spaces, and its intersection with the `chi`-space is `K_chi`-invariant.
Transitivity of the orbit and irreducibility of `sigma` therefore make the
induced representation irreducible.  This proves `(CSM2)`, and the same
coset model gives

```text
pi_(chi,sigma)|_D
 = direct_sum_(eta in K.chi) eta^(direct_sum dim sigma),
```

which is `(CSM3)`.

Because `J` is fixed by `K`, all characters in an orbit take the same value
on `J`.  The marked irreducibles are consequently parametrized by a choice
of `K`-orbit in `Omega_-` and a choice of `sigma in Irr(K_chi)`.  More than
one orbit gives more than one marked type.  A nontrivial finite stabilizer
`K_chi` also gives more than one type: besides its trivial representation it
has a nontrivial irreducible constituent of its regular representation.
Thus uniqueness forces one orbit and `K_chi=1`, so the action on `Omega_-`
is free and transitive and `(CSM4)` follows.

For completeness, restriction of the affine hyperplane `Omega_-` to any
subgroup `A<=D` has constant-size fibers.  If `J in A`, its image is the
hyperplane of characters of `A` taking `J` to `-1`; if `J notin A`, each
fiber of `D^ -> A^` is cut in half by the condition on `J`.  This proves the
uniform-multiplicity assertion following `(CSM4)`.

In the free-transitive weight model, `d in D` acts on the `eta`-line by
`eta(d)`, while `k in K` applies the same permutation `eta |-> k.eta` to all
weights.  If `dk` preserves every weight line, then `k` fixes an element of
the free `K`-set `Omega_-`, hence `k=1`.  The remaining phase is exactly the
affine character `eta |-> eta(d)`.  This proves `(CSM5)--(CSM6)`.

## The normal extraspecial case

Write `|E|=2^(1+2n)`.  The extraspecial identities

```text
Z(E)=[E,E]=<J>,       E/<J> ~= (C_2)^(2n)
```

show that `E` has `2^(2n)` linear characters, all trivial on `J`.  Every
noncentral conjugacy class has two elements: its commutator map has image
`<J>` and hence its centralizer has index two.  Thus `E` has
`2^(2n)+1` conjugacy classes and exactly one nonlinear irreducible.  The
sum-of-squares formula gives its degree `2^n`; call it `rho`.  Schur's lemma
and nonlinearity force `rho(J)=-I`.  Hence `rho` is the unique irreducible
of `E` carrying the marked central sign.

Let `E normal H`, let `L=H/E`, and choose a section `s:L->H`.  If `pi` is
any representation of `H` with `pi(J)=-I`, complete reducibility and the
preceding uniqueness give

```text
pi|_E = rho tensor I_M.
```

For each `l in L`, choose `U_l` implementing on `rho` the automorphism of
`E` induced by `s(l)`.  Then

```text
(U_l^* tensor I) pi(s(l))
```

commutes with `rho(E) tensor I`.  Schur's lemma therefore supplies an
operator `V_l` on the multiplicity space such that

```text
pi(e s(l))=rho(e)U_l tensor V_l.                       (1)
```

Put `c(l,m)=s(l)s(m)s(lm)^(-1) in E`.  The two spin operators implementing
the same automorphism differ by a scalar, so there is a scalar cocycle
`alpha` with

```text
U_l U_m=alpha(l,m) rho(c(l,m)) U_(lm).
```

Substitution in `(1)` gives

```text
V_l V_m=alpha(l,m)^(-1) V_(lm).                       (2)
```

Conversely, `(1)` defines an `H`-representation for every projective
`V` satisfying `(2)`.  Commutants in `(1)` show that `pi` is irreducible
exactly when `V` is irreducible.  Marked irreducibles of `H` are therefore
the irreducible modules of the twisted group algebra

```text
A=C^(alpha^(-1))[L],
```

whose basis elements satisfy
`u_l u_m=alpha(l,m)^(-1)u_(lm)`.

The algebra `A` is semisimple: the usual finite-group averaging argument
turns a linear projection onto an invariant subspace of a projective module
into an invariant projection.  Its left regular module is faithful and is a
direct sum of irreducibles.  If, for some `l!=1`, the basis element `u_l`
acted as one prescribed scalar `c` in every irreducible module, it would act
as `cI` in the faithful regular module.  This would give `u_l=c u_1` in
`A`, contradicting linear independence of the twisted basis.  The same
argument covers the case when `A` is simple: its unique irreducible module
is then faithful.  Consequently an outer coset cannot have `V_l=I` in every
marked representation, proving `(CSM8)`.

Finally let `A_0<=E` be a maximal abelian selector subgroup containing `J`.
For `e in E`, conjugation carries every `A_0`-weight `eta` to the weight
obtained by multiplying `eta` by the fixed commutator character

```text
a |-> [e,a] in <J>.
```

This translation is independent of `eta`.  If it is trivial, then `e`
centralizes `A_0`.  Maximal abelianness gives
`C_E(A_0)=A_0`, and on an `A_0`-weight the remaining action is the affine
phase `eta(e)`.  This proves `(CSM9)` and the extraspecial alternative.

If one concrete extension has a one-dimensional projective multiplicity
module, `(2)` makes `alpha` a coboundary.  After rescaling the implementers,
the quotient algebra is the ordinary group algebra `C[L]`.  For nontrivial
finite `L` it has the trivial representation and at least one further
irreducible constituent of the regular representation.  Thus a nonlinear
outer correction may be literal in one selected spin extension, but it
cannot be universal over the entire marked carrier.
