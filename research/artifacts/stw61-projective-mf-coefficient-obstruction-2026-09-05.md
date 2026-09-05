# LXI: the maximal-commutator obstruction for MF coefficients

Date: 2026-09-05. Complete proof, internally reviewed; no external
or formal verification is claimed.
This extends the preceding finite-representation theorem to MF
coefficients. It does not settle LXI or the unrestricted Toeplitz
coefficient case.

## 1. The theorem and a slightly stronger hypothesis

Let D be a unital C*-algebra, let p be a projection, and suppose
there is a unital homomorphism

```text
theta:D -> (product_j M_(n_j)) / (direct_sum_j M_(n_j))
```

such that theta(p) and theta(1-p) are both nonzero. Products here
are bounded C*-products and direct sums are the ideals of sequences
whose norms tend to zero. In the full unital free product
C=C(S^1)*_C D, write z for the circle unitary. Then

```text
||[z,W p W*]|| = 1   for every W in U(C).
```

In particular, the conclusion holds for every separable unital MF
algebra D and every projection 0<p<1. No finite-dimensional
representation of D is required. The homomorphism theta in the
stronger statement need not be faithful; for MF coefficients it
may be taken to be a unital embedding.

The matrix-quotient definition of MF is recalled in Hadwin--Li--
Shen--Wang, *Reduced Free Products of Unital AH Algebras and MF
Algebras*, Definition 1.2
([primary paper](https://jot.theta.ro/jot/archive/2012-068-001/2012-068-001-015.pdf)).
The proof below supplies the relevant unitalization, projection
selection, and lifting arguments explicitly.

## 2. Unital matrix-quotient embeddings and actual projections

Write Q_n=(product M_(n_j))/(direct_sum M_(n_j)). Every projection
q in Q_n lifts to a sequence of actual matrix projections. Indeed,
choose a bounded self-adjoint representative h_j of q. The relation
q^2=q means ||h_j^2-h_j|| tends to zero. For all sufficiently large
j, its spectrum avoids 1/2 and lies increasingly close to {0,1}.
Then

```text
q_j = 1_(1/2,infinity)(h_j)
```

is a projection with ||q_j-h_j|| tending to zero. The finitely many
remaining coordinates can be chosen arbitrarily.

If an MF embedding theta_0 of a unital D is initially nonunital,
apply this construction to q=theta_0(1_D). Its range lies in q Q_n q.
For a projection lift q_j, compression of representatives identifies

```text
q Q_n q = (product_j q_j M_(n_j) q_j)
          / (direct_sum_j q_j M_(n_j) q_j).
```

Coordinates with q_j=0 can be deleted; infinitely many remain
because q is nonzero. Identify each remaining matrix corner with
M_(rank q_j). The resulting embedding is unital, with the same
faithful range as theta_0. This justifies using a unital theta for
the MF corollary without a separate convention on MF embeddings.

Now fix the unital theta from Section 1. Lift theta(p) to actual
projections P_j in M_(n_j). Since theta(p) and theta(1-p) are
nonzero projections, they have norm one. The quotient norm formula

```text
||[(a_j)]|| = limsup_j ||a_j||
```

therefore shows that P_j is nonzero for arbitrarily large j, and
P_j is different from 1_(n_j) for arbitrarily large j. These two
properties need not initially hold at the same coordinates.

## 3. Block sums which preserve faithfulness

Choose m(j)>=j as follows:

- If P_j=0, choose m(j) with P_(m(j)) nonzero.
- If P_j=1_(n_j), choose m(j) with P_(m(j)) different from its unit.
- If 0<P_j<1_(n_j), take m(j)=j.

The choices exist by Section 2. Put

```text
N_j=n_j+n_(m(j)),
P'_j=P_j direct_sum P_(m(j)).
```

Then 0<rank(P'_j)<N_j for every j. Define a unital homomorphism
on bounded products by

```text
Delta((a_j))=(a_j direct_sum a_(m(j))).
```

Because m(j)>=j, a norm-null sequence is sent to a norm-null
sequence, so Delta induces a unital map Q_n -> Q_N. It is
isometric: for every bounded sequence (a_j),

```text
limsup_j max(||a_j||,||a_(m(j))||) = limsup_j ||a_j||.
```

The inequality greater than or equal follows by retaining the
original j coordinate, and the reverse inequality follows from
m(j)>=j. Thus an initially faithful theta remains faithful after
Delta. A pair of arbitrary detecting subsequences alone would not
justify that claim; retaining every j avoids the issue.

Replace theta by Delta theta and relabel P'_j as P_j. We have
obtained actual representatives with

```text
0<rank P_j<N_j   for every j.
```

No coordinatewise homomorphism D -> M_(N_j) has been asserted or
used. All algebraic relations of D are represented in the quotient.

## 4. Constant matrices and a projective-space quotient

Let X_j=CP^(N_j-1), and put

```text
R = (product_j C(X_j,M_(N_j)))
    / (direct_sum_j C(X_j,M_(N_j))).
```

The coordinatewise inclusion of a matrix as a constant function
induces a unital isometric homomorphism iota:Q_N -> R. This follows
directly from the same limsup norm formula: constant functions have
exactly the norms of their matrix values.

Let e_j be the tautological rank-one projection over X_j and define

```text
V_j=i(2e_j-1_(N_j)),   V=[(V_j)] in R.
```

These are genuine continuous unitaries. The universal property of
the full unital free product gives a unital homomorphism

```text
Psi:C(S^1)*D -> R,
Psi(z)=V,   Psi(d)=iota(theta(d)).
```

In particular, Psi(p) is represented by the constant projections
P_j. There is no need to lift theta on all of D, or to lift Psi
on the whole free product.

## 5. Every quotient unitary has genuine coordinate unitary lifts

Fix W in U(C) and write u=Psi(W). Choose any bounded representative
w_j in C(X_j,M_(N_j)) of u. Since u*u=uu*=1 in R,

```text
||w_j*w_j-1|| -> 0,   ||w_jw_j*-1|| -> 0.
```

For all sufficiently large j both defects are less than one, so
w_j is invertible in C(X_j,M_(N_j)). Its polar correction

```text
U_j=w_j(w_j*w_j)^(-1/2)
```

is a continuous unitary. Functional calculus gives
||U_j-w_j|| tending to zero. On the finitely many remaining
coordinates choose U_j=1. Hence [(U_j)]=u in R.

This is a lift of the one unitary needed for the proof. There is
no claim of a simultaneous multiplicative lift of the coefficient
algebra. The argument uses norm-null defects, exactly the quotient
ideal specified in Section 1.

## 6. The finite projective obstruction survives in the quotient

For each j put

```text
Q_j(x)=U_j(x) P_j U_j(x)*.
```

Its range bundle is trivial of rank r_j=rank P_j, and its
complementary bundle is trivial of rank N_j-r_j. Both ranks lie
between one and N_j-1. The projective argument from Sections 3--4
of the
[finite-representation audit](stw61-projective-finite-representation-obstruction-2026-09-05.md)
therefore applies separately at every j. It gives

```text
||[V_j,Q_j]||_(C(X_j,M_(N_j))) = 1.
```

To recall its content, lambda_j=Tr(e_j Q_j) must attain both zero
and one. Otherwise the tautological line embeds into one of the
two trivial complementary bundles, contradicting the nonzero top
Chern class of the corresponding sum of dual tautological lines.
Connectedness of X_j gives lambda_j=1/2 somewhere, where

```text
||[V_j(x),Q_j(x)]||=2 sqrt(lambda_j(x)(1-lambda_j(x)))=1.
```

Now [(Q_j)]=Psi(WpW*) and V=[(V_j)], so

```text
||Psi([z,WpW*])|| = limsup_j ||[V_j,Q_j]|| = 1.
```

Contractivity of Psi gives ||[z,WpW*]||>=1. Conversely, for any
unitary u and projection q, writing [u,q] in the q decomposition
gives an off-diagonal block matrix whose two blocks have norm at
most one. Hence ||[u,q]||<=1. This proves the claimed equality.

## 7. Scope and the LXI application

The theorem includes every MF coefficient algebra with a nontrivial
projection, even when it has no nonzero finite-dimensional
representation. For example, an infinite-dimensional UHF algebra
is a genuine enlargement of the finite-representation class:
its finite tensor stages embed it into a matrix quotient, whereas
simplicity and infinite dimension rule out a nonzero homomorphism
to a finite-dimensional algebra. The former embedding can also
be constructed directly: assign each finite-stage element its
compatible images in every later matrix stage modulo finitely many
coordinates, then complete the resulting isometric homomorphism.

For the ambient application, let v be a full-spectrum unitary in
a unital A and let D be a unital subalgebra of T_2 containing p.
The full-free-product inclusion theorem identifies C*(v,D) with
C(S^1)*D inside A*T_2, as checked in Section 2 of the preceding
audit. Therefore, whenever D is MF and 0<p<1,

```text
||[v,WpW*]||=1   for every W in U(C*(v,D)).
```

For p=s_1s_1*, this rules out the strict BRR commutator criterion
for all these conjugates, despite proper infiniteness and fullness
of both complementary projections in the ambient algebra.

It does not supply the matrix-quotient representation for D=T_2.
Indeed, a unital matrix quotient as above is finite: if an element
is an isometry, its matrix representatives have initial defects
tending to zero; finite square matrices then have final defects
tending to zero as well, so the isometry is unitary in the
quotient. Thus the two Toeplitz isometries with orthogonal ranges
cannot map unitally into it. This also explains why the MF
hypothesis on a unital coefficient subalgebra is consistent with
proper infiniteness of the larger ambient algebra.

An unrestricted strict-commutator construction must therefore
escape the matrix-quotient coefficient condition detecting p and
1-p. No such construction, survival of the free-envelope witness,
or solution of STW LXI is asserted here.
