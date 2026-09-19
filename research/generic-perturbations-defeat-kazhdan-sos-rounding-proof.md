---
rg: 2
id: generic-perturbations-defeat-kazhdan-sos-rounding-proof
kind: route
title: Lift the SOS identity, then exhibit the disappearing-kernel obstruction
target: ozawa-sos-does-not-round-approximate-actor-to-exact-commutant
requires:
  - kazhdan-stabilizer-collapses-shared-pauli-sign
  - high-type-mass-is-discontinuous-at-exact-code-tuples
  - generic-perturbations-destroy-exact-commutant-gap
---

# Generic perturbations defeat exact-commutant rounding

All Hilbert--Schmidt norms and traces below are normalized.

## 1. An explicit two-dimensional disappearing kernel

Choose two named generators `a,b in S`.  It is enough to treat
`0<eta<1`: for a larger requested tolerance, reuse the tuple constructed
with `eta` replaced by `1/2`.  Let

~~~text
X = [[0,1],[1,0]],             Z = [[1,0],[0,-1]]
~~~

be Pauli matrices.  For `0<eta<pi` assign

~~~text
U_a=exp(i eta X),      U_b=exp(i eta Z),      U_s=I
~~~

for every other presentation generator `s`, and put `T=X`.  This assignment
extends exactly to a representation of the free group on `S`.

For either active generator,

~~~text
norm_2(U_s-I)=2|sin(eta/2)|<=eta.                         (1)
~~~

A telescoping product estimate therefore gives, for every word `w`,

~~~text
norm_2(U_w-I)<=|w| eta.                                  (2)
~~~

In particular every defining relator has defect at most `L_R eta`.

The matrix `T` commutes with `U_a`.  Since `XZ=-ZX`,

~~~text
norm_2(U_b T-T U_b)=2|sin eta|<=2 eta.                   (3)
~~~

On the other hand, `U_a` and `U_b` each have two distinct eigenvalues.
Their joint commutant is the joint commutant of `X` and `Z`, hence is
`C I`.  Since `tr_2(T)=0` and `norm_2(T)=1`,

~~~text
dist_2(T,C I)=1.                                         (4)
~~~

For a scalar unitary `lambda I`,

~~~text
norm_2(T-lambda I)^2
 =norm_2(T)^2+norm_2(I)^2-2 Re(lambda-bar tr_2(T))
 =2.                                                     (5)
~~~

Equations (1)--(5) prove (OSC1)--(OSC2).  Notice that the conclusion is
independent of every algebraic property of `Gamma`.  It therefore applies
in particular to a property-(T) presentation.

The small eigenvalues are also visible directly.  For the free-group
conjugation Laplacian, the energy of `T` is `O(eta^2)`, but the invariant
space is only the scalars and `T` has unit distance from it.  Thus the
positive spectral gap above the exact kernel tends to zero.

## 2. The obstruction preserves an arbitrary finite moment profile

We use the following elementary density fact.

**Lemma.**  If `N>=2` and a tuple has at least two unitary entries, then it
can be perturbed arbitrarily little in operator norm to a tuple whose joint
commutant is scalar.

**Proof.**  Perturb the first selected unitary to one with simple spectrum.
In its eigenbasis, perturb the second selected unitary so that every matrix
entry is nonzero.  Such unitaries are dense: the zero set of any fixed
matrix entry has empty interior in `U(N)`, and there are only finitely many
entries.

A projection commuting with the first unitary is diagonal in this basis and
is the indicator of a subset of eigenvectors.  If the subset is nonempty
and proper, commutation with the second unitary would force a cross-block
matrix entry to vanish.  Hence the only common commuting projections are
`0` and `I`.  The finite-dimensional joint commutant is therefore `C I`.
This proves the lemma.

Now start from any tuple `V=(V_s) in U(d)^S` and set

~~~text
W_s=V_s tensor I_2,        T=I_d tensor X.                (6)
~~~

The tuple `W` commutes with `T`.  By the lemma choose an irreducible tuple
`U` with

~~~text
max_s norm_op(U_s-W_s)<eta.                               (7)
~~~

Then

~~~text
norm_2(U_sT-TU_s)
 <=2 norm_2(U_s-W_s)
 <=2 eta.                                                 (8)
~~~

Telescoping along a word, including inverse letters, gives

~~~text
norm_op(U_w-W_w)<=|w| eta.                                (9)
~~~

Normalized Hilbert--Schmidt norm is bounded by operator norm, and
`|tr(Y)|<=norm_2(Y)`.  Therefore (9) implies both estimates in (OSC4).
In particular, if `V` already realizes a finite collection of actor
relators and canonical mixed traces to tolerance `delta`, then `U` realizes
the same collection to tolerance `delta+L eta`, where `L` is the maximum
word length in that collection.  Nevertheless its exact commutant has
collapsed from a copy of `M_2` to the scalars, while `T` remains almost
central and stays at distance one from that commutant.

This is stronger than the near-trivial example for the proposed use: it
survives amplification of any given hyperlinear coordinate and changes
every fixed observable continuously.

For the Kun--Thom elementary actor, `generic-perturbations-destroy-exact-commutant-gap`
sharpens this construction further: it starts from left-regular residual
finite quotients, keeps a trace-zero right-regular unitary almost central,
and therefore retains canonical trace-faithfulness while the literal
commutant collapses to scalars.

## 3. What the lifted Ozawa certificate actually gives

Let `F=F(S)` and use a finite symmetric generating alphabet.  Write

~~~text
Delta_F=|S| - sum_(s in S) s.
~~~

Suppose a fixed property-(T) sum-of-squares certificate in `C Gamma` is

~~~text
Delta^2-kappa Delta=sum_i xi_i^* xi_i.                    (10)
~~~

Choose finite-support lifts `tilde(xi_i) in C F`.  The difference between
the two sides of (10) belongs to the two-sided relator ideal.  Because it
has finite support, choose one finite decomposition

~~~text
Delta_F^2-kappa Delta_F-sum_i tilde(xi_i)^*tilde(xi_i)
 =sum_j a_j(r_j-1)b_j,                                   (11)
~~~

where `a_j,b_j in C F` and each `r_j` is a defining relator (an inverse can
be absorbed into a coefficient).

An arbitrary unitary assignment `U=(U_s)` gives a genuine free-group
representation on `L^2(M_D)`,

~~~text
pi_U(w)(Y)=U_w Y U_w^*.
~~~

If `norm_2(U_r-I)<=epsilon` and `Y` is bounded, then

~~~text
norm_2((pi_U(r)-I)Y)
 <=2 epsilon norm_op(Y).                                 (12)
~~~

For a group-algebra element `c`, conjugation by each group element is an
operator-norm isometry, so

~~~text
norm_op(pi_U(c)Y)<=norm_1(c) norm_op(Y),
norm_2(pi_U(c)Y)<=norm_1(c) norm_2(Y).                    (13)
~~~

Apply (12)--(13) to one summand in (11).  For every bounded `T`,

~~~text
|<pi_U(a_j(r_j-1)b_j)T,T>|
 <=2 epsilon norm_1(a_j) norm_1(b_j) norm_op(T)^2.        (14)
~~~

Set

~~~text
C_R=2 sum_j norm_1(a_j) norm_1(b_j).                      (15)
~~~

After evaluating (11), positivity of every square gives

~~~text
norm_2(Delta_U T)^2-kappa <Delta_U T,T>
 >=-C_R epsilon norm_op(T)^2.                             (16)
~~~

This is exactly (OSC5).  It is a legitimate, dimension-free consequence of
the finite SOS certificate and uses boundedness of `T` to turn HS relator
defect into an adjoint-action estimate.

## 4. Why (16) is not the needed Poincare inequality

For an exact actor representation, the relator term in (16) vanishes for
every vector.  The polynomial spectral inequality excludes spectrum in
`(0,kappa)` and gives the projection onto the exact invariant space used in
`kazhdan-stabilizer-collapses-shared-pauli-sign`.

For an approximate actor, (16) has an additive error depending on
`norm_op(T)`.  The two-dimensional tuple in Section 1 has positive
Laplacian eigenvalues tending to zero, so its kernel drops discontinuously
even though all relator errors and the commutator energy tend to zero.
Spectral cutoff does not fix this: a cutoff vector need not retain a useful
operator-norm bound, while heat-kernel regularization is operator-norm
contractive but can converge only on the inverse scale of those arbitrarily
small eigenvalues.  There is no presentation-controlled time scale.

Most decisively, Section 2 shows that the same disappearing kernel can be
inserted within `eta` of every amplified actor coordinate while preserving
all fixed trace observables.  Therefore no additional finite list of
ordinary moments repairs the exact-commutant projection.

The SOS calculation may still be useful with either of two genuinely
stronger inputs:

1. an independently stable nearby genuine actor representation, whose
   commutant has a real spectral gap; or
2. a formulation in a stable near-commutant or low-spectrum bimodule which
   never asks for projection to the discontinuous exact kernel.

Neither input is supplied by property (T), finite presentation, or
pointwise hyperlinear convergence alone.  Thus the exact-actor shared-Pauli
collapse remains valid, but this proposed bridge from approximate actors is
closed.
