---
rg: 2
id: moving-tail-projective-space-countermodel-proof
kind: route
title: Build the projective-space Kazhdan fibers and normalize the moving half-corner
target: moving-tail-fixed-traces-keep-quantum-fibers
requires: []
---

## 1. The projective-space irreducible

Fix a prime `p>=5` and put

~~~text
G_p=PSL_3(F_p),          X_p=P^2(F_p),
N_p=|X_p|=p^2+p+1.                                      (MTP1)
~~~

The action of `G_p` on ordered pairs of distinct projective points is
transitive.  Indeed, lift the two source lines and the two target lines to
independent vectors, extend both pairs to bases, and rescale the image of the
third basis vector to make the resulting linear map have determinant one.
Thus the permutation character on `X_p` has rank two.  Over `C`,

~~~text
C^(X_p)=1 direct_sum pi_p,       dim(pi_p)=N_p-1=p^2+p,  (MTP2)
~~~

and rank two is exactly the statement that `pi_p` is irreducible.

We use the classical minimal-index theorem for `PSL_3(F_p)`: for
`p>=5`, every proper subgroup has index at least

~~~text
p^2+p+1,                                                (MTP3)
~~~

with equality for a projective point or line stabilizer.  This is the
rank-three case of the minimal faithful permutation-degree theorem for
finite classical simple groups (and also follows directly from the Dickson
maximal-subgroup list).

The representation `pi_p` is not monomial.  Since `G_p` is simple, the
permutation action on the coordinate lines of a hypothetical monomial basis
would have either trivial kernel or all of `G_p` as kernel.  The latter
would make the image diagonal and hence abelian, which is impossible.
The former would be a faithful permutation action of degree

~~~text
dim(pi_p)=p^2+p<p^2+p+1,                                (MTP4)
~~~

contradicting (MTP3).

Reduction modulo `p`, followed by the central quotient, inflates `pi_p`
to an irreducible nonmonomial representation of
`Gamma=SL_3(Z)`, still denoted `pi_p`.

## 2. Canonical character convergence with an explicit rate

Let `g!=1` be fixed in `SL_3(Z)`.  Its reduction is non-scalar for all
but finitely many primes.  Otherwise every off-diagonal entry and every
difference of two diagonal entries of `g` would be divisible by infinitely
many primes, so `g` would be a scalar integral matrix.  Determinant one
would then force `g=1`.

A non-scalar three-dimensional linear map over `F_p` has at most
`p+2` invariant projective lines.  Projective fixed points are eigenlines;
the maximum occurs for a two-dimensional eigenspace, which contributes
`p+1` lines, and one further eigenline.  If `F_p(g)` is the number of
fixed projective points, (MTP2) gives

~~~text
chi_(pi_p)(g)=F_p(g)-1.
~~~

Consequently, for all sufficiently large `p`,

~~~text
|tr_(p^2+p)(pi_p(g))|
 =|F_p(g)-1|/(p^2+p)
 <=(p+1)/(p^2+p)
 =1/p.                                                   (MTP5)
~~~

This is pointwise canonical-character convergence with no diagonal choice
of error rate hidden in the proof.

## 3. Property (T) makes the nonmonomiality uniform

Let `S` be a finite symmetric Kazhdan generating set for `Gamma`, and
let `kappa>0` satisfy (MTQ1).  Fix an exact monomial representation

~~~text
mu:Gamma->U(r_p)
~~~

and a unitary `Z`.  On the normalized Hilbert--Schmidt space
`M_(r_p)(C)`, consider

~~~text
T_g(A)=mu(g) A pi_p(g)^*.                                (MTP6)
~~~

Its invariant vectors are the intertwiners from `pi_p` to `mu`.
There are none.  If a nonzero intertwiner existed, irreducibility of
`pi_p` would embed it in `mu`; the two representations have the same
dimension, so they would be equivalent, contradicting nonmonomiality of
`pi_p`.

The vector `Z` has normalized Hilbert--Schmidt norm one.  Hence (MTQ1)
applied to (MTP6) gives

~~~text
max_(s in S)||mu(s)Z-Z pi_p(s)||_2 >=kappa.              (MTP7)
~~~

Multiplication by unitaries turns the left side into the one in (MTQ3).
The constant is the fixed Kazhdan constant of `SL_3(Z)`; it is independent
of `p`, the matrix dimension, and the Boolean window.

This use of property `(T)` is worth emphasizing.  It does not scalarize the
fiber.  It upgrades exact inequivalence of two same-dimensional
representations to a uniform metric separation.

## 4. Exact Boolean models and their pointwise trace

Let

~~~text
A=direct_sum_(j>=1) C_2,        m_p=p,
Y_p={-1,+1}^(m_p).                                      (MTP8)
~~~

On `ell^2(Y_p)`, let the first `m_p` lamp generators be the diagonal
coordinate signs and send every later lamp generator to the identity.  On

~~~text
V_p=ell^2(Y_p) tensor C^(r_p)
~~~

put

~~~text
theta_p(a,g)=L_p(a) tensor pi_p(g),      (a,g) in A times Gamma. (MTP9)
~~~

This is an exact representation.  The `m_p`-window character projections
are

~~~text
P_y=|y><y| tensor I_(r_p),       y in Y_p,               (MTP10)
~~~

so all have trace `2^(-m_p)` and rank `r_p`.  Actor covariance is exact
because the action on the lamps is trivial.

For a fixed nonidentity `(a,g)`, once `p` contains the support of `a`,
either `a!=1`, in which case the Boolean factor in (MTP9) has trace zero,
or `a=1` and `g!=1`, in which case (MTP5) tends to zero.  Therefore

~~~text
tr(theta_p(a,g))->0             for every (a,g)!=1.      (MTP11)
~~~

The same calculation covers all mixed lamp--actor words.

The ambient dimension is

~~~text
D_p=2^p p(p+1).                                         (MTP12)
~~~

Since `p=m_p`, equation (MTP12) is exactly (MTQ7).

## 5. Atom and positive-density corner normalization

On one atom `P_y V_p`, use the normalized corner norm

~~~text
||P_y x P_y||_(2,P_y)^2
 =(1/r_p) Tr_(P_y V_p)((P_y x P_y)^*(P_y x P_y)).        (MTP13)
~~~

The restricted actor representation is exactly `pi_p`, so (MTP7) is the
claimed per-atom lower bound.

Now let

~~~text
e_p=sum_(y in Y_p, y_(m_p)=+1) P_y.                     (MTP14)
~~~

It has rank `D_p/2` and trace `1/2`.  In the ambient matrix factor every
nonzero projection has full central support, and the normalized corner norm
is

~~~text
||e_p x e_p||_(2,e_p)^2
 =(2/D_p) Tr_(e_p V_p)((e_p x e_p)^*(e_p x e_p)).        (MTP15)
~~~

The selector uses the last, hence moving, lamp coordinate.  Given any fixed
lamp word, its support avoids that coordinate for all sufficiently large
`p`.  Conditional on `y_(m_p)=+1`, all fixed coordinates remain uniformly
independent.  Combining this observation with (MTP5) proves that the
compressed exact representations in `e_p M_(D_p)e_p` still satisfy the
canonical trace limit (MTP11).

Suppose `Z=direct_sum_y Z_y` is an atomwise gauge on `e_pV_p` and
`M:Gamma->U(e_pV_p)` is an exact atom-preserving monomial representation.
Write

~~~text
delta_(s,y)
 =||Z_y pi_p(s) Z_y^*-M_y(s)||_(2,P_y).                  (MTP16)
~~~

For every `y`, (MTP7) gives
`max_(s in S)delta_(s,y)>=kappa`.  Therefore

~~~text
sum_(s in S)||e_p(ZU_sZ^*-M_s)e_p||_(2,e_p)^2
 =average_(y_(m_p)=+1) sum_(s in S) delta_(s,y)^2
 >=kappa^2.                                              (MTP17)
~~~

Taking the largest summand proves (MTQ9).

## 6. The sharp padding firewall

The construction deliberately records the exact flexible escape.  Equation
(MTP2) says

~~~text
pi_p direct_sum 1 = C^(X_p),                             (MTP18)
~~~

and the right side is a permutation representation.  Add one trivial line
to every Boolean atom.  All actor matrices then become exactly permutation
matrices in the projective-point bases, with no perturbation and with the
Boolean blocks still exact.  The added dimension is `2^(m_p)`, whereas the
original dimension is `2^(m_p)r_p`; their ratio is `1/r_p`.

Thus no same-dimension conclusion can follow from the hypotheses recorded
above, even in a positive-density normalized corner and even with property
`(T)`.  Conversely, this particular obstruction is absorbed by
`o(D_p)` padding.  Any attack on the pinned Kun--Thom wreath must either
use the nontrivial coset action to prevent that absorption or prove a
padding-stable moving-holonomy theorem.  Neither assertion is made here.
