# Explicit mixed LHS cocycle and the true relator-coordinate problem

## The cocycle formula

Let \(A\) be a finite group, let \(N\) be a finite abelian left
\(\mathbb Z[A]\)-module, and form

\[
G=N\rtimes A,
\qquad
(n,a)(m,b)=(n+a\cdot m,ab).
\]

Let

\[
\widehat N=\operatorname{Hom}(N,\mathbb T)
\]

with the contragredient \(A\)-action.  Write characters additively when
convenient.  Let

\[
\lambda\in Z^1(A,\widehat N),
\qquad
\lambda(ab)=\lambda(a)+a\cdot\lambda(b).
\]

Define

\[
\alpha_\lambda((n,a),(m,b))
:=\lambda(a)(a\cdot m)\in\mathbb T.
\]

### Theorem 1 (explicit mixed multiplier)

The function \(\alpha_\lambda\) is a normalized two-cocycle on \(G\).  Its
cohomology class is the mixed LHS class corresponding to

\[
[\lambda]\in
E_2^{1,1}=H^1(A,H^1(N,\mathbb T)).
\]

It vanishes on \(A\times A\) and on \(N\times N\).

#### Proof

Let

\[
g=(n,a),\quad h=(m,b),\quad k=(\ell,c).
\]

The left-hand side of the cocycle identity is

\[
\lambda(a)(a m)+\lambda(ab)(ab\ell).
\]

The right-hand side is

\[
\lambda(b)(b\ell)+\lambda(a)(a(m+b\ell)).
\]

Using

\[
\lambda(ab)=\lambda(a)+a\cdot\lambda(b)
\]

and

\[
(a\cdot\lambda(b))(ab\ell)=\lambda(b)(b\ell)
\]

makes the two expressions equal.  Normalization and the two vanishing
statements are immediate.  The standard edge description of the split LHS
spectral sequence identifies this cocycle with \([\lambda]\). \(\square\)

The formula also proves directly that the mixed class survives: it supplies
an actual global cocycle, not merely an associated-graded class.

## Fixed presentation phases

Choose generators

\[
s_1,\ldots ,s_d
\]

for \(A\), and choose finitely many elements

\[
v_1,\ldots ,v_t\in N
\]

whose \(A\)-orbits generate \(N\).  A standard presentation of \(N\rtimes A\)
has:

1. the fixed relators of \(A\);
2. additive/commutativity relators for the module generators;
3. covariance relators expressing
   \[
   s_iv_js_i^{-1}=s_i\cdot v_j.
   \]

### Proposition 2 (only covariance carries curvature)

For the multiplier \(\alpha_\lambda\), relators of types 1 and 2 have
trivial scalar phase.  The phase of a covariance relator is, up to inversion
according to the presentation convention,

\[
\boxed{
\lambda(s_i)(s_i\cdot v_j).
}
\]

#### Proof

Type 1 uses only pairs from \(A\times A\), and type 2 only pairs from
\(N\times N\), so Theorem 1 gives phase one.  Moving \(s_i\) past \(v_j\)
uses the product

\[
(0,s_i)(v_j,1),
\]

whose multiplier is exactly
\(\lambda(s_i)(s_i\cdot v_j)\). \(\square\)

Thus the bounded-coordinate condition in the Bockstein amplifier is the
finite list of scalar estimates

\[
\lambda_k(s_i)(s_i\cdot v_j)
=e^{2\pi i m_{ij,k}/p^k},
\qquad
\sum_{i,j}m_{ij,k}^2=o(p^{2k}).
\]

There are no hidden matrix relations.

## Explicit Shapiro coordinates

Let \(B\leq A\), let \(J\) be a finite \(B\)-module, and take

\[
N=\operatorname{Ind}_B^AJ.
\]

Duality identifies \(\widehat N\) with the coinduced module

\[
\operatorname{Coind}_B^A\widehat J.
\]

Choose a right transversal

\[
\tau:B\backslash A\longrightarrow A.
\]

For \(a\in A\) and \(x\in B\backslash A\), define the Schreier transition

\[
\beta_\tau(x,a)
:=\tau(x)a\tau(xa)^{-1}\in B.
\]

Let

\[
z\in Z^1(B,\widehat J)
\]

be the local clock cocycle.  The Shapiro cocycle

\[
\lambda_\tau\in Z^1(A,\operatorname{Coind}_B^A\widehat J)
\]

is given, in coset coordinates, by evaluating \(z\) on
\(\beta_\tau(x,a)\), with the standard conjugation action on the coefficient
coordinate.

Consequently the covariance phase associated to a fixed generator \(s_i\)
and a module vector supported at the coset \(x\) is a local clock evaluation of

\[
\beta_\tau(x,s_i).
\]

For a general fixed module generator \(v_j\), expressed in the coset
coordinates of the induced module, the scalar phase

\[
\lambda_\tau(s_i)(s_i\cdot v_j)
\]

is the corresponding finite product of local clock evaluations, with the
coordinate multiplicities of \(v_j\).  This is the exact scalar quantity
that enters Proposition 2.

### Proposition 3 (orbit-sum Schreier energy)

Suppose, in addition, that the matrix model is the orthogonal direct sum of
the coset-supported clock sectors, each with equal multiplicity.  Then its
total normalized covariance energy is the average, over cosets and the fixed
generating set, of the clock energy of the Schreier transitions:

\[
\mathcal E_k(\tau)^2
=
\frac1{|B_k\backslash A_k|}
\sum_{x\in B_k\backslash A_k}
\sum_{i=1}^{d}
\left|z_k(\beta_\tau(x,s_i))-1\right|^2,
\]

up to the fixed multiplicity coming from the chosen module generators.

#### Proof

On the sector indexed by \(x\), the relevant covariance defect is scalar and
equal to the local clock evaluation of \(\beta_\tau(x,s_i)\).  The square of
the normalized Hilbert--Schmidt norm of a block-diagonal operator is the
dimension-weighted average of the squared block norms.  Equal multiplicities
give the displayed formula. \(\square\)

Without this orbit-sum hypothesis, there is no averaging statement: a single
central projective sector sees the one scalar pairing from Proposition 2.

Changing the transversal replaces \(\beta_\tau\) by a cohomologous Schreier
cocycle.  Thus minimizing the fixed-relator defect is exactly a finite gauge
problem on the principal \(B_k\)-bundle \(A_k\to B_k\backslash A_k\).

For the orbit-sum realization, this identifies the earlier principal-bundle
obstruction precisely.  The remaining problem is not to construct arbitrary
matrices for the external generators; it is to find a Schreier gauge whose
local clock labels have normalized energy \(o(1)\), while the Bockstein fold
label retains its fixed nonzero phase.  For the scalar central route, the
corresponding task is the bounded-coordinate pairing of Proposition 2.

## Relation to the long-chain no-go theorem

The naive long-chain splice chooses a particular transversal along successive
compressor depths.  Its second compressor accumulates a shear around each
depth cycle.  In the present language, that shear is the holonomy of the
Schreier cocycle \(\beta_\tau\), and the positive density of bad covariance
relations is a lower bound for \(\mathcal E_k(\tau)\) for that gauge.

The no-go theorem therefore rules out that transversal; it does not rule out
the mixed cohomology class itself.  A successful construction must either:

- find a different gauge with sublinear clock-coordinate energy;
- enlarge the induced module so the monodromy is distributed over a
  vanishing fraction of coordinates; or
- prove, via the paired discriminant formula, that two gauges have small
  covariance energy but distinct fold holonomy.

All three alternatives are finite scalar/cochain problems.
