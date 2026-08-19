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

## The exact finite clock cocycle

For the metacyclic group

\[
B_k=
\langle \bar h,\bar c\mid
\bar h^{p^{k+1}}=1,
\bar c^{p^k}=1,
\bar c\bar h\bar c^{-1}=\bar h^{p+1}
\rangle,
\]

put

\[
n=p^{k+1},
\qquad M=p^k,
\qquad q=p+1,
\]

and

\[
J_k=\left\{
(x_0,\ldots ,x_{M-1})\in(\mathbb Z/n)^M:
\sum_jx_j=0
\right\}.
\]

Orient the regular cycle so that the contragredient action below has the
displayed eigenvalue.  Define

\[
\varphi_k(x)
:=
\exp\left(
\frac{2\pi i}{n}
\sum_{j=0}^{M-1}q^{-j}x_j
\right).
\]

The inverses \(q^{-j}\) are taken modulo \(n\); they are periodic because
\(q^M\equiv1\pmod n\).

### Proposition 4 (explicit clock cocycle)

The character \(\varphi_k\in\widehat{J_k}\) has exact order \(p^k\) and
satisfies

\[
\bar c\cdot\varphi_k=q\varphi_k.
\]

Consequently

\[
z_k(\bar h)=\varphi_k,
\qquad
z_k(\bar c)=0
\]

extends uniquely to a cocycle

\[
z_k\in Z^1(B_k,\widehat{J_k})
\]

dual to the \(\bar h\)-coordinate generator of
\(H_1(B_k,J_k)\).

#### Proof

Since \(q^{-j}\equiv1\pmod p\) and \(\sum_jx_j=0\), the numerator in the
definition of \(\varphi_k\) is divisible by \(p\).  Hence the order divides
\(p^k\).  On the augmentation vector

\[
v=e_1-e_0
\]

the numerator is

\[
q^{-1}-1=-pq^{-1},
\]

which has exact \(p\)-adic valuation one.  Thus the order is exactly \(p^k\).

With the chosen cycle orientation, shifting the coordinates in the
contragredient action multiplies the weight vector \((q^{-j})_j\) by \(q\),
so \(\bar c\cdot\varphi_k=q\varphi_k\).

The cocycle relation applied to
\(\bar c\bar h\bar c^{-1}=\bar h^q\) is precisely this eigencharacter
identity.  The order relations hold because \(p^k\varphi_k=0\), hence also
\(p^{k+1}\varphi_k=0\), and because \(z_k(\bar c)=0\). \(\square\)

### Corollary 5 (unit-normalized local low-error/high-witness scale)

For \(v=e_1-e_0\),

\[
\varphi_k(v)
=
\exp\left(-\frac{2\pi iq^{-1}}{p^k}\right),
\]

where `q^(-1)` is a residue modulo `p^k`.  Its standard integer
representative need not stay bounded, so this raw formula by itself does
**not** imply an `O(p^(-k))` chord.

Instead put

\[
u_k=-q^{-1}\pmod {p^k},
\qquad
b_k=u_k^{-1}=-q\pmod {p^k},
\qquad
\psi_k=\varphi_k^{\,b_k}.
\]

The power `b_k` is a unit, so `psi_k` still has exact order `p^k` and still
satisfies the same eigencharacter identity

\[
\bar c\cdot\psi_k=q\psi_k.
\]

It is normalized by the exact equality

\[
\psi_k(v)=\exp(2\pi i/p^k),
\]

and hence

\[
|\psi_k(v)-1|=O(p^{-k}).
\]

The nonzero ordinary Bockstein of the order-\(p^k\) clock generator is its
\(p^{k-1}\)-multiple, and the normalized character takes on it the value

\[
\exp(2\pi i/p),
\]

whose distance from \(1\) is bounded below independently of \(k\).

Thus the local covariance coordinate is microscopically small while the fold
Bockstein is macroscopically visible.  Under Shapiro induction, the only new
coordinates are the \(\bar h\)-exponents of the Schreier transitions
\(\beta_\tau(x,s_i)\).  Controlling those exponents, in the scalar or averaged
sense appropriate to the chosen model, is the exact remaining ambient
extension problem.

More explicitly, write a transition in metacyclic normal form as

\[
\beta_\tau(x,s)
=\bar h^{a_\tau(x,s)}\bar c^{t_\tau(x,s)}.
\]

Because \(\bar h\) acts trivially on \(\widehat{J_k}\) and
\(z_k(\bar c)=0\), the unit-rescaled cocycle
`z'_k=b_k z_k` satisfies

\[
z'_k(\beta_\tau(x,s))
=a_\tau(x,s)\psi_k.
\]

On \(v=e_1-e_0\), the corresponding phase is

\[
\exp\left(
\frac{2\pi i a_\tau(x,s)}{p^k}
\right).
\]

Therefore the orbit-sum covariance energy is, up to a fixed multiplicity,

\[
\boxed{
\frac1{|B_k\backslash A_k|}
\sum_{x\in B_k\backslash A_k}
\sum_{s\in S_A}
4\sin^2\left(
\frac{\pi a_\tau(x,s)}{p^k}
\right).
}
\]

The final averaged extension question is precisely whether a transversal can
make this expression tend to zero while the Bockstein fold phase remains the
fixed nontrivial \(p\)-th root.  This is the scalar Schreier version of the
proposed frozen-clock computation.

## Exact twisted gauge law and cycle discriminants

Changing the transversal by the normal metacyclic subgroup is completely
explicit.  Let

\[
\tau'(x)=\bar h^{g_x}\tau(x),
\qquad
g_x\in\mathbb Z/p^{k+1}.
\]

If an oriented Schreier edge \(e=(x,s)\), with endpoint \(y=xs\), has label

\[
\beta_\tau(e)=\bar h^{a_e}\bar c^{t_e},
\]

then the semidirect multiplication law gives

\[
\boxed{
a'_e=a_e+g_x-q^{t_e}g_y,
\qquad
t'_e=t_e.
}
\]

Thus the normal labels form a twisted one-cochain, and normal changes of
transversal add the twisted coboundary

\[
(d_tg)(e)=g_x-q^{t_e}g_y.
\]

For a closed path \(C=e_1\cdots e_m\), define

\[
T_C=t_{e_1}+\cdots+t_{e_m}
\]

and the normal holonomy

\[
A_C
=a_{e_1}+q^{t_{e_1}}a_{e_2}
+q^{t_{e_1}+t_{e_2}}a_{e_3}
+\cdots.
\]

At the base vertex, a gauge change gives

\[
\boxed{
A'_C=A_C+(1-q^{T_C})g.
}
\]

Hence the cycle obstruction is the discriminant class

\[
[A_C]
\in
(\mathbb Z/p^{k+1})/(1-q^{T_C}).
\]

If \(T_C=0\pmod{p^k}\), the holonomy is fully gauge invariant.  More
generally,

\[
v_p(1-q^{T_C})=1+v_p(T_C)
\]

for nonzero \(T_C\), so the exact depth of the residual obstruction is known.

The energy minimization is therefore the finite twisted circle-repair problem

\[
\inf_g
\frac1{|E|}\sum_{e\in E}
4\sin^2\left(
\frac{\pi (a_e+(d_tg)(e))}{p^k}
\right).
\]

This is not merely analogous to the paired discriminant formula: after
writing the twisted incidence matrix of \(d_t\), it is exactly an instance of
that formula.  The cycle classes \([A_C]\) are its finite discriminant data.
The remaining proof can therefore be phrased as a uniform asymptotic estimate
for this explicit family of twisted incidence lattices.
