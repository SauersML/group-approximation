# Schur curvature is necessary for the central FALSE route

**Closure update for the explicit symmetric double.** The necessary growing
curvature condition is not sufficient there: its full finite residual
\(R\) satisfies \(R=[D,R]\), forcing a fixed relator coefficient vector and
a uniform bound on every canonical character ratio. See
`FALSE_FINITE_RESIDUAL_COMMUTATOR_NO_GO.md`.

## Setup

Let

\[
P=\langle s_1,\ldots ,s_d\mid r_1,\ldots ,r_\ell\rangle=F/N
\]

and let \(w\) represent a nonidentity element of
\(\operatorname{Rad}_{\rm sof}(P)\).  For a finite quotient
\(P\twoheadrightarrow Q\), put \(L=\ker(F\to Q)\) and

\[
C_Q=L/[F,L].
\]

The relator classes \(a_j=[r_j]\) and the marked class \(b=[w]\) lie in
\(C_Q\).

## Hopf curvature versus generator gauge

The five-term sequence for

\[
1\longrightarrow L\longrightarrow F\longrightarrow Q\longrightarrow1
\]

and the vanishing of \(H_2(F;\mathbb Z)\) give

\[
0\longrightarrow H_2(Q;\mathbb Z)
\longrightarrow C_Q
\xrightarrow{\epsilon_Q}
B_Q
\longrightarrow0,
\]

where

\[
B_Q:=\ker\bigl(F_{\rm ab}\cong\mathbb Z^d
\longrightarrow Q_{\rm ab}\bigr).
\]

The injection is the Hopf-formula identification

\[
H_2(Q;\mathbb Z)
\cong
(L\cap[F,F])/[F,L].
\]

A character of \(C_Q\) that is trivial on \(H_2(Q;\mathbb Z)\) factors
through \(B_Q\).  Such a character changes only the scalar phases assigned
to the chosen lifts of the presentation generators.  It is therefore the
precise algebraic form of a global gauge.  A character nontrivial on
\(H_2(Q;\mathbb Z)\) carries genuine projective curvature, or equivalently a
Schur-multiplier class.

## Uniform sterility of the pure-gauge sector

Let

\[
e:F\longrightarrow F_{\rm ab}\cong\mathbb Z^d
\]

be exponent sum.  Because \(w\) lies in the finite residual of \(P\), its
image in the finitely generated abelian group \(P_{\rm ab}\) is zero.
Therefore there is a fixed vector

\[
v^0=(v_1^0,\ldots ,v_\ell^0)\in\mathbb Z^\ell
\]

such that

\[
e(w)=\sum_{j=1}^{\ell}v_j^0e(r_j).
\]

This vector depends only on the original finite presentation and \(w\), not
on \(Q\).

### Theorem 1 (pure-gauge bound)

For every finite quotient \(Q\) and every character
\(\chi:C_Q\to\mathbb T\) that is trivial on \(H_2(Q;\mathbb Z)\),

\[
|\chi(b)-1|
\leq
\|v^0\|_2
\left(\sum_{j=1}^{\ell}|\chi(a_j)-1|^2\right)^{1/2}.
\]

#### Proof

The character factors as \(\chi=\psi\circ\epsilon_Q\) for a character
\(\psi:B_Q\to\mathbb T\).  Since \(\mathbb T\) is divisible, \(\psi\)
extends to a character \(\widetilde\psi:\mathbb Z^d\to\mathbb T\).  Hence

\[
\chi(b)=\widetilde\psi(e(w))
=\prod_j\widetilde\psi(e(r_j))^{v_j^0}
=\prod_j\chi(a_j)^{v_j^0}.
\]

Using \(|z^n-1|\leq |n|\,|z-1|\), telescoping, and Cauchy--Schwarz gives
the claimed estimate. \(\square\)

### Corollary 2 (curvature necessity)

No sequence of pure-gauge characters can make the marked/relator ratio
diverge.  Consequently, if the canonical central-quotient criterion proves
FALSE, every witnessing tail must involve characters that are nontrivial on

\[
H_2(Q_n;\mathbb Z).
\]

In particular, ordinary scalar rephasing of generator lifts can never finish
the proof.

### Theorem 3 (unbounded Schur exponent is necessary)

Let \(\mathcal Q\) be a family of finite quotients of \(P\).  If there is an
integer \(M\) such that

\[
M\,H_2(Q;\mathbb Z)=0
\qquad(Q\in\mathcal Q),
\]

then the canonical central marked/relator ratios are uniformly bounded over
\(Q\in\mathcal Q\).  Consequently, divergence of the central FALSE
criterion requires

\[
\boxed{
\exp H_2(Q_n;\mathbb Z)\longrightarrow\infty
}
\]

along some sequence of finite quotients.

#### Proof

For each \(Q\), the group

\[
B_Q\leq\mathbb Z^d
\]

is free abelian, so the exact sequence

\[
0\to H_2(Q;\mathbb Z)\to C_Q\to B_Q\to0
\]

splits as a sequence of abelian groups.  Relative to any splitting, a
character \(\chi\in\widehat{C_Q}\) has two parts:

- a curvature character \(\alpha\in\widehat{H_2(Q;\mathbb Z)}\);
- a gauge character \(\psi\in\widehat{B_Q}\), which extends to a point of
  \(\widehat{\mathbb Z^d}\cong\mathbb T^d\).

If \(MH_2(Q;\mathbb Z)=0\), then the curvature contributions to the values
of \(\chi\) on the finite list

\[
a_1,\ldots ,a_\ell,b
\]

belong to the finite set \(\mu_M^{\ell+1}\).  The gauge contributions are
the fixed monomials on \(\mathbb T^d\) determined by the exponent-sum vectors

\[
e(r_1),\ldots ,e(r_\ell),e(w).
\]

Thus every quotient-level marked/relator ratio is the restriction of one of
finitely many functions

\[
z\longmapsto
\frac{|\zeta_w z^{e(w)}-1|}
{\left(\sum_j|\zeta_j z^{e(r_j)}-1|^2\right)^{1/2}},
\qquad
(\zeta_1,\ldots ,\zeta_\ell,\zeta_w)\in\mu_M^{\ell+1}.
\]

Only patterns realized by an actual quotient and curvature character need be
considered.  For such a pattern, a zero of every denominator term is also a
zero of the numerator: otherwise the associated character of \(C_Q\) would
make every presentation relator trivial while retaining \(w\), producing an
exact finite-dimensional unitary representation of \(P\) that separates
\(w\).  The finitely generated linear image of that representation is
residually finite, contradicting radicality.

Near a common zero, write the monomial phases in local angular coordinates.
Their first-order parts are the fixed integer linear forms
\(e(r_j)\), while the marked first-order form \(e(w)\) lies in their real
span because \(w=0\) in \(P_{\rm ab}\).  The quotient is therefore locally
bounded.  Away from the common zero set it is continuous on a compact set.
Each of the finitely many realized phase patterns consequently has finite
supremum, and taking their maximum gives a bound independent of \(Q\).
\(\square\)

The theorem explains why a fixed torsion multiplier cannot finish the
construction.  A successful sequence must carry curvature of genuinely
growing order, exactly as suggested by the integral \(p^k\)-Bockstein tower.

## Interpretation

The theorem is the scalar central analogue of the principal-bundle tangent
sterility result.  The two possible mechanisms are now separated exactly:

1. **Gauge:** a character factoring through \(B_Q\).  This sector has the
   fixed bound \(\|v^0\|_2\).
2. **Curvature:** a character detecting the Schur multiplier
   \(H_2(Q;\mathbb Z)\).  Only this sector can produce unbounded amplification.

The existing Baumslag--Solitar construction supplies growing integral
Bockstein classes and an exact clock representation.  To connect it to the
central criterion, one must now prove that the paired class maps to a global
Schur-multiplier class of the relevant finite fold quotient and compute its
pairing with:

- the two vertex copies of every fixed relator;
- the amalgam relators;
- the marked fold word.

The desired pairing is small on the first two families and macroscopic on the
last.  This is a cohomological extension problem, not a global gauge problem.

## Dual cohomological form

Because \(\mathbb T\) is divisible, Pontryagin duality turns the exact
sequence above into

\[
0\longrightarrow\widehat{B_Q}
\longrightarrow\widehat{C_Q}
\longrightarrow\widehat{H_2(Q;\mathbb Z)}
\longrightarrow0.
\]

For finite \(Q\), the universal coefficient theorem identifies

\[
\widehat{H_2(Q;\mathbb Z)}
\cong H^2(Q;\mathbb T).
\]

Thus the genuinely new data needed by FALSE is a sequence of projective
multiplier classes on finite quotients.  The local cyclotomic Bockstein is a
candidate source of precisely such classes; what remains is its global
extension and the quantitative evaluation stated above.
