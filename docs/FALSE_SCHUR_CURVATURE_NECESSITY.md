# Schur curvature is necessary for the central FALSE route

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

