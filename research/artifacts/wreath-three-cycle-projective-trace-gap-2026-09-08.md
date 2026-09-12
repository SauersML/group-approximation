# A trace gap for an exact three-cycle product

2026-09-08. A finite-dimensional representation argument. This lemma
concerns an exact three-cycle product group; it does not transfer an
arbitrary marked matrix subgroup to that group and does not determine
hyperlinearity of the Leavitt unit group.

Let \(M,N\) be finite groups, let \(\alpha\in\operatorname{Aut}(M)\)
satisfy \(\alpha^3=1\), and put

\[
G=(M\times N^3)\rtimes\langle c\rangle,\qquad c^3=1,
\]

where \(c\) acts by \(\alpha\) on \(M\) and cyclically permutes
the three \(N\) factors. Fix an involution
\(j=(1,j_1,j_2,j_3)\in\{1\}\times N^3\), allowing the identity,
and put \(r=(jc)^2\). The case \(M=\{1\}\) is the usual
three-factor wreath product. For a unitary matrix define

\[
d_{\rm sc}(U)=\min_{|z|=1}\|U-zI\|_2,
\qquad d_{\rm sc}(U)^2=2-2|\tau(U)|,
\]

using normalized trace and normalized Hilbert--Schmidt norm.

## 1. Ordinary unitary representations

Every finite-dimensional ordinary unitary representation \(\rho\)
of \(G\) satisfies

\[
\boxed{d_{\rm sc}(\rho(c))^2
       \leq\frac53 d_{\rm sc}(\rho(r))^2.}       \tag{1}
\]

This covers every complex representation of \(G\) after choosing an
invariant inner product. No perfectness assumption is needed.

We first describe the relevant irreducible blocks. Restriction to
\(M\times N^3\) decomposes into tensor products
\(\sigma\otimes\pi_1\otimes\pi_2\otimes\pi_3\), where
\(\sigma\) is irreducible for \(M\) and each \(\pi_i\) is
irreducible for \(N\). This follows by successively decomposing
the four commuting finite-dimensional operator algebras. The element
\(c\) permutes these tensor-product types, using \(\alpha\) on
the first factor. In an irreducible \(G\)-block there is one orbit
of types.

If that orbit has size three, \(c\) and \(r\), whose respective
cosets are \(c\) and \(c^2\), permute the three isotypic spaces
without fixing any. Both traces are therefore zero.

If the orbit has size one, the tensor type is
\(\sigma\otimes\pi\otimes\pi\otimes\pi\), with
\(\sigma\) equivalent to its \(\alpha\)-twist. Write
\(d=\dim\pi\) and \(h=\dim\sigma\). Choose a unitary
\(V\) implementing \(\alpha\) on \(\sigma\). Schur's lemma
makes \(V^3\) scalar, so rescale \(V\) to arrange \(V^3=I\).
The cycle acts, after identifying the equivalent tensor factors, as
\(V\otimes S\otimes T\), where

\[
S(\xi_1\otimes\xi_2\otimes\xi_3)
   =\xi_3\otimes\xi_1\otimes\xi_2.
\]

The multiplicity operator \(T\) is unitary and \(T^3=I\).
Its eigenspaces are invariant under the whole group, so
irreducibility forces multiplicity one and \(T=\zeta\), with
\(\zeta^3=1\).

The elementary tensor-cycle trace identities are

\[
\begin{aligned}
\operatorname{Tr}((A\otimes B\otimes C)S)
   &=\operatorname{Tr}(ACB),\\
\operatorname{Tr}((A\otimes B\otimes C)S^2)
   &=\operatorname{Tr}(ABC).
\end{aligned}                                                     \tag{2}
\]

These follow by summing diagonal coefficients in a tensor basis.
Set \(A=\pi(j_1), B=\pi(j_2), C=\pi(j_3)\). Since
\(S(A\otimes B\otimes C)S^{-1}=C\otimes A\otimes B\),
(2) gives

\[
\tau(\rho(c))=\frac{\zeta\,\tau_h(V)}{d^2},\qquad
\tau(\rho(r))=
 \frac{\zeta^2\,\tau_h(V^2)}{d^3}
      \operatorname{Tr}((ACB)^2).                              \tag{3}
\]

Thus when \(d\geq2\), both normalized trace magnitudes are at
most \(d^{-2}\leq1/4\). When \(d=1\), each of \(A,B,C\)
is a sign because \(j_i^2=1\). Since \(j\) is the identity in
the \(M\) coordinate, it acts as a scalar sign on this entire
block, even when \(h>1\). Thus \(\rho(r)=\rho(c)^2\).
Using \(\rho(c)^3=I\) gives

\[
\tau(\rho(r))=\overline{\tau(\rho(c))}.                       \tag{4}
\]

Now decompose an arbitrary representation orthogonally into these
irreducible blocks. Let \(w\) be the fraction of total dimension
occupied by the size-three-orbit blocks and the invariant blocks
with \(d\geq2\). The remaining blocks have (4). Consequently,
for some complex numbers \(z,a,b\),

\[
\tau(\rho(c))=z+a,\qquad
\tau(\rho(r))=\bar z+b,\qquad
|z|\leq1-w,\quad |a|,|b|\leq w/4.
\]

It follows that

\[
|\tau(\rho(r))|\leq1-3w/4,\qquad
|\tau(\rho(c))|\geq|\tau(\rho(r))|-w/2.
\]

Writing \(x=1-|\tau(\rho(r))|\), the first inequality gives
\(w\leq4x/3\), and the second gives
\(1-|\tau(\rho(c))|\leq x+w/2\leq5x/3\).
This proves (1), including arbitrary direct sums and multiplicities.

## 2. Projective representations need no multiplier analysis

Let \(\rho:G\to U(D)\) be any projective unitary representation.
Its scalar multiplier cancels in

\[
\widehat\rho(g)=\rho(g)\otimes\overline{\rho(g)},
\]

which is an ordinary unitary representation of the same exact group.
Moreover \(\tau(\widehat\rho(g))=|\tau(\rho(g))|^2\).
Applying (1) to \(\widehat\rho\) yields

\[
\boxed{1-|\tau(\rho(c))|^2
       \leq\frac53\bigl(1-|\tau(\rho(r))|^2\bigr).}          \tag{5}
\]

In particular, if \(\tau(\rho(c))=0\), then

\[
\boxed{d_{\rm sc}(\rho(r))
       \geq\sqrt{\,2-2\sqrt{2/5}\,}.}                        \tag{6}
\]

One may replace \(\rho(r)\) by the literally evaluated word
\((\rho(j)\rho(c))^2\): projectivity changes it only by a scalar
of modulus one, which affects neither trace magnitude nor scalar
distance. No cohomological assumption on \(M\) or \(N\) is involved.

The hypotheses here require an exact ordinary or projective
representation of \((M\times N^3)\rtimes C_3\), with the indicated
action and with \(j\) trivial in the \(M\) factor. The lemma alone does not
show that an arbitrary marked subgroup, a semisimple coefficient
model, or a group with a radical quotient has such a representation
or decomposition. Those transfer steps remain separate obligations.

The [semisimple coefficient application](leavitt-semisimple-path-algebra-marked-projective-gap-2026-09-08.md)
now proves such a transfer after localizing the balanced part of the
native involution. It retains the correlated semidirect product and
does not quotient a nonzero radical in a complex representation.
