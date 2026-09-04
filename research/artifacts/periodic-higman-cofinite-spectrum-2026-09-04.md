# The periodic-Higman spectrum contains every sufficiently large integer

Date: 2026-09-04.

## Statement and scope

Use the commutator convention `[a,b]=a^{-1}b^{-1}ab` throughout. Define

\[
\Sigma=\{\operatorname{ord}(\alpha)>1:\ H=\langle h_0,h_1,h_2,h_3\rangle
\text{ is finite},\ \alpha\in\operatorname{Aut}(H),\
\alpha(h_j)=[h_j,h_{j-1}]\ (j\in\mathbb Z/4)\}.
\]

**Theorem.** Put

\[
B_*=4000\cdot40^{12}=67108864000000000000000.
\]

Every integer `n>B_*` belongs to `Sigma`. Moreover, the presented group

\[
G_n=\langle x_0,x_1,x_2,x_3,t\mid
t x_jt^{-1}=[x_j,x_{j-1}],\ t^n=1\rangle
\]

has a finite matrix quotient in which all four `x_j` are nonidentity and
the image of `t` has exact order `n`.

This is a restriction on the proposed missing-period construction of a
non-residually-finite hyperbolic group. It is **not** a solution of Gromov's
question, and it does **not** prove that any `G_n` is residually finite.
The fixed-threshold claim `periodic-higman-large-prime-period-gap` remains
open: a missing prime between its threshold `m_0` and `B_*` has not been
excluded by this argument. The bound is deliberately conservative.

## 1. An exact algebraic matrix certificate

Let `i^2=-1` and set

\[
P(L)=L^5-(4+3i)L^4+2L^3+2iL^2-(3+4i)L+i.
\]

In the ring `R=Z[i,1/2,L]/(P)`, define

\[
\begin{aligned}
X&=\frac{-3iL^4-(9-11i)L^3-(3+3i)L^2+(3+3i)L-7+8i}{8},\\
C&=\frac{-(1+i)L^4+6iL^3-(2-4i)L^2+2iL-5+5i}{16},\\
W&=\frac{L^4-(5+3i)L^3+(5+3i)L^2-(1-5i)L-5i}{8},\\
K&=iL^4+(3-4i)L^3+2iL^2-2L+4-3i.
\end{aligned}
\]

Put

\[
A=\begin{pmatrix}X&1\\C&W\end{pmatrix},\quad
D=\begin{pmatrix}i&0\\0&1\end{pmatrix},\quad
T=\begin{pmatrix}L&0\\0&1\end{pmatrix},\quad
A_-=D^{-1}AD=\begin{pmatrix}X&-i\\iC&W\end{pmatrix}.
\]

Monic polynomial division by `P` gives the identities

\[
XW-C=1,\qquad LK=1,\qquad
A^{-1}A_-^{-1}AA_-=
\begin{pmatrix}X&L\\CK&W\end{pmatrix}=TAT^{-1}.       \tag{1}
\]

These are identities over `Z[i,1/2]`, not assertions that depend on a
chosen approximate root. For explicit verification, the inverse matrices
in (1) are

\[
A^{-1}=\begin{pmatrix}W&-1\\-C&X\end{pmatrix},\qquad
A_-^{-1}=\begin{pmatrix}W&i\\-iC&X\end{pmatrix}.
\]

Substitute the four displayed polynomials, multiply, and reduce by the
monic degree-five relation. The determinant residual, the inverse residual,
and all four commutator residuals are zero. The accompanying standard-library
script performs exactly these finite rational operations and also checks
all four cyclic equations:

```sh
python experiments/periodic_higman_algebraic_certificate.py
```

There is no need to assume that `P` is irreducible: monicity makes `R` a
free module over `Z[i,1/2]`, so the same zero remainders computed over
`Q(i)` hold over `Z[i,1/2]`.

Set `A_j=D^j A D^{-j}` for `j` modulo four. Because `D^4=1` and `D`
commutes with `T`, conjugating (1) by `D^j` proves

\[
T A_jT^{-1}=[A_j,A_{j-1}]\quad(j\in\mathbb Z/4).       \tag{2}
\]

Every `A_j` has determinant one and upper-right entry `i^j`.

## 2. Choose a unit that is not a root of unity

At least one complex root `lambda` of `P` has modulus greater than one.
Indeed, suppose every root had modulus at most one. Their sum, by Vieta's
formula, is `4+3i`, of modulus five. Equality in the triangle inequality
then forces all five roots to be the same number `(4+3i)/5`, of modulus
one. Their second elementary symmetric function would consequently have
modulus ten. Its actual value, the coefficient of `L^3` in `P`, is two.
This is a contradiction.

Fix such a root and put `F=Q(i,lambda)`. Then `[F:Q]<=10`. Since `P` is
monic with Gaussian integer coefficients, `lambda` is an algebraic integer.
The identity `lambda K(lambda)=1` shows that its inverse is also integral.
Thus `lambda` is an algebraic unit; its modulus excludes roots of unity.
All entries of the matrices above specialize into `O_F[1/2]`.

At every prime ideal of `O_F` above two, `i` reduces to one, and

\[
P(L)\bmod 2=L^5+L^4+L+1=(L+1)^5.
\]

Consequently `lambda` reduces to one at each such prime.

## 3. An imported primitive-divisor theorem

Voutier's Theorem 2(i), page 253 of *Primitive divisors of Lucas and Lehmer
sequences, II*, J. Théor. Nombres Bordeaux **8** (1996), 251–274, gives the
following general algebraic-integer statement. For coprime algebraic
integers `a,b`, with `b/a` not a root of unity and of degree `d` over `Q`,
every

\[
n>\max\{2(2^d-1),\ 4000(d\log(3d))^{12}\}
\]

admits a prime ideal dividing `a^n-b^n` and dividing none of
`a^r-b^r`, `1<=r<n`. [Primary source, Theorem 2(i)](https://www.numdam.org/item/JTNB_1996__8_2_251_0.pdf).

Apply this with `a=lambda`, `b=1`; the two principal ideals are coprime
because `lambda` is a unit. Here `d<=10`. Since `log(30)<4`, our integer
`B_*` exceeds the stated bound. This uses the general number-field theorem,
not the much sharper bounds specific to Lucas or Lehmer pairs.

## 4. Finite certificates of every large exact period

Fix `n>B_*` and choose a primitive prime ideal `p` as above. The reduction
`bar(lambda)` in the finite residue field `k=O_F/p` has exact multiplicative
order `n`: a smaller positive order would contradict primitivity.

In particular, `p` is not above two, since `lambda` reduces to one at those
primes and `n>1`. All the matrices in (2) therefore reduce to matrices over
`k`. Let

\[
h_j=\overline{A_j}\in\operatorname{SL}_2(k),\qquad
s=\overline T=\operatorname{diag}(\bar\lambda,1),\qquad
H=\langle h_0,h_1,h_2,h_3\rangle.
\]

Equation (2) gives `sHs^{-1}<=H`. The left-hand group has the same finite
cardinality as `H`, so equality holds. Hence conjugation by `s` restricts
to an automorphism `alpha` of `H` satisfying the required recurrence.

The equality `s^n=1` gives `alpha^n=1`. Conversely, if `alpha^r=1`, compare
the upper-right entries of `s^r h_0 s^{-r}` and `h_0`. They are
`bar(lambda)^r` and `1`; thus `n` divides `r`. It follows that
`ord(alpha)=n`, proving `n in Sigma`.

Each `h_j` is nonidentity because its upper-right entry is `bar(i)^j`,
which is nonzero. The assignments `x_j -> h_j` and `t -> s` satisfy all
defining relations of `G_n`; their image in `GL_2(k)` is the asserted
finite quotient. Notice that neither generation of all `SL_2(k)` nor a
classification of finite simple groups is needed. As a consistency check,
the recurrence implies `alpha(H)<=H'`, so surjectivity of `alpha` makes
`H` perfect. QED.

## 5. Consequences for the research graph

The implication in `periodic-higman-period-spectrum-criterion` remains
valid. Its hypothesis cannot hold for `m>B_*`, since `m` itself then
belongs to `Sigma` and divides `m`. The stronger conclusion above also
shows directly that these finite quotients detect the proposed base mark
`x_0`.

A witness to `periodic-higman-large-prime-period-gap`, if one exists, must
therefore lie in the finite interval `[m_0,B_*]`. No search of that entire
interval is claimed. If a filling threshold is enlarged beyond `B_*`, the
missing-prime assertion for that enlarged threshold is false; this does
not refute the assertion for a smaller, already fixed threshold.

Detecting four individual generators is insufficient to prove residual
finiteness, which requires detecting every nonidentity element. No new
route establishing `non-residually-finite-hyperbolic-group` is supplied.
The contribution here is the explicit algebraic certificate and its
cofinite-spectrum consequence. The primitive-divisor theorem is existing
literature; no independent priority claim is made for the application.
