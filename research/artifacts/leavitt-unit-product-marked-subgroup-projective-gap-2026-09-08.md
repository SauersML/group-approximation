# A projective gap in the marked subgroup when ts is a unit

Date: 2026-09-08. Pure ring and matrix proof; independently audited.

For literal coefficients in a finite algebra, the ambient-extension
assumption can be removed whenever \(ts\) is a unit, of arbitrary
order. A diagonal change of coordinates exposes a finite coefficient
ring and a residual cyclic quotient of order at most three. An
induced three-block representation handles that quotient in the rank
calculation. No code or build was used.

The subsequent [unit-root theorem](leavitt-unit-root-marked-subgroup-projective-gap-2026-09-08.md)
keeps the same constant when K contains x_13(z) for any unit z,
even with singular ts. The proof below remains the simpler
unit-product case and includes an explicit example explaining its
cyclic quotient.

## 1. The theorem

Let \(A\) be a nonzero finite unital \(\mathbb F_2\)-algebra,
\(s,t,v\in A\), and suppose that \(Z=ts\) is invertible in \(A\).
Let \(c=(123)\) be the coordinate cycle and put

\[
K=\langle c,x_{12}(s),x_{12}(t),x_{12}(v)\rangle
       \leq\operatorname{EL}_3(A).
\]

Use the three native words \(r_*,R_v,R_0\) from
[the finite coefficient packet](leavitt-24k-finite-coefficient-kernel-packet-2026-09-08.md).
Their straight-line definitions are also given in Section 1 of
[the full finite-coefficient theorem](leavitt-all-finite-coefficient-projective-gap-2026-09-08.md).
For a homomorphism \(\rho:K\to\operatorname{PU}(N)\), write
\(L(g)=d_{\rm sc}(\rho(g),1)\), with normalized Hilbert--Schmidt
scalar distance.

**Theorem.** Every such representation satisfies

\[
\boxed{L(c)\leq49L(r_*)+24L(R_v)+24L(R_0).}       \tag{1}
\]

If a unitary representative of \(\rho(c)\) has trace zero, then

\[
\boxed{\max\{L(r_*),L(R_v),L(R_0)\}
                     \geq\frac{\sqrt2}{97}.}      \tag{2}
\]

The representation is defined only on \(K\). Neither an extension
to \(\operatorname{EL}_3(A)\) nor the equality \(ts=1\) is assumed.

## 2. Recover constant roots after a diagonal change of coordinates

Set

\[
\Delta=\operatorname{diag}(1,Z^{-1},Z),\quad
K'=\Delta K\Delta^{-1},\quad C=\Delta c\Delta^{-1},\quad w=Z^3.
\]

Transport \(\rho\) and \(L\) to \(K'\); this requires no value
of \(\rho\) on \(\Delta\). A prime denotes conjugation by
\(\Delta\). The native intermediate words satisfy

\[
d'=x_{13}(1),\quad e'=x_{21}(1),\quad
h'=x_{32}(w),\quad a'=x_{12}(w),\quad
j'=a'e'(a')^{-1}.                                \tag{3}
\]

All follow directly from \(d=x_{13}(Z), e=x_{21}(Z),
h=x_{32}(Z), a=x_{12}(Z^2)\). For each \(m\geq1\),

\[
[x_{32}(w^m),x_{21}(1)]=x_{31}(w^m),\qquad
[x_{31}(w^m),x_{12}(w)]=x_{32}(w^{m+1}).           \tag{4}
\]

Thus \(K'\) contains \(x_{32}(w^m)\) for every positive \(m\).
Since \(w\) is a unit of a finite ring, some such power is one.
Together with (3), the distinct-index commutator identities now
give all six constant roots. In particular, \(K'\) contains the
constant coordinate permutations and the constant cycle \(c_0=(123)\).
The membership construction (4) need not have bounded word length;
no metric bound is inferred from that construction.

Define

\[
B=\{b\in A:x_{ij}(b)\in K'\text{ for every }i\ne j\}.
\]

Same-root addition and distinct-index commutators make \(B\) a
finite unital subring. It contains \(w,w^{-1}\) and

\[
b_s=sZ,\qquad b_t=tZ,\qquad b_v=vZ,               \tag{5}
\]

because the three marked root generators become \(x_{12}(b_s)\),
\(x_{12}(b_t)\), \(x_{12}(b_v)\), and permutations move their
coefficients to every root position.

There is an automorphism \(\sigma=\operatorname{Ad}Z\) of \(B\).
Indeed,

\[
H=Cc_0^{-1}=\operatorname{diag}(Z^{-1},Z^{-1},Z^2)\in K',
\qquad H^{-1}x_{12}(b)H=x_{12}(\sigma(b)).         \tag{6}
\]

Permutation conjugation and the analogous identity using \(H\)
give \(\sigma(B)=B\). Furthermore

\[
\sigma(w)=w,\qquad \sigma^3=\operatorname{Ad}w.    \tag{7}
\]

In fact \(\operatorname{EL}_3(B)\) is normal in \(K'\), and
\(K'/\operatorname{EL}_3(B)\) is cyclic of order at most three.
To see normality, write
\(H=\operatorname{diag}(Z^{-1},Z^{-1},Z^{-1})
       \operatorname{diag}(1,1,w)\).
Its conjugation carries root coefficients into \(B\) by (6)--(7),
as does its inverse. The same holds for \(C=Hc_0\).
Since \(K'=\langle\operatorname{EL}_3(B),C\rangle\) and \(C^3=1\),
the quotient assertion follows. We do not require \(Z\in B\).

## 3. Extract the three defect coefficients using only K'

Put

\[
F=1+w,\qquad Q=(v^2+Z)Z^{-1},\qquad T=tvsZ^3.
\]

These lie in \(B\): the transformed root words are

\[
R_v'=x_{13}(Q),\qquad R_0'=x_{12}(T).             \tag{8}
\]

Writing \(\eta_*=L(r_*),\eta_v=L(R_v),\eta_0=L(R_0)\),
equation (6) shows that all roots with coefficients
\(\sigma^i(Q)\), respectively \(\sigma^i(T)\), have lengths
\(\eta_v\), respectively \(\eta_0\), for every integer \(i\).

The first row of \(r_*'\), obtained by conjugating the previously
computed row \((Z^{10},1+Z^3,Z^5(1+Z^3))\), is

\[
\bigl(Zw^3,\ ZF,\ ZwF\bigr).                    \tag{9}
\]

It is annihilated on the right by the column \((F,w^3,0)^T\).
The proof of
[Preusser, Proposition 9(i)](https://arxiv.org/pdf/1912.03536)
therefore extracts every \(x_{ij}(\alpha F\beta)\),
\(\alpha,\beta\in B\), as eight conjugates of \(r_*'\) and its
inverse **inside \(K'\)**. Here the internal scope of the proof
matters: it uses

\[
\tau=x_{13}(F)x_{23}(w^3),\qquad
x_{21}(\alpha),\qquad x_{31}(-\beta),
\]

and coordinate permutations. All belong to
\(\operatorname{EL}_3(B)\subseteq K'\). His two simultaneous
commutator reductions express the extracted root as four conjugates
of \([\tau,r_*']^{\pm1}\), hence eight \(K'\)-conjugates of
\((r_*')^{\pm1}\). In particular, this application does not assume
that \(r_*'\) has all its entries in \(B\).

Consequently,

\[
L(x_{ij}(\alpha F\beta))\leq8\eta_*.
\]

For the other coefficients, the distinct-index identity

\[
[[x_{ki}(\alpha),x_{ij}(z)],x_{ji}(\beta)]
                         =x_{ki}(\alpha z\beta)
\]

and permutation conjugation cost four copies of the root with
coefficient \(z\). Thus, for \(i=0,1,2\), arbitrary
\(\alpha,\beta\in B\), and any root position,

\[
\begin{aligned}
L(x_{kl}(\alpha F\beta))&\leq8\eta_*,\\
L(x_{kl}(\alpha\sigma^i(Q)\beta))&\leq4\eta_v,\\
L(x_{kl}(\alpha\sigma^i(T)\beta))&\leq4\eta_0.
\end{aligned}                                    \tag{10}
\]

## 4. An induced representation supplies a nine-term unit identity

Fix any simple component map
\(\pi:B\to M_d(\mathbb F_{2^a})\) of \(B/J(B)\). For \(b\in B\),
define matrices of size \(3d\) by

\[
\mathcal D(b)=\operatorname{diag}
       (\pi(b),\pi(\sigma(b)),\pi(\sigma^2(b))),\qquad
W=\begin{pmatrix}0&I&0\\0&0&I\\\pi(w)&0&0\end{pmatrix}.
\]

Equations (7) give the exact identities

\[
W\mathcal D(b)=\mathcal D(\sigma(b))W,
\qquad W^3=\mathcal D(w).                         \tag{11}
\]

Now set

\[
\mathsf S=\mathcal D(b_s)W^{-1},\quad
\mathsf T=\mathcal D(b_t)W^{-1},\quad
\mathsf V=\mathcal D(b_v)W^{-1}.
\]

All the following are coefficient identities in \(B\):

\[
\begin{aligned}
b_t\sigma^{-1}(b_s)&=w,\\
b_v\sigma^{-1}(b_v)+w&=Qw,\\
b_t\sigma^{-1}(b_v)\sigma^{-2}(b_s)&=T.
\end{aligned}
\]

They follow by substituting (5) and cancelling adjacent powers of
\(Z\), without commuting \(s,t,v\). Hence (11) implies

\[
\mathsf T\mathsf S=W,\qquad
\mathsf V^2+W=\mathcal D(Q)W,\qquad
\mathsf T\mathsf V\mathsf S W^2=\mathcal D(T)W^{-1}. \tag{12}
\]

For square coefficient matrices \(S,T,V\) of size \(m\), with
\(Z=TS\), the elementary rank argument gives

\[
\operatorname{rank}(TVSZ^2)+\operatorname{rank}(V^2+Z)
                 +3\operatorname{rank}(1+Z^3)\geq m. \tag{13}
\]

Indeed, \(S Z^2\) is injective on \(\ker(1+Z^3)\), and
\(\operatorname{nullity}T\leq\operatorname{rank}(1+Z^3)\);
combining these with the product-rank inequality proves (13).
This is the rank calculation of Section 3 of the linked full-group
theorem.

Apply (13) to (12). Since \(\sigma(F)=F\), the result is

\[
\sum_{i=0}^2\operatorname{rank}\pi(\sigma^i(Q))
+\sum_{i=0}^2\operatorname{rank}\pi(\sigma^i(T))
+9\operatorname{rank}\pi(F)\geq3d.
\]

In particular,

\[
\sum_{i=0}^2\operatorname{rank}\pi(\sigma^i(Q))
+\sum_{i=0}^2\operatorname{rank}\pi(\sigma^i(T))
+3\operatorname{rank}\pi(F)\geq d.               \tag{14}
\]

Partition a basis into nine pieces with sizes bounded by the nine
ranks in (14), counting \(F\) three times. Each corresponding
diagonal projection has the form \(\alpha z\beta\) for its chosen
coefficient \(z\). Assemble these choices in every simple component
of \(B/J(B)\), lift the coefficients to \(B\), and invert their
sum, which is congruent to one modulo \(J(B)\). Absorbing that
inverse into the left coefficients gives an exact identity

\[
1=\sum_{j=1}^9\alpha_j z_j\beta_j,
\quad
(z_j)=(F,F,F,Q,\sigma Q,\sigma^2Q,T,\sigma T,\sigma^2T).
                                                               \tag{15}
\]

All \(\alpha_j,\beta_j\) lie in the internally recovered ring \(B\).
Thus (10), same-root addition, and (15) imply

\[
L(x_{ij}(1))\leq\kappa
      :=24\eta_*+12\eta_v+12\eta_0               \tag{16}
\]

for every root position.

## 5. The first relator controls the remaining cycle

By (3), \(j'\) is conjugate inside \(K'\) to \(x_{21}(1)\),
so \(L(j')\leq\kappa\). The literal word identity

\[
r_*'=j'Cj'C=j'(Cj'C^{-1})C^2
\]

and \(C^3=1\) now give

\[
L(c)=L(C)=L(C^2)\leq\eta_*+2L(j')
       \leq49\eta_*+24\eta_v+24\eta_0.
\]

This proves (1). Trace zero gives \(L(c)=\sqrt2\), proving (2).
There is no uncontrolled word length from the finite order of \(w\)
in this estimate: that order establishes membership of auxiliary
conjugators, while (10)--(16) supply the uniform metric estimates.

## 6. Exact scope

The result covers arbitrary projective representations of the marked
subgroup for every finite coefficient algebra with literal invertible
\(ts\), including nilpotent radicals and unit orders divisible by
three. It is weaker numerically than the \(\sqrt2/18\) bound when
the coefficient equality \(ts=1\) holds, but has a strictly broader
hypothesis.

It does not assert \(K=\operatorname{EL}_3(A_0)\) for the original
coefficient-generated ring \(A_0\). The recovered ring \(B\) and the
possible cyclic quotient are part of the proof. Noninvertible \(ts\)
is outside this proof, although the later unit-root theorem covers
some such cases. No step
assigns coefficient matrices to arbitrary frozen \(24k\) unitary
tuples, so the unrestricted hyperlinearity problem remains open.

## 7. A genuine cyclic quotient inside the F64 coefficient algebra

Let \(A=\mathbb F_{64}\), with its subfields \(\mathbb F_8\) and
\(\mathbb F_4\). Choose a primitive \(\alpha\in\mathbb F_8^\times\)
and an element \(\omega\in\mathbb F_4^\times\) of order three. Set

\[
s=\alpha\omega^{-1},\qquad
t=\alpha^{-1}\omega^{-1},\qquad
v=\omega^{-1}.
\]

Then \(Z=ts=\omega\) and \(w=Z^3=1\). The original unital
coefficient-generated ring is all of \(A\): it contains
\(\omega=v^2\) and \(\alpha=s\omega\), and these generate the
compositum of \(\mathbb F_4\) and \(\mathbb F_8\), namely
\(\mathbb F_{64}\). Thus \(A_0=\mathbb F_{64}\).

The three coefficients \(s,t,v\) are linearly independent over
\(\mathbb F_2\). Multiplication by \(\omega\) reduces this to
independence of \(\alpha,\alpha^{-1},1\). A nonzero relation among
those three, multiplied by \(\alpha\), would give a polynomial of
degree at most two annihilating \(\alpha\), contradicting its
degree three over \(\mathbb F_2\). In particular, the marked root
subgroup is genuinely \(C_2^3\).

For \(\Delta=\operatorname{diag}(1,\omega^{-1},\omega)\), the
transformed marked generators are

\[
C=\omega^{-1}c_0,\qquad
b_1'=x_{12}(\alpha),\quad b_2'=x_{12}(\alpha^{-1}),\quad
b_3'=x_{12}(1).
\]

The constant-root construction in Section 2 applies with \(w=1\).
Together with \(x_{12}(\alpha)\), those roots generate
\(\operatorname{EL}_3(\mathbb F_8)=\operatorname{SL}_3(\mathbb F_8)\).
The element \(Cc_0^{-1}=\omega^{-1}I\) also belongs to \(K'\).
Conversely, every displayed marked generator lies in the product
of those two subgroups. Their intersection is trivial, since
\(\omega,\omega^{-1}\notin\mathbb F_8\). Therefore

\[
\boxed{K'=\operatorname{SL}_3(\mathbb F_8)
                   \times\langle\omega I\rangle
          \cong\operatorname{SL}_3(\mathbb F_8)\times C_3.}
\]

The recovered root-coefficient ring is exactly \(B=\mathbb F_8\).
Indeed, if \(x_{ij}(a)=\omega^r g\), with
\(g\in\operatorname{SL}_3(\mathbb F_8)\), its diagonal entries
force \(\omega^{-r}\in\mathbb F_8\), hence \(r=0\), and then
\(a\in\mathbb F_8\). In particular, \(x_{12}(\omega)\notin K'\),
so \(K'\) is a proper subgroup of
\(\operatorname{EL}_3(A_0)=\operatorname{SL}_3(\mathbb F_{64})\).
Conjugation by \(\Delta\) preserves this full special linear group;
thus the original \(K\) is proper as well.

This disproves the proposed shortcut
\(K=\operatorname{EL}_3(A_0)\) for arbitrary invertible \(ts\),
even with independent marked root coefficients. The cyclic quotient
in Sections 2--5 is needed. This is not a vanishing packet example:
here \(r_*'=\omega I\), \(R_v'=I\), and \(R_0'=x_{12}(1)\).
