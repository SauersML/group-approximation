# An explicit projective gap over every finite coefficient algebra

Date: 2026-09-08. Pure matrix and ring arguments; no code or build.

The three-word coefficient obstruction extends to every nonzero finite
unital \(\mathbb F_2\)-algebra, including algebras with a nilpotent
radical. The representation must extend to its full elementary group.
The bound below is explicit and does not use finite-simple-group
covering bounds.

## 1. Statement and native words

Let \(A\) be a nonzero finite unital \(\mathbb F_2\)-algebra, let
\(s,t,v\in A\), and put \(G=\operatorname{EL}_3(A)\). Use
\(x_{ij}(a)=I+aE_{ij}\), the coordinate cycle \(c=(123)\), and
\(b_1=x_{12}(s), b_2=x_{12}(t), b_3=x_{12}(v)\). The commutator
convention is \([x,y]=xyx^{-1}y^{-1}\).

For completeness, define the three native words by

\[
\begin{gathered}
\gamma=\operatorname{Ad}(c),\quad
d=[b_2,\gamma(b_1)],\quad h=\gamma^2(d),\quad a=[d,h],\quad
e=\gamma(d),\quad j=aea^{-1},\\
u=[b_2,\gamma(b_3)],\quad w=[\gamma^2(b_1),a],\\
r_*=jcjc,\qquad
R_v=[b_3,\gamma(b_3)]d^{-1},\qquad R_0=[u,w].
\end{gathered}
\]

These are the words of the
[finite coefficient packet](leavitt-24k-finite-coefficient-kernel-packet-2026-09-08.md).
No relation \(ts=1\) is assumed for their present evaluation.

**Theorem.** For every homomorphism \(\rho:G\to\operatorname{PU}(N)\),
write \(L(g)=d_{\rm sc}(\rho(g),1)\), where

\[
d_{\rm sc}(U,V)=\min_{|\zeta|=1}\|U-\zeta V\|_{2,N}.
\]

Then

\[
\boxed{L(c)\leq144L(r_*)+24L(R_v)+24L(R_0).}       \tag{1}
\]

Consequently, if a unitary representative \(C\) of \(\rho(c)\)
has normalized trace zero, then

\[
\boxed{\max\{L(r_*),L(R_v),L(R_0)\}
             \geq\frac{\sqrt2}{192}.}             \tag{2}
\]

The bounds are independent of the coefficient algebra, its radical
length, and the complex representation dimension and multiplicities.

## 2. Extract one useful coefficient from the first relator

Put

\[
Z=ts,\qquad f=1+Z^3,\qquad q=v^2+Z,\qquad p=tvsZ^2.
\]

The existing block calculations give
\(R_v=x_{13}(q)\), \(R_0=x_{12}(p)\), and

\[
jc=\begin{pmatrix}
Z^5&0&1+Z^3\\
1+Z^3&0&Z\\
0&1&0
\end{pmatrix}.
\]

Squaring verifies that the first row of \(r_*\) is

\[
\bigl(Z^{10},\ f,\ Z^5f\bigr).                   \tag{3}
\]

We use precisely
[Preusser, Proposition 9(i)](https://arxiv.org/pdf/1912.03536).
For an arbitrary unital ring, if \(\sigma\in\operatorname{GL}_n(A)\)
and a column \((x_1,\ldots,x_n)^T\) satisfies
\(\sum_i\sigma_{1i}x_i=0\) and \(x_n=0\), then every
\(x_{kl}(\alpha x_1\beta)\), \(k\ne l\), is a product of eight
\(\operatorname{EL}_n(A)\)-conjugates of \(\sigma\) and
\(\sigma^{-1}\). No commutativity, stable-range condition, or
semisimplicity is required in this proposition.

Apply it with \(n=3\), \(\sigma=r_*\), and

\[
(x_1,x_2,x_3)=(f,Z^{10},0).
\]

The required product is zero because
\(Z^{10}f+fZ^{10}=0\) in characteristic two. Hence, for arbitrary
\(\alpha,\beta\in A\) and any root position,

\[
L(x_{kl}(\alpha f\beta))\leq8L(r_*).              \tag{4}
\]

The other two coefficients need only elementary commutators. For
distinct \(i,j,k\), direct distinct-index identities give

\[
[[x_{ki}(\alpha),x_{ij}(z)],x_{ji}(\beta)]
                  =x_{ki}(\alpha z\beta).         \tag{5}
\]

This costs at most four conjugates of \(x_{ij}(z)\) and its inverse.
Coordinate permutations belong to \(\operatorname{EL}_3(A)\) in
characteristic two, so they carry its output to any root position.
Since \(L\) is conjugation-invariant and subadditive,

\[
L(x_{kl}(\alpha q\beta))\leq4L(R_v),\qquad
L(x_{kl}(\alpha p\beta))\leq4L(R_0).              \tag{6}
\]

All conjugations here take place in the full group \(G\).

## 3. Five coefficient terms generate one, including the radical

Let \(J\) be the Jacobson radical of \(A\). Its semisimple quotient
is a finite product of algebras \(M_d(\mathbb F_{2^a})\), with
possibly different \(d,a\) in each component. Work first in one
such component, retaining the names of the coefficient images.
Set

\[
r=\operatorname{rank}(f),\qquad
q_0=\operatorname{rank}(q),\qquad p_0=\operatorname{rank}(p).
\]

On \(\ker f\), the equality \(Z^3x=x\) shows that \(Z\) is
injective. Thus \(\operatorname{rank}Z\geq d-r\), and since
\(Z=ts\), \(\operatorname{nullity}t\leq r\). Also

\[
\operatorname{rank}v\geq\operatorname{rank}(v^2)
 =\operatorname{rank}(Z+q)\geq d-r-q_0.
\]

The map \(sZ^2\) is injective on \(\ker f\): if \(sZ^2x=0\)
there, then
\(x=Z^3x=tsZ^2x=0\). Therefore its nullity is at most \(r\).
The product-rank inequality now gives

\[
p_0=\operatorname{rank}(tvsZ^2)\geq d-q_0-3r,
\qquad p_0+q_0+3r\geq d.                          \tag{7}
\]

For matrices over a field, any matrix of rank at most
\(\operatorname{rank}z\) has the form \(\alpha z\beta\).
Partition a coordinate basis into five pieces whose sizes are at
most \(r,r,r,q_0,p_0\); (7) permits this, allowing empty pieces.
Write the five corresponding diagonal projections as products of
that form. Their sum is one. Performing this independently in each
simple component gives in \(A/J\) an identity with exactly five
coefficient terms, of types

\[
f,\ f,\ f,\ q,\ p.
\]

Lift all the left and right coefficients to \(A\). Their sum is
an element \(z\) congruent to one modulo \(J\), hence invertible.
Multiplying every left coefficient by \(z^{-1}\) yields the exact
identity in \(A\)

\[
1=\alpha_1f\beta_1+\alpha_2f\beta_2+\alpha_3f\beta_3
             +\alpha_4q\beta_4+\alpha_5p\beta_5.  \tag{8}
\]

There is no iteration through radical powers and no increase in the
number of terms. The inverse is absorbed into arbitrary coefficient
choices, which (4) and (6) already allow.

## 4. Finish the projective metric estimate

On a fixed root, coefficient addition is group multiplication.
Equations (4), (6), and (8) therefore show, for every \(k\ne l\),

\[
L(x_{kl}(1))\leq24L(r_*)+4L(R_v)+4L(R_0).         \tag{9}
\]

The coordinate cycle has the six-root expression

\[
c=\bigl(x_{12}(1)x_{21}(1)x_{12}(1)\bigr)
  \bigl(x_{23}(1)x_{32}(1)x_{23}(1)\bigr),
\]

because its two parenthesized factors are \((12)\) and \((23)\).
Subadditivity proves (1). Finally,
\(d_{\rm sc}(C,I)^2=2-2|\tau_N(C)|\), so the frozen trace-zero
condition gives (2). The argument takes place entirely in the
bi-invariant metric on \(\operatorname{PU}(N)\); it does not require
choosing compatible scalar representatives.

## 5. Scope

This closes the nilpotent-radical gap for exact representations of
full finite coefficient groups, and replaces the earlier unspecified
covering constant by an explicit bound for this construction. The
same proof works for every semilocal characteristic-two ring: its
semisimple quotient is a finite product of full matrix algebras over
division rings, where the same rank and matrix-factorization arguments
hold, and elements congruent to one modulo the Jacobson radical
remain invertible.

The distinction from arbitrary marked group models remains essential.
A representation of the subgroup generated by \(c,b_1,b_2,b_3\)
need not extend to \(\operatorname{EL}_3(A)\). In particular, the
auxiliary root elements and conjugators in (4)--(6), with the
coefficients selected in (8), need not lie in that marked subgroup.
This theorem neither constructs such an extension nor assigns
coefficient matrices to arbitrary frozen \(24k\) unitary tuples.
It does not decide hyperlinearity of the Leavitt unit group.

The subsequent [unit-product marked-subgroup theorem](leavitt-unit-product-marked-subgroup-projective-gap-2026-09-08.md)
does remove ambient extension whenever ts is a unit in a finite
coefficient algebra, without requiring ts=1. Its explicit scalar
gap is sqrt(2)/97. Section 6 below retains the sharper sqrt(2)/18
bound under the exact ts=1 hypothesis. The further
[unit-root theorem](leavitt-unit-root-marked-subgroup-projective-gap-2026-09-08.md)
keeps the gap sqrt(2)/97 whenever the marked group contains a
backward root with an invertible coefficient; this includes some
singular ts assignments. No coefficient construction is supplied
for arbitrary unitary tuples.

The [semisimple coefficient-generated theorem](leavitt-semisimple-path-algebra-marked-projective-gap-2026-09-08.md)
further removes ambient extension for every tuple generating a
semisimple finite algebra, including cases with no unit root. Its
gap is `sqrt(2-2sqrt(2/5))/97`. It does not remove the radical from
an arbitrary complex representation of a marked subgroup.

## 6. Literal ts=1 gives a sharper gap inside the marked subgroup

This section assumes that \(A\) is a nonzero unital directly finite
ring of characteristic two, and that the underlying coefficients
satisfy the exact identity \(ts=1\). Finiteness of \(A\) is not
required. Direct finiteness gives \(st=1\), so \(t=s^{-1}\).
Let \(A_0\) be the unital subring generated by \(s,t,v\), and put

\[
K=\langle c,x_{12}(s),x_{12}(t),x_{12}(v)\rangle.
\]

**Lemma.** One has \(K=\operatorname{EL}_3(A_0)\). For every
homomorphism \(\rho:K\to\operatorname{PU}(N)\), with \(L\) as
above,

\[
\boxed{L(c)\leq6L(R_v)+12L(R_0).}                \tag{10}
\]

A trace-zero representative of \(\rho(c)\) therefore forces

\[
\boxed{\max\{L(R_v),L(R_0)\}\geq\frac{\sqrt2}{18}.} \tag{11}
\]

In particular, this subcase needs no representation extension from
\(K\) to a larger ambient elementary group.

**Proof of the marked-group identification.** Since \(ts=1\), the
native words give

\[
d=x_{13}(1),\qquad \gamma^2(d)=x_{32}(1),\qquad
[d,\gamma^2(d)]=x_{12}(1).
\]

Cyclic conjugation supplies all six constant roots. Their products
give the coordinate transpositions, hence all coordinate permutation
matrices in \(K\). Permutation conjugation now gives all root
positions with each coefficient \(s,t,v\).

The set of coefficients \(z\in A_0\) for which all \(x_{ij}(z)\)
belong to \(K\) contains \(1,s,t,v\), is closed under addition by
the same-root identity, and is closed under multiplication by
\([x_{ij}(z),x_{jk}(w)]=x_{ik}(zw)\) at distinct indices.
In characteristic two it is also closed under additive inverses.
It is consequently all of \(A_0\). Thus
\(\operatorname{EL}_3(A_0)\subseteq K\), and the reverse inclusion
follows from the definitions and the six-root expression for \(c\).

**Proof of the metric bound.** The literal coefficient identities are

\[
R_v=x_{13}(v^2+1),\qquad R_0=x_{12}(tvs).
\]

The diagonal matrix

\[
D=\operatorname{diag}(s,s,s^{-2})
\]

belongs to \(K\). Indeed it is the product
\(\operatorname{diag}(s,s^{-1},1)\operatorname{diag}(1,s^2,s^{-2})\),
and each factor is elementary. Explicitly, for a unit \(z\), set

\[
w_{ij}(z)=x_{ij}(z)x_{ji}(z^{-1})x_{ij}(z).
\]

In characteristic two, \(w_{ij}(z)w_{ij}(1)\) has diagonal entries
\(z,z^{-1}\) in positions \(i,j\) and ones elsewhere.
Using both \(st=1\) and \(ts=1\), one obtains

\[
DR_0D^{-1}=x_{12}(s(tvs)t)=x_{12}(v).
\]

Therefore every root \(x_{ij}(v)\) has length \(L(R_0)\), and
every root \(x_{ij}(v^2+1)\) has length \(L(R_v)\), by permutation
conjugation inside \(K\). The distinct-index root identity gives

\[
x_{12}(1)
 =x_{12}(v^2+1)[x_{13}(v),x_{32}(v)].             \tag{12}
\]

For a conjugation-invariant length,
\(L([g,h])\leq2\min\{L(g),L(h)\}\). Hence (12) implies

\[
L(x_{12}(1))\leq L(R_v)+2L(R_0).
\]

All six constant roots are conjugate inside \(K\). Applying their
six-factor expression for \(c\) proves (10), and the trace-zero
identity \(L(c)=\sqrt2\) proves (11). \(\square\)

The hypothesis here is the literal ring equality \(ts=1\), together
with direct finiteness of the coefficient ring. A small scalar defect
of \(\rho(r_*)\), or even its being the identity in the projective
representation, does not supply that coefficient equality. Thus this
lemma does not remove the marked-subgroup extension issue for general
coefficient assignments or arbitrary frozen unitary tuples.
