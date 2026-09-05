# LVIII: contraction from uniformly small support, without a prescribed reservoir

Date: 5 September 2026. Complete proof; internal mathematical review completed.
No external review, formal verification, or novelty priority is claimed.
This gives a new sufficient localization condition and a necessary size
condition on a surviving unstable kernel. It does not localize every family
and does not solve LVIII.

## 1. Statement

Let \(B\) be a nonzero simple unital finite pure C*-algebra with
\(QT_1(B)\ne\varnothing\). Let \(X\) be a compact metric space of covering
dimension \(d\ge1\), and put \(A=C(X,B)\). For \(a\in A_+\), define
\[
 \Delta(a)=\sup_{x\in X,\ \tau\in QT_1(B)}d_\tau(a(x)).
 \tag{1}
\]
Here \(d_\tau(a)=\lim_n\tau(a^{1/n})\), after harmless positive rescaling
when necessary.

**Theorem 1.** Suppose \(u\in U(A)\), \([u]=0\) in \(K_1(A)\), and
\[
 \Delta(|u-1|)<\frac1{d+1}.
 \tag{2}
\]
Then \(u\in U_0(A)\).

More generally, it suffices that \(u-1\in\operatorname{Her}(h)\) for some
\(h\in A_+\) satisfying \(\Delta(h)<1/(d+1)\). Neither fullness of \(h\)
nor a nonzero element orthogonal to \(h\) is assumed.

For a based sphere \(X=S^k\), stable nullness means zero of the reduced
\(K_1(C(S^k,B))\)-class by the split evaluation and suspension sequence.
The contraction can be made based. In particular, every nonzero element
of the kernel of
\[
 \pi_kU(B)\longrightarrow K_{k+1}(B)
\]
has the following necessary property: **every** based representative \(u\)
satisfies
\[
 \sup_{x,\tau}d_\tau(|u(x)-1|)\ \ge\ \frac1{k+1}.
 \tag{3}
\]
No existence of such nonzero kernel elements is asserted.

The same argument applied to \(uv^*\) shows that unitaries \(u,v\) with
the same stable \(K_1\)-class and
\(\Delta(|uv^*-1|)<1/(d+1)\) lie in the same component. This is a
quantitative condition on support dimension, not operator norm.

## 2. Reviewed inputs and arbitrarily small full positive elements

The proof uses the previously internally reviewed
[soft-support reservoir theorem](stw58-soft-support-orthogonal-reservoir-contraction-2026-09-05.md).
In the notation here, that theorem contracts a stably zero unitary
supported in \(\operatorname{Her}(a)\) when
\[
 a\text{ is full},\quad ab=0,\quad (N-1)[a]\le[b],\quad N\ge d+1.
 \tag{4}
\]
For simple finite pure \(B\), it also proves the following sufficient
fiberwise comparison criterion when \(a,b\) are full:
\[
 d_\tau(a(x))\le\alpha,\quad d_\tau(b(x))\ge\beta,\quad
 (N-1)\alpha<\beta.
 \tag{5}
\]
This uses purity of \(C(X,B)\), strict comparison, and the proved passage
from uniform fiber quasitrace inequalities to global quasitraces.
In particular it does not assume that all quasitraces on \(C(X,B)\)
are elementary evaluations.

**Lemma 2.** For every \(\eta>0\) there is a nonzero positive contraction
\(c\in B\), full by simplicity, such that
\[
 \sup_{\tau\in QT_1(B)}d_\tau(c)<\eta.
 \tag{6}
\]

**Proof.** Choose an integer \(n>1/\eta\). The reviewed
[dimension-drop construction](stw58-compatible-split-stable-surjectivity-2026-09-05.md),
Section 2, supplies a unital homomorphism \(Z_{n,n+1}\to B\):
Lin gives stable rank one, almost divisibility and compactness of
\([1_B]\) give the finite-matrix inequalities required by
Rørdam--Winter, Proposition 5.1. Among the two canonical order-zero
endpoint maps choose a nonzero one \(\phi:M_\ell\to B\), where
\(\ell\in\{n,n+1\}\).

Its diagonal images \(c_j=\phi(e_{jj})\) are nonzero, orthogonal,
and Cuntz equivalent; their sum is the positive contraction
\(\phi(1)\). Thus for \(c=c_1\) and every normalized quasitrace,
\[
 \ell d_\tau(c)
 =d_\tau\!\left(\sum_{j=1}^{\ell}c_j\right)\le1.
\]
This proves (6). Neither a unital matrix subalgebra nor a projection
of small trace is required. \(\square\)

The prior-art source for the dimension-drop input is
[Rørdam--Winter, Proposition 5.1](https://web.math.ku.dk/~rordam/manus/jiang-su-revisited.pdf),
*The Jiang--Su algebra revisited*. The exact \(W(B)\) versus
\(\mathrm{Cu}(B)\) bridge is included in the linked reviewed proof.

## 3. Fullness enlargement and automatic reservoirs after cutoff

**Lemma 3.** Suppose \(h\in A_+\) and \(\Delta(h)<1/N\), where
\(N\ge2\). There is a full positive \(H\in A\) such that
\[
 \operatorname{Her}(h)\subseteq\operatorname{Her}(H),
 \qquad \Delta(H)\le\gamma<1/N.
 \tag{7}
\]
For every sufficiently small \(\varepsilon>0\), the elements
\[
 a_\varepsilon=(H-\varepsilon)_+,\qquad
 b_\varepsilon=(\varepsilon/2-H)_+
 \tag{8}
\]
are full in \(A\), are orthogonal, and satisfy
\[
 (N-1)[a_\varepsilon]\le[b_\varepsilon].
 \tag{9}
\]

**Proof.** Choose \(\eta>0\) with \(\Delta(h)+\eta<1/N\), choose \(c\)
from Lemma 2, and regard \(c\) as a constant section. Set \(H=h+c\).
The inequality \([h+c]\le[h]+[c]\) gives
\[
 d_\tau(H(x))\le d_\tau(h(x))+d_\tau(c),
\]
so (7) holds for some \(\gamma<1/N\). Positive domination \(h\le H\)
implies the hereditary inclusion in (7). The constant \(c\) is full
in \(A\): a finite sum of constant multiples of \(c\) approximating
\(1_B\) also approximates \(1_A\). Hence \(H\) is full.

Fullness of \(H\) implies fullness of \(a_\varepsilon\) for every
sufficiently small positive \(\varepsilon\). Indeed, fix a finite
sum \(\sum_j r_j H s_j\) within distance less than one from \(1_A\).
Replacing \(H\) by \(a_\varepsilon\) changes that sum by a quantity
tending to zero, so it remains invertible for small \(\varepsilon\).

Functional calculus gives \(a_\varepsilon b_\varepsilon=0\).
For any \(x,\tau\), restriction of \(\tau\) to the abelian algebra
generated by \(H(x)\) and the unit is a probability measure \(\mu\)
on its spectrum. Consequently
\[
 \begin{aligned}
 d_\tau(a_\varepsilon(x))
   &=\mu((\varepsilon,\infty))\le\gamma,\\
 d_\tau(b_\varepsilon(x))
   &=\mu([0,\varepsilon/2))
     \ge\mu(\{0\})
      =1-d_\tau(H(x))\ge1-\gamma.
 \end{aligned}
 \tag{10}
\]
In particular \(b_\varepsilon(x)\ne0\) at every \(x\).

A continuous positive section over a compact space with nonzero
fibers in a simple coefficient algebra is full. To see this directly,
at each point choose a finite positive sum of multiples of that fiber
which is invertible. The same holds nearby by norm continuity.
A finite subordinate central partition of unity combines these
local positive sums to an everywhere uniformly invertible element
of the generated ideal. Apply this to \(b_\varepsilon\).

Finally
\[
 (N-1)\gamma<1-\gamma
\]
because \(N\gamma<1\). Criterion (5), applied after any needed
positive normalization of \(a_\varepsilon,b_\varepsilon\), proves
(9). Only the strict-comparison part of criterion (5) is used here:
this comparison holds for every integer \(N\ge2\) under the stated
size bound. The additional inequality \(N\ge d+1\) is needed for
unitary contraction in Theorem 1, not for Lemma 3. \(\square\)

There is no approximation of a bidual support projection in this
argument. The reservoir in (8) is an actual continuous positive
element of \(A\). It is orthogonal to the cutoff, not necessarily to
the original \(H\) or \(h\).

## 4. Proof of Theorem 1

Use the general formulation with \(u-1\in\operatorname{Her}(h)\), and
take \(N=d+1\) in Lemma 3. The cutoff hereditary algebras
\(\operatorname{Her}(a_\varepsilon)\) have dense union in
\(\operatorname{Her}(H)\) as \(\varepsilon\downarrow0\). Choose
\(\varepsilon\) sufficiently small for Lemma 3 and
\(z\in\operatorname{Her}(a_\varepsilon)\) with
\[
 \|1+z-u\|<1/10.
 \tag{11}
\]
The polar unitary \(w\) of \(1+z\) belongs to
\(1+\operatorname{Her}(a_\varepsilon)\). Polar repair of the
straight-line path from \(u\) to \(1+z\) gives a unitary homotopy
from \(u\) to \(w\); the straight-line path is invertible throughout
by (11). Thus \([w]=[u]=0\) in \(K_1(A)\).

The full pair \(a_\varepsilon,b_\varepsilon\) satisfies (4).
The reviewed reservoir theorem therefore contracts \(w\) in \(U(A)\),
and hence contracts \(u\). This proves the general assertion.

For \(h=|u-1|\), the normality of \(u-1\) gives
\(u-1\in\operatorname{Her}(h)\); for example,
multiply \(u-1\) by continuous cutoffs of \(|u-1|\) and let the
cutoff threshold tend to zero. Thus (2) is the claimed special case.

If \(u\) is based at \(x_0\) and \(K(x,t)\) is any contraction with
\(K(x,0)=u(x)\), \(K(x,1)=1\), replace it by
\[
 K(x,t)K(x_0,t)^*.
\]
This is a based contraction with the same endpoints. Taking the
contrapositive gives (3). \(\square\)

## 5. Why a reservoir cannot be demanded before cutoff

Small support dimension alone does **not** imply that the original
hereditary algebra has a nonzero orthogonal complement inside \(B\).
This already fails in the \(2^\infty\) UHF algebra \(B\), which is
simple, finite, and pure.

Write its diagonal as \(D=C(K)\), where \(K=\{0,1\}^{\mathbb N}\)
has the fair Bernoulli probability measure \(\mu\). Given
\(0<\alpha<1\), choose a dense open set \(V\subset K\) with
\(\mu(V)<\alpha\): enumerate a countable dense subset and cover its
\(j\)-th point by a cylinder set of measure less than
\(\alpha 2^{-j-1}\). Their union has the required properties.
Choose \(h\in C(K)_+\) with \(\{h>0\}=V\); for example, use the
distance to the closed complement for a compatible metric.
The unique trace satisfies
\[
 d_\tau(h)=\mu(V)<\alpha.
\]

Nevertheless there is no nonzero positive \(b\in B\) with \(hb=0\).
The canonical diagonal expectation \(E:B\to D\) is faithful and
\(D\)-bimodular. If \(hb=0\), then \(hE(b)=0\). Since \(h\) is
positive on the dense set \(V\), continuity forces \(E(b)=0\),
and faithfulness forces \(b=0\).

For completeness, this expectation is obtained by the compatible
finite-matrix diagonal expectations. It preserves the unique
faithful trace, so it is faithful. The same standard input appears
explicitly in [Akemann--Eilers, *Regularity of projections revisited*,
Proposition 3.7, printed p. 524](https://jot.theta.ro/jot/archive/2002-048-003/2002-048-003-004.pdf).
No external input about exotic hereditary subalgebras is required.

Thus the original orthogonality hypothesis was a genuine restriction.
Lemma 3 removes it by first passing to a cutoff while retaining
control of the unitary by norm approximation.

## 6. What remains

The theorem applies in projectionless coefficient algebras and to
supports vanishing at some parameter points. It removes two
hypotheses from the earlier supported contraction result: a prescribed
full support and a prescribed orthogonal reservoir.

It does not prove that every stably null sphere family can be deformed
to satisfy (2), nor that it factors globally into families which do.
Pointwise smallness, local logarithms, and a norm-local word
factorization do not supply such a global deformation. A full solution
would need a further argument that changes or fragments the support
dimension while respecting transition topology. Equation (3) states
the precise quantitative constraint any surviving kernel must obey.
