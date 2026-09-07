# Locally finite-dimensional compression and the Jacobson MF radical

This is a complete written proof and audit of the new results in
[non_mf_groups_exist.tex](../../non_mf_groups_exist.tex), at labels
thm:finite-dimensional-orbit, cor:locally-finite-compression,
thm:positive-characteristic, and cor:jacobson-mf-radical.
The new analytic assembly and the new ring endpoint have not been
formalized in Lean. Existing manuscript verification markers do not
certify these extensions.

## The structural theorem

Let $G$ be countable, let $L\le G$ have property (T), and suppose
$H=uLu^{-1}\le L$. Let
$$
 \Theta:G\longrightarrow U(Q_{\mathbf d}),\qquad
 Q_{\mathbf d}=\prod_n M_{d_n}(\mathbb C)/\bigoplus_n M_{d_n}(\mathbb C).
$$
If $a\in Q_{\mathbf d}$ commutes with $\Theta(H)$, and
$$
 C^*(1,\Theta(g)a\Theta(g)^*:g\in F)
$$
is finite-dimensional for every finite $F\subset L$, then $a$
commutes with $\Theta(L)$.

The element $a$ need not be a unitary or have finite order. The orbit
need not commute. Its finite-dimensional algebras need not have a
uniform dimension bound.

### Local lifting and correction

Write $a_g=\Theta(g)a\Theta(g)^*$, and exhaust the orbit algebra by
nested finite-dimensional unital algebras $D_m$.
For each fixed $m$, the inclusion $D_m\to Q_{\mathbf d}$ has a
unital homomorphic lift on a tail of the coordinates: round diagonal
matrix units to orthogonal projections, and polar-decompose compressed
first-column lifts. The remaining matrix units are their pairwise
products. This is the usual finite-dimensional matrix-unit lifting
argument, recalled in the manuscript.

Choose bases of all $D_m$. Diagonalizing over these countably many
basis elements gives $m(n)\to\infty$ and unital homomorphisms
$\rho_n:D_{m(n)}\to M_{d_n}$ such that
$[\rho_n(x)]_n=x$ for every fixed $x\in\bigcup_m D_m$.
Each coordinate is exact on its current domain. No compatibility of
the homomorphisms at different coordinates is required.

We use the following elementary intertwiner correction. For a fixed
finite-dimensional unital algebra $D$, suppose unital homomorphisms
$\alpha_n,\beta_n:D\to M_{d_n}$ and unitaries $U_n$ satisfy
$$
 \|U_n\alpha_n(x)U_n^*-\beta_n(x)\|\longrightarrow0\quad(x\in D).
$$
Finite-dimensionality makes this convergence uniform on $U(D)$.
The Haar average
$$
 T_n=\int_{U(D)}\beta_n(v)U_n\alpha_n(v)^*\,dv
$$
intertwines $\alpha_n$ with $\beta_n$ and satisfies
$\|T_n-U_n\|\to0$. Eventually it is invertible. Its polar part
$W_n=T_n(T_n^*T_n)^{-1/2}$ is a unitary intertwiner and
$\|W_n-U_n\|\to0$.

### A cocycle at the displacement scale

Choose unitary lifts $V_n(g)$ of $\Theta(g)$. Define
$$
 c_n(g)=\rho_n(a_g-a).
$$
For fixed $h,g\in L$, apply the correction to
$$
 D=C^*(1,a,a_g),\quad
 \alpha_n(x)=\rho_n(x),\quad
 \beta_n(x)=\rho_n(\Theta(h)x\Theta(h)^*).
$$
Both maps are defined on a tail, and $V_n(h)$ asymptotically
intertwines them. Hence there are unitaries $W_n(h,g)$ such that
$$
 c_n(hg)-c_n(h)=W_n(h,g)c_n(g)W_n(h,g)^*,\qquad
 \|W_n(h,g)-V_n(h)\|\longrightarrow0.                 \tag{1}
$$
All Hilbert--Schmidt norms below are unnormalized.

Suppose $a$ is moved by $L$. Choose a finite symmetric generating
set $S$ of $L$. A generator moves $a$, so on a subsequence
$$
 k_n=\max_{s\in S}\|c_n(s)\|_{\rm HS}\ge\epsilon>0.
$$
Equation (1) and the triangle inequality give, for each fixed $g$,
$$
 \|c_n(g)\|_{\rm HS}\le |g|_S k_n
$$
eventually. Consider the Hilbert ultraproduct of
$H_n=(M_{d_n},k_n^{-1}\|\cdot\|_{\rm HS})$.
The maps $\sigma_n(g)=\operatorname{Ad}V_n(g)$ give a unitary
representation $\sigma$ of $G$ on this ultraproduct, factoring
through the norm matrix corona
$\mathcal B=\prod B(H_n)/\bigoplus B(H_n)$.
Rescaling the Hilbert norm does not change the estimate
$\|\operatorname{Ad}U-\operatorname{Ad}V\|\le2\|U-V\|$.

The critical estimate is
$$
 \frac{\|c_n(hg)-c_n(h)-\sigma_n(h)c_n(g)\|_{\rm HS}}{k_n}
 \le 2\|W_n(h,g)-V_n(h)\|\,|g|_S\longrightarrow0.       \tag{2}
$$
Thus $c(g)=[c_n(g)]_\omega$ is a cocycle, with
$\max_{s\in S}\|c(s)\|=1$ and $c|_H=0$.

Property (T), by Delorme--Guichardet, makes
$c(g)=\sigma(g)\xi-\xi$. Thus $\xi$ is $H$-fixed.
Let $P$ be the image of the Kazhdan projection of $L$ in
$\mathcal B$, and let $U=[\sigma_n(u)]_n$.
Compression gives $U^*PU\le P$; finiteness of the norm matrix
corona gives equality. Consequently $UPU^*=P$, so the fixed spaces
of $H$ and $L$ on the Hilbert ultraproduct coincide.
Then $\xi$ is $L$-fixed and $c=0$, a contradiction.

The corrections in (1) are chosen separately for each fixed pair.
They are not asserted to form a representation. Equation (2) is
enough; it is precisely the estimate needed to handle growing
finite-dimensional algebras.

## Locally finite subgroups

If $A\le G$ is locally finite and normalized by $L$, and
$b\in A\cap C_G(H)$, apply the theorem to $a=\Theta(b)$.
Finitely many conjugates generate a finite subgroup, whose complex
group algebra has finite-dimensional image. Every corona
homomorphism therefore kills $[b,L]$. The same holds for every MF
target, since it embeds into a norm matrix corona.

This retains property (T) of the compressed group $L$; it imposes
no property (T) condition on $A$.

## One-sided inverses with additively torsion defect

Let $R$ be countable and unital, with $ts=1$, and put $e=1-st$.
Suppose $e\ne0$ and $qe=0$ for some positive integer $q$.
Let $S$ be the unital subring generated by $s,t$.
The ideal $I=SeS$ is spanned additively by
$$
 f_{ij}=s^iet^j,\qquad f_{ij}f_{kl}=\delta_{jk}f_{il}.
$$
Indeed words reduce to $s^it^j$, and $te=es=0$.
Each span with $i,j<N$ is a finite ring: all its matrix units
are annihilated by $q$. Its identity is
$p_N=\sum_{i<N}f_{ii}$.

The kernel $A=\operatorname{GL}_4(S)\cap(1+M_4(I))$ is locally
finite. Given finitely many elements, put all entries of them minus
the identity and their inverses minus the identity in one such
finite ring. They then lie in a finite group of the form
$1-P+M_4(I_N)^\times$, where $P=\operatorname{diag}(p_N,\ldots,p_N)$.

In $G=\operatorname{EL}_4(S)$, let $L=\operatorname{EL}_3(S)$ on
the first three coordinates. The ring $S$ is finitely generated,
so $L$ has property (T) by Ershov--Jaikin-Zapirain, Theorem 1.1.
The manuscript's rank-four compression cell, which uses only $ts=1$,
gives
$$
 uLu^{-1}\le L,\quad c\in C_G(L),\quad
 b=ucu^{-1}=e_{12}(e),\quad [b,e_{23}(1)]=e_{13}(e)\ne1.
$$
Here $b\in A\cap G$ centralizes $uLu^{-1}$, so locally finite
compression kills $e_{13}(e)$ in every MF homomorphism.
Restricting from $\operatorname{EL}_n(R)$ and conjugating by signed
elementary permutations gives the same conclusion for every
$e_{ij}(e)$, $n\ge4$.

In particular, every non-directly-finite ring of positive
characteristic yields a non-MF elementary group in every rank at
least four. Composite characteristic is allowed. Fullness of $e$
is not required.

## Exact radical for the binary Jacobson algebra

For $J=\mathbb F_2\langle s,t\mid ts=1\rangle$, the standard
one-sided shift representation is faithful. The ideal $JeJ$ is
the finitary matrix algebra and $J/JeJ=\mathbb F_2[z,z^{-1}]$.
Thus, for $n\ge4$,
$$
 1\longrightarrow L_{\rm fin}
 \longrightarrow\operatorname{EL}_n(J)
 \longrightarrow\operatorname{EL}_n(\mathbb F_2[z,z^{-1}])
 \longrightarrow1,                                   \tag{3}
$$
where $L_{\rm fin}=\operatorname{GL}_{\rm fin}(\mathbb N\times
\{1,\ldots,n\},\mathbb F_2)$.

For completeness, elementary roots with coefficients $s^iet^j$
give transvections between different coordinate rays. Commutators
through another ray give those within one ray. Since all invertible
finite matrices over $\mathbb F_2$ have determinant one, these
transvections generate the entire finitary kernel in (3).

The preceding theorem kills $e_{13}(e)$. Its conjugates by finitary
permutation matrices include every finitary transvection, so every
MF homomorphism kills $L_{\rm fin}$.
The quotient in (3) is residually finite: reduce Laurent polynomials
modulo irreducibles different from $z$, choosing one that does not
divide a selected nonzero matrix entry of $g-1$.
An element outside $L_{\rm fin}$ therefore survives in a finite
quotient. Consequently
$$
 \operatorname{Rad}_{\rm MF}(\operatorname{EL}_n(J))=L_{\rm fin}.
$$
The existing established claim
[binary-jacobson-steinberg-cover-is-elementary](../binary-jacobson-steinberg-cover-is-elementary.md)
transfers the rank-five result to $\operatorname{St}_5(J)$.

## Provenance and scope

Repository and primary-source status checked September 7, 2026.
The semisimple packet and binary Jacobson head-root targets were open
before this route. The fixed finite-packet case, finite-dimensional
exactification, and weighted Kazhdan transport were already present.

The cocycle strategy extends
[Eckhardt, Theorem 4.3](https://arxiv.org/html/2608.28772v1).
The property (T) input for elementary groups is
[Ershov--Jaikin-Zapirain, Theorem 1.1](https://arxiv.org/abs/0809.4095).
The fixed-point characterization is Bekka--de la Harpe--Valette,
*Kazhdan's Property (T)*, Theorem 2.12.4, already cited in the manuscript.
The additional step here is the local correction estimate (2) and
its use for growing orbit algebras and the Jacobson ideal.
No assertion of priority in the external literature is made.

The accompanying standard-library Python checker,
[check_locally_finite_compression.py](../../scripts/check_locally_finite_compression.py),
replays the compressor and centralizer calculations in the universal
ring $\mathbb Z\langle s,t,a\mid ts=1\rangle$, with a free coefficient
$a$. It also checks 1,296 matrix-unit products and 432 rational
noncommuting covariance examples, including the exact polar
correction and relative Hilbert--Schmidt estimate. These checks
supplement the written proof; they do not verify its analytic limits.

Exact finite-dimensionality of each orbit window is a hypothesis.
Approximate finite-dimensionality of its closure alone is not
asserted to suffice. Neither the ring statement in general
characteristic without additive torsion nor a hyperlinear obstruction
is proved here. The Jacobson example has a nontrivial residually finite
quotient, so the result computes its radical rather than claiming
every MF homomorphism is trivial.
