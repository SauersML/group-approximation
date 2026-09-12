# Directed coefficient compactness and the central envelope

## Outcome

Let

\[
P=\langle s_1,\ldots ,s_d\mid r_1,\ldots ,r_\ell\rangle=F/N
\]

be finitely presented, and let $w\in R_{\rm fin}(P)$. For every finite
quotient of $P$, the class of $w$ in the canonical relation module is an
integral combination of the fixed relator classes. This note proves that
the corresponding shortest coefficient norms are uniformly bounded if and
only if **one coefficient vector works in every finite quotient**.

The common-vector condition has an exact group-theoretic interpretation.
Put

\[
\widetilde R=\bigcap_{N\leq L\lhd_{\rm fi}F}L,
\qquad
J=\bigcap_{N\leq L\lhd_{\rm fi}F}[F,L].
\]

Then

\[
\boxed{
\sup_L\delta_L(w)<\infty
\quad\Longleftrightarrow\quad
W\in NJ,
}
\]

where $W\in\widetilde R$ represents $w$.

There is a second, more structural description. Define the central
envelope

\[
E=F/[F,\widetilde R],
\qquad
Z=\widetilde R/[F,\widetilde R]\leq Z(E).
\]

The hidden intersection $J$ is precisely the finite residual of this
central envelope:

\[
\boxed{
J/[F,\widetilde R]=R_{\rm fin}(E).
}
\]

Consequently the exact obstruction group for the canonical central route is

\[
\Omega(P;F,N)
:=
\frac{Z}
{\,N[F,\widetilde R]/[F,\widetilde R]+R_{\rm fin}(E)\,}.
\]

For a nontrivial $w\in\operatorname{Rad}_{\rm sof}(P)$, the canonical
central construction proves the existence of a hyperlinear nonsofic group
if and only if the class of $W$ in $\Omega(P;F,N)$ is nonzero.

This sharpens the earlier candidate screen. Nonzero
$R_{\rm fin}(P)/[P,R_{\rm fin}(P)]$ is necessary but not sufficient: the
finite residual of $E$ may absorb the class. If $E$ is residually finite,
however, every nonzero finite-residual coinvariant class is a complete
FALSE certificate.

## 1. Canonical relation modules

Finite quotients $P\twoheadrightarrow Q$ are represented by normal
finite-index subgroups

\[
N\leq L\lhd_{\rm fi}F,
\qquad Q=F/L.
\]

Set

\[
C_L=L/[F,L].
\]

Because $w\in R_{\rm fin}(P)$, its fixed lift $W\in F$ belongs to every
such $L$. Write $a_{j,L}\in C_L$ for the class of $r_j$ and
$b_L\in C_L$ for the class of $W$.

### Lemma 1 (integral containment from the finite residual)

For every $L$,

\[
b_L\in\langle a_{1,L},\ldots ,a_{\ell,L}\rangle.
\]

#### Proof

Let $K=L/N\lhd P$. There is a canonical isomorphism

\[
\frac{C_L}{\langle a_{1,L},\ldots ,a_{\ell,L}\rangle}
\cong
\frac{K}{[P,K]}.
\]

The group $P/[P,K]$ is finitely generated and has the central subgroup
$K/[P,K]$ of finite index. It is therefore finitely generated virtually
abelian, hence residually finite. If the image of $w$ in $K/[P,K]$
were nontrivial, a finite quotient of $P/[P,K]$, and therefore a finite
quotient of $P$, would separate $w$. This contradicts
$w\in R_{\rm fin}(P)$. Thus the image is zero. \(\square\)

Define

\[
S_L=
\left\{
v\in\mathbb Z^\ell:
b_L=\sum_{j=1}^\ell v_ja_{j,L}
\right\}
\]

and

\[
\delta_L(w)=\min_{v\in S_L}\|v\|_2.
\]

Lemma 1 says that every $S_L$ is nonempty.

If $L'\leq L$, inclusion induces a homomorphism

\[
C_{L'}\longrightarrow C_L
\]

which preserves the marked and relator classes. Hence

\[
S_{L'}\subseteq S_L. \tag{1}
\]

The family is directed: the common refinement of finitely many $L_i$ is
$L_*:=\bigcap_iL_i$.

## 2. A finite-intersection theorem

### Theorem 2 (directed coefficient compactness)

The following are equivalent:

1. $\sup_L\delta_L(w)<\infty$;
2. there exists $v\in\mathbb Z^\ell$ which belongs to every $S_L$.

#### Proof

The implication $2\Rightarrow1$ is immediate.

Suppose $\delta_L(w)\leq B$ for all $L$, and let

\[
V_B=\{v\in\mathbb Z^\ell:\|v\|_2\leq B\}.
\]

This is a finite set. Each $S_L\cap V_B$ is nonempty. Given finitely
many $L_1,\ldots,L_m$, their common refinement $L_*=\bigcap_iL_i$
satisfies, by (1),

\[
\varnothing\neq S_{L_*}\cap V_B
\subseteq
\bigcap_{i=1}^m(S_{L_i}\cap V_B).
\]

Thus the subsets $S_L\cap V_B$ of the finite set $V_B$ have the finite
intersection property. Their total intersection is nonempty. \(\square\)

This argument gives the useful contrapositive

\[
\boxed{
\bigcap_LS_L=\varnothing
\quad\Longleftrightarrow\quad
\sup_L\delta_L(w)=\infty.
} \tag{2}
\]

No quantitative character estimate or matrix optimization is involved.

## 3. The commutator-intersection criterion

Let

\[
J=\bigcap_{N\leq L\lhd_{\rm fi}F}[F,L].
\]

For $v=(v_1,\ldots,v_\ell)$, put

\[
n_v=\prod_{j=1}^\ell r_j^{v_j}.
\]

The order chosen in this product is irrelevant modulo every $[F,L]$.
By definition,

\[
v\in S_L
\quad\Longleftrightarrow\quad
Wn_v^{-1}\in[F,L].
\]

Therefore Theorem 2 gives

\[
\sup_L\delta_L(w)<\infty
\quad\Longleftrightarrow\quad
Wn_v^{-1}\in J
\text{ for some }v. \tag{3}
\]

Every $n\in N$ is congruent modulo $[F,N]$ to some $n_v$, because the
images of the defining relators generate $N/[F,N]$. Moreover

\[
[F,N]\leq[F,\widetilde R]\leq J.
\]

Thus $W\in NJ$ is equivalent to $Wn_v^{-1}\in J$ for some $v$. We have
proved:

### Corollary 3

\[
\boxed{
\sup_L\delta_L(w)<\infty
\quad\Longleftrightarrow\quad
W\in NJ.
} \tag{4}
\]

Equivalently, the canonical coefficient norms diverge precisely when the
class of $W$ is nonzero in $\widetilde R/NJ$.

## 4. The central-envelope identity

Put

\[
B=[F,\widetilde R],
\qquad
E=F/B,
\qquad
Z=\widetilde R/B.
\]

Then $Z\leq Z(E)$, and

\[
E/Z\cong F/\widetilde R
\cong P/R_{\rm fin}(P).
\]

The last group is residually finite by the definition of the finite
residual.

### Theorem 4 (central-envelope finite residual)

\[
\boxed{J/B=R_{\rm fin}(E).} \tag{5}
\]

In particular $R_{\rm fin}(E)\leq Z$.

#### Proof

For every $L$, write $\overline L=L/B\lhd E$. These are exactly the
normal finite-index subgroups of $E$ which contain $Z$, and

\[
[F,L]/B=[E,\overline L].
\]

Hence

\[
J/B=\bigcap_{\overline L\geq Z}[E,\overline L], \tag{6}
\]

where the intersection ranges over normal finite-index subgroups containing
$Z$.

First let $x$ lie in the right side of (6). Its image in $E/Z$ lies in

\[
\bigcap_{K\lhd_{\rm fi}E/Z}[E/Z,K].
\]

This intersection is trivial: $[E/Z,K]\leq K$, while $E/Z$ is
residually finite. Thus $x\in Z$.

Let $M\lhd_{\rm fi}E$ be arbitrary. The subgroup $MZ$ is normal,
finite index, and contains $Z$. Since $Z$ is central,

\[
x\in[E,MZ]=[E,M]\leq M.
\]

Thus $x\in R_{\rm fin}(E)$.

Conversely, let $x\in R_{\rm fin}(E)$, and fix $\overline L\geq Z$ as
in (6). The image of $\overline L$ is central in

\[
E/[E,\overline L]
\]

and has finite index there. This quotient is finitely generated and
virtually abelian, hence residually finite. The image of $x$, being in
the finite residual of every quotient of $E$, must therefore be trivial.
So $x\in[E,\overline L]$. Since $\overline L$ was arbitrary, $x$
lies in the right side of (6). \(\square\)

## 5. The exact obstruction group

Let

\[
\overline N=NB/B\leq Z.
\]

By Corollary 3 and Theorem 4,

\[
\sup_L\delta_L(w)<\infty
\quad\Longleftrightarrow\quad
W+B\in\overline N+R_{\rm fin}(E).
\]

Define

\[
\boxed{
\Omega(P;F,N)
=
Z/\bigl(\overline N+R_{\rm fin}(E)\bigr).
} \tag{7}
\]

Then

\[
\boxed{
\sup_L\delta_L(w)=\infty
\quad\Longleftrightarrow\quad
[W]_{\Omega}\neq0.
} \tag{8}
\]

There is a natural identification

\[
Z/\overline N
\cong
\frac{R_{\rm fin}(P)}{[P,R_{\rm fin}(P)]}. \tag{9}
\]

Indeed, the preimage in $\widetilde R$ of
$[P,R_{\rm fin}(P)]$ is $N[F,\widetilde R]=NB$. Therefore
$\Omega$ is the quotient of the ordinary finite-residual coinvariants by
the image of the second finite residual $R_{\rm fin}(E)$.

### Corollary 5 (residually finite envelope criterion)

If $E$ is residually finite, then

\[
\Omega(P;F,N)
\cong
R_{\rm fin}(P)/[P,R_{\rm fin}(P)].
\]

Consequently, if $w\in\operatorname{Rad}_{\rm sof}(P)\setminus\{1\}$,
the image of $w$ in $R_{\rm fin}(P)/[P,R_{\rm fin}(P)]$ is nonzero,
and $E$ is residually finite, then the canonical central-character
construction produces a hyperlinear nonsofic group.

#### Proof

Residual finiteness of $E$ makes $R_{\rm fin}(E)=1$, so (7)--(9) give
the algebraic assertion. The nonzero class gives unbounded coefficient
distortion by (8). Fixed-rank character compactness converts this into
unbounded character ratios, and the universal centralized-presentation
criterion then constructs a hyperlinear image retaining $w$. Since
$w$ lies in the sofic radical, that image is nonsofic. \(\square\)

## 6. The whole Kazhdan infranormal-double class fails the first screen

The vanishing for the Laurent pair is not special.

### Proposition 6 (infranormal relative-\(H_1\) vanishing)

Let \(\Gamma\leq G\) be infranormal in the Kun--Thom sense: the semigroup

\[
\mathcal S=\{s\in G:s\Gamma s^{-1}\leq\Gamma\}
\]

generates \(G\). Let \(N=\langle\!\langle\Gamma\rangle\!\rangle_G\), and
assume that \(\Gamma_{\rm ab}\) is finite. Then inclusion induces a
surjection

\[
\Gamma_{\rm ab}\twoheadrightarrow N_{\rm ab}.
\]

For the symmetric-double kernel

\[
R=\ker(G*_\Gamma G\longrightarrow G*_N G)
\]

one consequently has

\[
R/[G*_\Gamma G,R]=0.
\]

#### Proof

Let \(B\) be the image of \(\Gamma\) in \(N_{\rm ab}\). It is finite. For
each \(s\in\mathcal S\), conjugation by \(s\) is an automorphism of
\(N_{\rm ab}\), while the compression inclusion gives
\(\operatorname{Ad}(s)B\leq B\). Its restriction to the finite group \(B\)
is injective, hence \(\operatorname{Ad}(s)B=B\). Since \(\mathcal S\)
generates \(G\), the subgroup \(B\) is \(G\)-invariant.

The normal closure \(N\) is generated by the \(G\)-conjugates of
\(\Gamma\). Their images in \(N_{\rm ab}\) are all \(B\), so
\(B=N_{\rm ab}\). This proves surjectivity.

The standard Bass--Serre relation-module sequence for the symmetric double
gives

\[
R/[G*_\Gamma G,R]
\cong
\operatorname{coker}(\Gamma_{\rm ab}\to N_{\rm ab}),
\]

which now vanishes. \(\square\)

Every Kazhdan group has finite abelianization. Thus every element of the
displayed Kun--Thom double kernel has zero class in \(\Omega\), independently
of the chosen finite presentation. When \(G*_N G\) is residually finite, so
that this kernel is the full finite residual, one gets \(\Omega=0\) outright.
A central-route replacement cannot be obtained merely by changing the
coefficient ring or the compressor inside that theorem. It must use a
genuine \(H_2\) central extension before forming the model, abandon the
symmetric-double radical, or remain noncentral.

## 7. Consequences for the search

The new screen has three levels.

1. If $R_{\rm fin}(P)=[P,R_{\rm fin}(P)]$, then $\Omega=0$. This is
   exactly what happens for the current Kun--Thom symmetric double.
2. A nonzero coinvariant class is necessary, but it may still die in the
   image of $R_{\rm fin}(E)$.
3. A nonzero coinvariant class together with residual finiteness of the
   central envelope $E$ is already a complete FALSE proof.

Thus a replacement-candidate search should not start with matrices. It
should compute the marked class in (9) and then test residual finiteness of
the finitely generated central envelope $E$. The genuinely noncentral
kernel-carry route remains the only surviving route for the present
symmetric double.
