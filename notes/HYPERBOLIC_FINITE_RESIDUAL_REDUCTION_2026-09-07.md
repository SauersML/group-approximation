# Hyperbolic residual finiteness: finite-kernel reduction

## Status and scope

Checked on 2026-09-07: the unrestricted question whether every
word-hyperbolic group is residually finite remains open in the primary
sources checked. Cui--Wan, [arXiv:2604.04007v1, Section 1.2](https://arxiv.org/html/2604.04007v1),
explicitly records its open status. Sisto--Wilton,
[arXiv:2410.00556](https://arxiv.org/abs/2410.00556), treats universal
residual finiteness of hyperbolic groups as a hypothesis.

This note does not give a proof or a counterexample. It records complete
elementary arguments about the finite residual, to make the existing
finite-central-extension approach more precise. These are deductions from
standard residual-finiteness arguments, with no claim of historical novelty
or Lean verification.

Write

$$
R(G)=\bigcap_{f:G\to F,\ F\text{ finite}}\ker f.
$$

This is a characteristic normal subgroup. It also equals the intersection
of all finite-index subgroups: every such subgroup contains its normal core,
which is the kernel of its finite coset action.

The distinction between this residual and the **finite radical** (the
largest finite normal subgroup, when it exists) is essential. The finite
residual need not be finite.

## 1. Exact passage through a finite normal quotient

**Proposition.** Let $K\trianglelefteq G$ be finite, and let
$q:G\to G/K$ be the quotient map. No finite-generation, hyperbolicity, or
residual-finiteness assumption on $G$ is needed. Then

$$
R(G/K)=q(R(G))=R(G)K/K,
\qquad q^{-1}(R(G/K))=R(G)K.
$$

**Proof.** Every homomorphism $G/K\to F$ to a finite group pulls back to a
homomorphism $G\to F$. Thus it kills $q(R(G))$, giving one inclusion.

For the converse let $x\notin R(G)K$. For each $k\in K$, the element
$xk^{-1}$ is outside $R(G)$, so choose a finite group $F_k$ and a
homomorphism $f_k:G\to F_k$ with $f_k(xk^{-1})\ne1$. Form

$$
f=(f_k)_{k\in K}:G\longrightarrow\prod_{k\in K}F_k.
$$

This target is finite because $K$ is finite. If $f(x)=f(k)$ for some
$k\in K$, its $k$-coordinate contradicts the choice of $f_k$. Consequently
$f(x)\notin f(K)$. Normality of $K$ implies $f(K)\trianglelefteq f(G)$.
The homomorphism

$$
G/K\longrightarrow f(G)/f(K),\qquad gK\longmapsto f(g)f(K)
$$

is well-defined, has finite target, and does not kill $xK$. Hence
$xK\notin R(G/K)$. This proves the reverse inclusion and the inverse-image
formula. $\square$

In particular, a quotient of a residually finite group by a finite normal
subgroup is residually finite. The proposition concerns a **quotient with
finite kernel**; it does not assert that arbitrary quotients preserve
residual finiteness or that arbitrary finite-kernel extensions do so.

## 2. Two elementary facts needed for the next reduction

**Finite-index heredity.** If $L\le G$ has finite index, then, identifying
$L$ with its image in $G$,

$$R(L)=R(G).$$

In particular $R(G)\le L$. To prove the displayed equality, first observe
that restricting any finite homomorphism of $G$ to $L$ gives
$R(L)\le R(G)$. Conversely, a subgroup of finite index in $L$ has finite
index in $G$, so it contains $R(G)$. Intersect all such subgroups of $L$.
This gives the other inclusion. $\square$

This equality is already available in the repository in
`GroupApproximation/Algebra/FiniteResidual.lean` and
`GroupApproximation/Algebra/FiniteResidualCommensurability.lean`.

**Residual quotient.** For every group $G$, the quotient $G/R(G)$ is
residually finite. If $x\notin R(G)$, choose a finite homomorphism not
killing $x$. Its kernel contains $R(G)$ by definition, so the homomorphism
descends to $G/R(G)$ and separates $xR(G)$. $\square$

## 3. A central prime kernel over the original base, up to finite index

**Theorem.** Suppose

$$1\longrightarrow K\longrightarrow E\overset{\pi}{\longrightarrow}H
\longrightarrow1$$

is exact, $K$ is finite, $H$ is residually finite, and $E$ is not
residually finite. Put $R=R(E)$. Then $R$ is a nontrivial finite abelian
subgroup of $Z(K)$. There are a finite-index normal subgroup $L$ of $E$,
a finite-index normal subgroup $H_0=\pi(L)$ of $H$, a prime $p$, and
$B\le R$ such that

$$
L\cap K=R\le Z(L),\qquad R/B\cong C_p,
$$

and the induced sequence

$$1\longrightarrow R/B\longrightarrow L/B\longrightarrow H_0
\longrightarrow1$$

is central, with

$$R(L/B)=R/B\cong C_p.$$

Moreover,

$$[E:L]=[H:H_0]\,[K:R].$$

If $H$ is word-hyperbolic, then $E$, $L$, $L/B$, and $H_0$ are
word-hyperbolic. Thus allowing a noncentral finite kernel does not enlarge
this counterexample approach beyond central prime kernels over
finite-index subgroups of residually finite hyperbolic bases.

**Proof.**

1. If $e\notin K$, residual finiteness of $H$ supplies a finite
   homomorphism detecting $\pi(e)$. Composing with $\pi$ detects $e$.
   Therefore $R\le K$. Since $E$ is not residually finite, $R\ne1$.

2. Conjugation gives a homomorphism
   $c:E\to\operatorname{Aut}(K)$ with finite target. Hence $R\le\ker c$.
   Combining this with $R\le K$ gives $R\le Z(K)$; in particular $R$ is
   abelian. This proves centrality in $K$, not yet centrality in $E$.

3. For each $k\in K\setminus R$, choose a finite homomorphism
   $f_k:E\to F_k$ detecting $k$. Let $f$ be their diagonal product,
   taking the trivial homomorphism if $K=R$. Then
   $K\cap\ker f=R$. Define

   $$L=\ker f\cap\ker c.$$

   Both kernels are normal of finite index. Every finite homomorphism of
   $E$ kills $R$, so $R\le L$. Consequently $L\cap K=R$. Because $L$
   centralizes $K$, $R\le Z(L)$.

4. The image $H_0=\pi(L)$ is normal of finite index in $H$, and
   $\ker(\pi|_L)=R$, so $L/R\cong H_0$. Also
   $\pi^{-1}(H_0)=KL$. Multiplication of indices and the coset bijection
   $K/(K\cap L)\cong KL/L$ give
   $[E:L]=[E:KL][KL:L]=[H:H_0][K:R]$.

5. Section 2 gives $R(L)=R$. Choose a maximal proper subgroup $B$ of
   the nontrivial finite abelian group $R$. The quotient $R/B$ is a
   nontrivial simple abelian group: a nonidentity element generates it,
   and a finite cyclic group is simple exactly when its order is prime.
   Thus $R/B\cong C_p$ for some prime $p$.
   Since $R\le Z(L)$, $B$ is normal in $L$. Applying Section 1 to the
   finite normal subgroup $B$ gives

   $$R(L/B)=R(L)B/B=R/B.$$

   The map $lB\mapsto\pi(l)$ is onto $H_0$ and has exactly this central
   kernel, proving every algebraic assertion.

6. A surjection with finite kernel preserves word-hyperbolicity in both
   directions. For the word-metric reason, choose generators of the total
   group consisting of lifts of a finite symmetric generating set of the
   quotient (and their inverses), together with the finite kernel. Then

   $$d_H(\pi x,\pi y)\le d_E(x,y)\le d_H(\pi x,\pi y)+1.$$

   The second inequality follows by lifting a shortest quotient word and
   correcting the resulting kernel element in one step. This is a
   quasi-isometry; word-hyperbolicity is invariant under quasi-isometry.
   Finite-index subgroups are likewise quasi-isometric to their ambient
   finitely generated groups. Apply these facts to the displayed maps
   and subgroups. $\square$

The passage to $L$ is important. Simply projecting an original finite
abelian kernel onto a prime cyclic quotient can kill its entire invisible
subgroup. At the level of finite abelian groups, the only quotient
$C_4\to C_2$ kills $2C_4$. Step 3 first isolates the actual residual as
the kernel of a cover over $H_0$; Step 5 then quotients that residual.
This illustration does not assert that a hyperbolic extension with the
specified $C_4$ residual data exists.

## 4. Exact scope of the existing cohomology approach

**Corollary.** The following existence statements are equivalent:

1. A word-hyperbolic group $G$ has $1<|R(G)|<\infty$.
2. A residually finite word-hyperbolic group $H$ has a finite-kernel
   extension $E$ which is not residually finite.
3. A residually finite word-hyperbolic group $H_0$ has a central extension
   by $C_p$, for some prime $p$, whose finite residual is precisely $C_p$.
4. A residually finite word-hyperbolic group $H_0$ has a class
   $\alpha\in H^2(H_0;C_p)$, with trivial coefficient action, whose
   restriction to every finite-index subgroup is nonzero.

**Proof.** For (1) implies (2), use $K=R(G)$ and $H=G/R(G)$. Section 2
proves residual finiteness of $H$, and the finite-kernel argument proves
its hyperbolicity. For (2) implies (3), apply the theorem of Section 3.
Statement (3) implies (1) by taking the total group of that extension;
its hyperbolicity follows from the same finite-kernel argument.

For (3) implies (4), let $\alpha$ classify the central extension
$1\to C_p\to J\to H_0\to1$. If its restriction to a finite-index
subgroup $U$ vanished, a section would produce a subgroup $S\le J$
with $S\cap C_p=1$ and
$[J:S]=p[H_0:U]<\infty$. But every finite-index subgroup of $J$
contains $R(J)=C_p$, a contradiction.

For (4) implies (3), form the central extension $J$ classified by
$\alpha$. If $J$ were residually finite, simultaneous separation of the
finitely many nonidentity elements of $C_p$ would give a normal
finite-index subgroup $M\le J$ with $M\cap C_p=1$. The restriction of
the quotient map to $M$ would be an isomorphism onto a finite-index
subgroup of $H_0$, giving a section there and contradicting persistence.
Thus $J$ is not residually finite. Residual finiteness of $H_0$ forces
$R(J)\le C_p$; nontriviality and primality give $R(J)=C_p$. $\square$

Only the usual classification of central extensions by degree-two group
cohomology is used in the last two directions. This is the same input as
the existing classical virtual-splitting criterion.

All four existence statements remain **open** for word-hyperbolic groups.
The corollary identifies what the cohomology approach would produce; it
does not show that an arbitrary hyperbolic counterexample has finite
residual. In particular, ruling out persistent classes would rule out
finite nontrivial residuals, and would still leave a possible infinite
residual untreated.

As a basic positive case, finite and virtually cyclic groups are
residually finite. For the infinite cyclic group, a nonzero integer $n$
is detected modulo any integer $m>|n|$; finite-index heredity then handles
virtually cyclic groups. This settles the elementary hyperbolic groups,
not the unrestricted question.

## 5. Proof-dependency correction

The final paragraph of the existing canonical claim
`finite-residual-transports-across-commensurability` reversed the two
inclusions in its explanation. For an arbitrary subgroup $L\le G$,
restriction of finite homomorphisms gives

$$R(L)\le R(G)\cap L.$$

Finite index is needed for the converse, as proved in Section 2. The
claim's displayed equality and the cited Lean proofs already had the
correct content; the explanatory paragraph has been corrected. No claim
about arbitrary-subgroup heredity is used in Section 3.

## Source and verification boundary

The proofs above are supplied in full. For the standard surrounding facts,
Matthew Stover's [survey, Section 2.1](https://arxiv.org/html/2407.07680v2)
records finite-index invariance, simultaneous finite separation, and the
finite-central-kernel detection criterion. The repository already contains
the classical equivalence
[[finite-central-extension-rf-iff-virtually-splits]] and its proof.

The hyperbolicity steps use only the standard invariance under
quasi-isometry and finite-index passage, already represented by the
repository's hyperbolic transport modules. No new Lean module or
kernel-checking result is asserted here. Cairn validates the dependency
graph; its `ESTABLISHED` status is not a proof-assistant certificate.

Neither the finite-quotient formula nor the central-prime reduction
produces an element of $R(G)$, shows that $R(G)$ is finite for hyperbolic
$G$, or supplies a bound at which a finite-quotient search can safely stop.
In particular, detecting every generator of a presentation is not
detection of every nonidentity word.
