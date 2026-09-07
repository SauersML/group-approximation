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

## Source and verification boundary

The proofs above are supplied in full. For the standard surrounding facts,
Matthew Stover's [survey, Section 2.1](https://arxiv.org/html/2407.07680v2)
records finite-index invariance, simultaneous finite separation, and the
finite-central-kernel detection criterion. The repository already contains
the classical equivalence
[[finite-central-extension-rf-iff-virtually-splits]] and its proof.

The finite-quotient formula does not produce an element of $R(G)$, does not
show that $R(G)$ is finite for hyperbolic $G$, and supplies no bound at which
a search for separating finite quotients can safely stop. In particular,
detecting every generator of a presentation is not detection of every
nonidentity word.
