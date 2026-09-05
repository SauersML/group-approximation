# Non-MF groups without property T: proof audit, stronger matrix bounds, and remaining gap

Research record dated **5 September 2026**.

**Status: the requested existence theorem is not proved in this document.** I did not obtain a complete property-T-free construction. The attached Cairn project already recognizes this as an open strengthening of its non-MF theorem. This document gives complete proofs of the elementary results established or reconstructed in this investigation, a quantitative improvement to its two-selector obstruction, explicit countermodels to several attempted deductions, and the exact remaining implication. It does not label a conditional implication a breakthrough.

The main additional calculation is in §6. Under precisely stated common-carrier and common-gauge hypotheses, the two binary selector rows satisfy

\[
\delta_1^2+\delta_2^2\ge\frac23,
\qquad
\delta_1+\delta_2\ge\sqrt{\frac23},
\qquad
\max(\delta_1,\delta_2)\ge\sqrt{\frac25},
\]

where the defects use the normalized Hilbert–Schmidt norm. These constants are attained by explicit finite-dimensional matrices. In operator norm, at least one of the two defects is **exactly 2**. These strengthen the estimates printed in the inspected Cairn selector node. They do **not** supply its missing group-to-selector construction. No claim of global novelty is made.

## 1. Scope, sources, and verification status

The intended problem is to produce a countable discrete group whose failure of operator-norm MF approximation has a proof independent of property T. Merely taking an existing non-MF group and multiplying it by an infinite cyclic group would preserve the existing proof dependency. It does not meet this request. Nor would changing the meaning of MF to a stronger approximation property meet it.

The supplied archive was inspected locally:

- Filename: `group-approximation-main - 2026-09-04T232307.772.zip`.
- SHA-256: `21ad71e273342c979a7bd6fcda8d40b8680be77d68075e5bd02b877c5bfa870f`.
- ZIP entries: 21,111, including directories; file entries: 21,029.
- Top-level Markdown files under `research/`: 14,055. This is a file count, not a count of proved theorems.

GitHub access identified the repository as [SauersML/group-approximation](https://github.com/SauersML/group-approximation). The `main` commit returned during this investigation was `e9bf60a141aed49af506f24c53028d83824be1f4`. The live versions of the main Leavitt target and the two-selector matrix theorem were also read at that commit. Links below are pinned to it.

The most relevant source nodes were:

| Source | What it actually supplies |
|---|---|
| [Property-T-free manuscript target](https://github.com/SauersML/group-approximation/blob/e9bf60a141aed49af506f24c53028d83824be1f4/research/property-t-free-manuscript-results.md) | An explicitly open replacement program; larger in scope than the user's existence request. |
| [Binary Leavitt full-radical target](https://github.com/SauersML/group-approximation/blob/e9bf60a141aed49af506f24c53028d83824be1f4/research/property-t-free-leavitt-full-mf-radical.md) | The open claim for \(\operatorname{St}_{20}(L_{\mathbb F_2}(1,2))\), with extensive failed-route boundaries. |
| [Whitehead proof audit](https://github.com/SauersML/group-approximation/blob/e9bf60a141aed49af506f24c53028d83824be1f4/research/proposed-property-t-free-whitehead-proof-safe-prefix-audit.md) | A valid prefix of a proposed proof and an explicitly missing native-selector attachment. |
| [Atomic Morita return](https://github.com/SauersML/group-approximation/blob/e9bf60a141aed49af506f24c53028d83824be1f4/research/binary-leavitt-atomic-morita-return.md) | The unproved extraction of three coefficient equations on a prescribed nonzero marked corner. |
| [Atomic corner gap](https://github.com/SauersML/group-approximation/blob/e9bf60a141aed49af506f24c53028d83824be1f4/research/atomic-leavitt-gap-on-nonzero-matrix-corner.md) | An elementary, dimension-independent trace obstruction; reconstructed in §5. |
| [Two-selector rank theorem](https://github.com/SauersML/group-approximation/blob/e9bf60a141aed49af506f24c53028d83824be1f4/research/two-shared-gauge-selector-rows-have-an-affine-rank-obstruction.md) | A conditional matrix obstruction; strengthened in §6. |
| [Native-selector attachment](https://github.com/SauersML/group-approximation/blob/e9bf60a141aed49af506f24c53028d83824be1f4/research/same-center-whitehead-native-selector-subcorner-attachment.md) | The remaining occurrence and carrier identification, explicitly open in the inspected material. |
| [Jacobson head-root target](https://github.com/SauersML/group-approximation/blob/e9bf60a141aed49af506f24c53028d83824be1f4/research/binary-jacobson-steinberg-head-root-is-mf-invisible.md) | A smaller open group-level obstruction; discussed in §9. |

The archived README says the `verified` branch follows a successful full Lean CI run. That is a repository statement, not verification performed here. No Lean build, kernel audit, or proof-assistant certification of this document was performed.

A local invocation of `cairn context property-t-free-leavitt-full-mf-radical` printed the target as open, but also reported graph errors: malformed overlong IDs, invalid `kind` values, missing targets, and unresolved revision-pinned artifacts. Some missing historical artifacts are expected in a ZIP without Git history; other errors concern node metadata. Therefore I do not report a clean graph compilation. Individual claims and proof bodies, rather than a presumed successful global build, ground this audit. The original uploaded ZIP was not edited.

The external primary-source check agrees that a property-T-based existence result is already available: Caleb Eckhardt's [*Non-MF groups and non-finite full group C*-algebras*, arXiv:2608.28772v1](https://arxiv.org/abs/2608.28772v1), submitted 28 August 2026, assumes a property-T subgroup with a proper self-embedding. Its proof of Theorem 4.3 uses property T in the fixed-point and cocycle arguments. This confirms the starting point; it supplies no property-T-free replacement.

“All progress and failed attempts” below means the mathematical work undertaken and audited in this investigation. It does not mean every one of the archive's fourteen thousand research Markdown files was read or reproduced.

## 2. The approximation property and its elementary calculus

### 2.1. Definition

For positive integers \(d_n\), let

\[
\mathcal Q_{\mathbf d}
=\frac{\{(a_n):a_n\in M_{d_n}(\mathbb C),\ \sup_n\|a_n\|<\infty\}}
{\{(a_n):\|a_n\|\longrightarrow0\}}.
\]

Here and throughout, an undecorated norm is the operator norm. The norm of a quotient class is

\[
\|[(a_n)]\|=\limsup_n\|a_n\|.
\]

Indeed, changing a sequence by a norm-null sequence does not change this limsup, and deleting a finite initial segment gives the reverse bound needed for the quotient norm formula.

A countable group \(G\) is **operator-MF** if it admits an injective homomorphism

\[
G\longrightarrow U(\mathcal Q_{\mathbf d})
\]

for some dimension sequence. Equivalently, there are maps
\(u_n:G\to U(d_n)\), with \(u_n(1)=I\), such that

\[
\|u_n(gh)-u_n(g)u_n(h)\|\longrightarrow0
\quad(g,h\in G),
\]

and

\[
\limsup_n\|u_n(g)-I\|>0
\quad(g\ne1).
\]

**Proof of equivalence.** Such maps define a homomorphism into the quotient, and the norm formula makes it injective. Conversely, a unitary quotient element has unitary coordinate lifts. To see this, start with a bounded lift \(a_n\); unitarity gives
\(\|a_n^*a_n-I\|,\|a_na_n^*-I\|\to0\). For large \(n\), replace \(a_n\) by its polar unitary
\(a_n(a_n^*a_n)^{-1/2}\). Functional calculus shows that the replacement changes it by norm tending to zero. Choose arbitrary unitaries at the finitely many exceptional coordinates. Lift each group element this way and lift the identity by \(I\). The quotient relations give asymptotic multiplicativity, and injectivity gives separation. ∎

The normalized Hilbert–Schmidt norm on \(M_d(\mathbb C)\) is

\[
\|a\|_{2,d}=\left(\frac1d\operatorname{Tr}(a^*a)\right)^{1/2}.
\]

It satisfies \(\|a\|_{2,d}\le\|a\|\), but norm separation need not imply normalized Hilbert–Schmidt separation. Section 8 gives explicit examples. We do not replace operator-MF by either hyperlinearity or the stronger assertion that the reduced group C*-algebra is MF.

### 2.2. MF radical

Define

\[
\operatorname{Rad}_{\rm MF}(G)
=\{g\in G:\rho(g)=1\text{ for every }\mathbf d
\text{ and every }\rho:G\to U(\mathcal Q_{\mathbf d})\}.
\]

This is a normal subgroup, since each kernel is normal. Every homomorphism
\(f:G\to H\) satisfies

\[
f(\operatorname{Rad}_{\rm MF}(G))
\subseteq\operatorname{Rad}_{\rm MF}(H).
\]

For if \(x\) belongs to the radical and \(\rho\) is a corona representation of \(H\), then \((\rho\circ f)(x)=1\).

Consequently:

1. A subgroup of an operator-MF group is operator-MF, by restricting an embedding.
2. If a nontrivial element belongs to \(\operatorname{Rad}_{\rm MF}(G)\), then \(G\) is not operator-MF.
3. If an element \(z\) normally generates \(G\), and every corona representation kills \(z\), every such representation is trivial.
4. If \(\operatorname{Rad}_{\rm MF}(G)=G\), every homomorphism from \(G\) to an operator-MF group is trivial: compose with the target's corona embedding.
5. Every corona representation factors uniquely through \(G/\operatorname{Rad}_{\rm MF}(G)\), by the elementary universal property of a quotient.

These assertions use no rigidity theorem. They do not produce the required nontrivial radical element.

## 3. An explicit candidate and a complete normal-generation proof

### 3.1. The coefficient algebra is nonzero and countable

Let

\[
R=\mathbb F_2\langle s_0,s_1,t_0,t_1\mid
t_i s_j=\delta_{ij}1,\quad s_0t_0+s_1t_1=1\rangle.
\]

This is the binary Leavitt algebra. It is countable because its elements are represented by finite sums of finite words over a finite alphabet.

Here is an explicit nonzero representation of the defining ring relations. Let \(X\) be the countable set of infinite binary sequences that are eventually zero, and let \(V\) be the \(\mathbb F_2\)-vector space with basis \(\{e_x:x\in X\}\). Define

\[
S_i e_x=e_{ix},
\qquad
T_i e_{jx}=\begin{cases}e_x&i=j,\\0&i\ne j.\end{cases}
\]

Each sequence has exactly one first digit, so

\[
T_iS_j=\delta_{ij}I,
\qquad S_0T_0+S_1T_1=I.
\]

Thus the presented ring maps unitally into \(\operatorname{End}_{\mathbb F_2}(V)\), and \(1\ne0\) in \(R\). Put

\[
q=s_1t_1.
\]

Its image projects onto sequences beginning with 1, so \(q\ne0\). Direct calculation gives

\[
q^2=q,\qquad qs_1=s_1,\qquad t_1qs_1=1.
\]

### 3.2. The Steinberg group and the marked element

Take

\[
\Delta=\operatorname{St}_{20}(R).
\]

For clarity, this means the group with generators \(x_{ij}(a)\), where \(i\ne j\) and \(a\in R\), subject to

\[
x_{ij}(a)x_{ij}(b)=x_{ij}(a+b),
\]

\[
[x_{ij}(a),x_{jk}(b)]=x_{ik}(ab)
\quad(i,j,k\text{ distinct}),
\]

\[
[x_{ij}(a),x_{kl}(b)]=1
\quad(j\ne k,\ i\ne l),
\]

where \([g,h]=ghg^{-1}h^{-1}\). The elementary matrices \(I+aE_{ij}\) satisfy these relations. There is therefore a homomorphism from \(\Delta\) to \(\operatorname{GL}_{20}(R)\) sending roots to these matrices.

Define

\[
z=x_{13}(q).
\]

Since \(q+q=0\), the additive relation gives \(z^2=1\). Its elementary-matrix image is \(I+qE_{13}\ne I\), so \(z\ne1\). This argument requires no assertion that the entire Steinberg-to-elementary map is injective.

The group is countable. It is also finitely generated: take all roots at the finitely many ordered positions with coefficients in
\(\{1,s_0,s_1,t_0,t_1\}\). Addition of coefficients is realized by multiplication of roots at one position. Products of already available coefficients are realized by the displayed commutator, using any third index. Induction on noncommutative polynomial expressions supplies every root generator. No finite-presentation claim is needed here.

### 3.3. The mark normally generates the entire group

**Theorem.** \(\langle\!\langle z\rangle\!\rangle_\Delta=\Delta\).

**Proof.** Let \(N\) be the normal closure of \(z\). First,

\[
[z,x_{32}(s_1)]
=x_{12}(qs_1)=x_{12}(s_1)\in N.
\]

For every \(a\in R\), a second ordinary Steinberg commutator gives

\[
[x_{41}(a t_1),x_{12}(s_1)]
=x_{42}(a t_1s_1)=x_{42}(a)\in N.
\]

If \(i\notin\{2,4\}\), then

\[
[x_{i4}(1),x_{42}(a)]=x_{i2}(a)\in N.
\]

Together with the already obtained fourth row, this yields \(x_{i2}(a)\in N\) for every \(i\ne2\). If \(i\ne2\) and \(j\notin\{i,2\}\), then

\[
[x_{i2}(a),x_{2j}(1)]=x_{ij}(a)\in N.
\]

Finally, to obtain \(x_{2j}(a)\), choose \(k\notin\{2,j\}\) and use

\[
[x_{2k}(1),x_{kj}(a)]=x_{2j}(a)\in N.
\]

All root generators lie in \(N\). Hence \(N=\Delta\). ∎

This reconstructs the algebraic content of Cairn's [full-idempotent saturation proof](https://github.com/SauersML/group-approximation/blob/e9bf60a141aed49af506f24c53028d83824be1f4/research/full-leavitt-idempotent-defect-saturation-proof.md), without needing Weyl-word calculations or a simplicity theorem.

Thus it suffices to prove the following **still unproved** assertion:

\[
\rho(z)=1
\quad\text{for every }\rho:\Delta\to U(\mathcal Q_{\mathbf d}).
\tag{OPEN-Z}
\]

## 4. A surviving torsion normal generator can be made macroscopic

This section reconstructs the active-carrier argument in Cairn's [torsion normal-generator proof](https://github.com/SauersML/group-approximation/blob/e9bf60a141aed49af506f24c53028d83824be1f4/research/torsion-normal-generator-full-support-proof.md). It is a useful reduction, but it does not prove (OPEN-Z).

### 4.1. Finite-order rounding

Suppose \(A_n\) are unitary and \(\|A_n^m-I\|\to0\), where \(m\ge2\) is fixed. For each eigenvalue of \(A_n\), choose a nearest \(m\)-th root of unity and replace the eigenvalue by that root, retaining an orthonormal eigenbasis. The resulting unitaries \(B_n\) satisfy

\[
B_n^m=I,\qquad \|B_n-A_n\|\to0.
\]

To justify the convergence independently of dimension, let \(D_m\) be the finite set of \(m\)-th roots. For every \(\epsilon>0\), compactness of the unit circle gives

\[
\min\{|\lambda^m-1|:|\lambda|=1,
\operatorname{dist}(\lambda,D_m)\ge\epsilon\}>0
\]

whenever the set is nonempty. Thus a uniformly small power defect forces every eigenvalue uniformly close to \(D_m\).

### 4.2. Active-carrier theorem

**Theorem.** Let \(G\) be finitely generated, and let a finite-order element \(a\ne1\) normally generate \(G\). If a corona homomorphism \(\rho\) retains \(a\), there is an operator-norm asymptotic unitary representation \(\sigma_n:G\to U(k_n)\) and a constant \(c>0\) such that

\[
\|\sigma_n(a)-I\|_{2,k_n}\ge c
\quad\text{for every }n.
\]

**Proof.** Choose a finite generating set \(S\) containing \(a\). For every \(s\in S\), fix an expression

\[
s=\prod_{j=1}^{\ell_s}h_{s,j}a^{\epsilon_{s,j}}h_{s,j}^{-1},
\qquad \epsilon_{s,j}\in\{1,-1\}.
\]

Use the one-term expression for \(a\), and put \(L=\sum_s\ell_s\).

Choose unitary lifts \(U_n(g)\) of \(\rho(g)\), and round \(U_n(a)\) to an exact \(m\)-torsion unitary \(A_n\), where \(a^m=1\). Since \(\rho(a)\ne1\), the rounded matrices are nonidentity on an infinite subsequence. Restrict to that subsequence. Let

\[
E_n=\operatorname{Ran}(A_n-I),\qquad r_n=\dim E_n\ge1.
\]

Replace the generator lifts by

\[
V_n(s)=\prod_{j=1}^{\ell_s}
U_n(h_{s,j})A_n^{\epsilon_{s,j}}U_n(h_{s,j})^*.
\]

For each fixed generator, \(\|V_n(s)-U_n(s)\|\to0\). This follows by telescoping a fixed finite product, using rounding and asymptotic multiplicativity.

Let \(K_n\) be the span of all subspaces \(U_n(h_{s,j})E_n\) occurring in these expressions. Then

\[
E_n\subseteq K_n,\qquad r_n\le k_n:=\dim K_n\le Lr_n.
\]

Each conjugated torsion factor acts as the identity off its own active subspace, which is contained in \(K_n\). It therefore preserves \(K_n\), and so does each \(V_n(s)\). Moreover each \(V_n(s)\) is identity on \(K_n^\perp\).

For each \(g\in G\), choose a fixed representative word in \(S\), choosing the one-letter word for \(a\) and the empty word for the identity. Evaluate it in the \(V_n(s)\), and restrict to \(K_n\), obtaining \(\sigma_n(g)\). A fixed word evaluation differs from the corresponding \(U_n(g)\) by norm tending to zero. For each fixed pair \(g,h\), the relation between their chosen words therefore has defect tending to zero. Restriction to a reducing subspace cannot increase operator norm, so \(\sigma_n\) is an asymptotic representation.

Let

\[
\eta_m=\min\{|\zeta-1|:\zeta^m=1,\ \zeta\ne1\}>0.
\]

Every eigenvalue of \(A_n\) on \(E_n\) has distance at least \(\eta_m\) from 1. Consequently,

\[
\|\sigma_n(a)-I\|_{2,k_n}^2
\ge\eta_m^2\frac{r_n}{k_n}
\ge\frac{\eta_m^2}{L}.
\]

Take \(c=\eta_m/\sqrt L\). ∎

Only a subsequence of the original corona representation is used. We do not assert that every other originally surviving element remains separated after this operation.

### 4.3. Consequence for characters

Call a pointwise limit of normalized traces of operator-norm asymptotic representations an **MF character**. Such a limit is a normalized positive-definite conjugation-invariant function. Indeed, the trace of
\(\sum_{i,j}\overline{c_i}c_j\sigma_n(g_i)^*\sigma_n(g_j)\) is nonnegative, and approximate multiplication identifies its limit with the positive-definiteness expression for the proposed character. Approximate multiplication and trace cyclicity give conjugation invariance.

For a finitely generated group with a finite-order normal generator,

\[
\operatorname{Rad}_{\rm MF}(G)=G
\quad\Longleftrightarrow\quad
\text{every MF character is identically }1.
\]

**Proof.** If every corona representation is trivial, the sequence defining any MF character satisfies \(\|\sigma_n(g)-I\|\to0\) for each \(g\), so its trace limit is 1. Conversely, a nontrivial corona homomorphism retains the normal generator. Apply the active-carrier theorem. By countability and successive subsequence extraction, the normalized traces converge pointwise along a subsequence. Since

\[
\|\sigma_n(a)-I\|_2^2
=2-2\operatorname{Re}\operatorname{tr}_{k_n}(\sigma_n(a)),
\]

the limiting character is not 1 at \(a\). ∎

For the Leavitt group, excluding these nontrivial characters remains an unproved step. Positive marked density alone is not an authentication theorem for other spectral projections or transported coefficient operators.

## 5. The exact finite-corner obstruction

### 5.1. Atomic Leavitt gap, with sharp constant

**Theorem.** Let \(p\ne0\) be an orthogonal projection in \(M_d(\mathbb C)\). For any \(m\ge2\) and any
\(s_i,t_i\in pM_d(\mathbb C)p\),

\[
m-1\le
\sum_{i=1}^m\|t_is_i-p\|
+\left\|\sum_{i=1}^m s_it_i-p\right\|.
\tag{5.1}
\]

Thus at least one of these \(m+1\) defects is at least \((m-1)/(m+1)\). This constant is sharp.

**Proof.** Normalize the ordinary trace on the nonzero corner:

\[
\tau_p(x)=\frac{\operatorname{Tr}(x)}{\operatorname{rank}p}.
\]

It is a tracial state with \(\tau_p(p)=1\) and \(|\tau_p(x)|\le\|x\|\). Set \(b=\sum_i\tau_p(t_is_i)\). Cyclicity gives \(b=\tau_p(\sum_i s_it_i)\), whence

\[
|m-b|\le\sum_i\|t_is_i-p\|,
\qquad
|b-1|\le\left\|\sum_i s_it_i-p\right\|.
\]

The triangle inequality proves (5.1). If all defects are at most \(\epsilon\), then \(m-1\le(m+1)\epsilon\).

For sharpness, on any nonzero corner take

\[
s_i=p,\qquad t_i=\frac{2}{m+1}p
\quad(1\le i\le m).
\]

Every inverse defect and the completeness defect then equal \((m-1)/(m+1)\). ∎

For \(m=2\), the gap is \(1/3\). No off-diagonal relation \(t_is_j=0\) is required. Neither bounded dimension nor a positive lower bound on \(\operatorname{rank}(p)/d\) is required.

### 5.2. Consequence in a norm matrix corona

No nonzero projection in a norm matrix corona supports an exact family satisfying

\[
t_is_i=p\quad(i=0,1),\qquad s_0t_0+s_1t_1=p.
\tag{5.2}
\]

**Proof.** A projection \(p\) has projection lifts \(p_n\). To see this, take a self-adjoint lift \(a_n\). Since \(\|a_n^2-a_n\|\to0\), the eigenvalues approach \(\{0,1\}\) uniformly. Cutting at \(1/2\) gives projections with \(\|p_n-a_n\|\to0\). If \(p\ne0\), the \(p_n\) are nonzero at infinitely many coordinates.

Lift the finitely many purported corner operators by bounded sequences and compress their lifts by \(p_n\). Equations (5.2) say that all three defects tend to zero. Apply (5.1) along the nonzero coordinates to obtain \(1\le o(1)\), a contradiction. ∎

The same proof works in each finite matrix amplification of the corona. It proves the relevant finite-projective obstruction without asserting the existence of a coefficient decoder.

### 5.3. Exact conditional group theorem

Suppose a group \(G\) has a nontrivial involution \(z\). Assume that for every operator-norm asymptotic representation retaining \(z\), one can pass to a subsequence, round the image of \(z\), and construct operators

\[
s_{0,n},s_{1,n},t_{0,n},t_{1,n}
\in p_nM_{d_n}(\mathbb C)p_n,
\qquad p_n=\frac{I-z_n^{\rm round}}2\ne0,
\]

whose two inverse defects and completeness defect tend to zero.

Then every corona representation kills \(z\). If \(z\) normally generates \(G\), its MF radical is all of \(G\).

**Proof.** A surviving corona image gives nonzero rounded negative projections on an infinite subsequence, because an exact nonidentity involution has norm distance 2 from the identity. The assumed construction and (5.1) give \(1\le o(1)\). Thus the image cannot survive. Normal generation completes the last assertion. ∎

For \(G=\Delta\), this hypothesis is precisely the sort of construction requested by Cairn's open atomic-return node. The ring presentation alone does not prove it.

## 6. Stronger and sharp bounds for the two-selector obstruction

The improvement over the inspected Cairn node is to use the squared Hilbert–Schmidt distance between projections, rather than just Cauchy–Schwarz for their trace difference. This section is an unconditional matrix theorem. Its application to \(\Delta\) is conditional on the unproved attachment of actual group-word occurrences to these matrices.

### 6.1. Projection rank mismatch

**Lemma.** For orthogonal projections \(P,Q\in M_d(\mathbb C)\),

\[
|\operatorname{tr}_d(P)-\operatorname{tr}_d(Q)|
\le\|P-Q\|_{2,d}^2.
\tag{6.1}
\]

If their ranks differ, \(\|P-Q\|=1\).

**Proof.** Write \(p=\operatorname{tr}_d(P)\), \(q=\operatorname{tr}_d(Q)\). Since
\(0\le PQP\le P\) and \(0\le QPQ\le Q\), cyclicity gives

\[
0\le\operatorname{tr}_d(PQ)\le\min(p,q).
\]

Therefore

\[
\|P-Q\|_2^2=p+q-2\operatorname{tr}_d(PQ)\ge|p-q|.
\]

If \(\operatorname{rank}P>\operatorname{rank}Q\), the restriction of \(Q\) to \(\operatorname{Ran}P\) has nonzero kernel. For a unit vector \(v\) there, \((P-Q)v=v\). This proves \(\|P-Q\|\ge1\); the reverse inequality follows from \(-I\le P-Q\le I\). Interchange \(P,Q\) for the other rank ordering. ∎

For reflections \(R=I-2P\), \(T=I-2Q\), this gives

\[
\|R-T\|_2^2\ge4|p-q|,
\tag{6.2}
\]

and unequal negative ranks imply \(\|R-T\|=2\).

### 6.2. The common-gauge setup

Let \(H\) and \(M\) be nonzero complex Hilbert spaces of finite dimensions \(n,m\). Let \(V=V^*=V^{-1}\) act on \(M\), and put

\[
\theta=\frac{\operatorname{rank}((I+V)/2)}m.
\]

Let \(F_i\) be projections on \(H\) of normalized ranks \(q_i\), and set

\[
C_i=I-2F_i,\qquad T_i=C_i\otimes V.
\]

Let \(E_i\) be projections on \(H\otimes M\) of normalized ranks \(r_i\), and set \(R_i=I-2E_i\). For arbitrary unitaries \(W_i\) on \(H\otimes M\), define

\[
\delta_i=\|W_iR_iW_i^*-T_i\|_{2,nm}.
\]

The negative spectral fraction of \(T_i\) equals

\[
\Phi_{q_i}(\theta)
=q_i\theta+(1-q_i)(1-\theta)
=1-q_i+(2q_i-1)\theta.
\tag{6.3}
\]

Indeed, on the positive eigenspace of \(V\), the negative eigenspace is \(F_iH\); on the negative eigenspace of \(V\), it is \((I-F_i)H\).

Applying (6.2) to the negative projections gives the stronger inequality

\[
\boxed{\ \delta_i^2\ge4|r_i-\Phi_{q_i}(\theta)|.\ }
\tag{6.4}
\]

Conjugate gauges in place of the identical \(V\) give the same result, since only the positive spectral fraction is used.

### 6.3. The binary rows

Take

\[
(r_1,q_1)=\left(\frac12,\frac14\right),
\qquad
(r_2,q_2)=\left(\frac14,\frac18\right).
\]

Equation (6.4) becomes

\[
\delta_1^2\ge2\left|\theta-\frac12\right|,
\qquad
\delta_2^2\ge3\left|\theta-\frac56\right|.
\tag{6.5}
\]

It follows that

\[
\boxed{\delta_1^2+\delta_2^2\ge\frac23.}
\tag{6.6}
\]

For

\[
2\left|\theta-\frac12\right|
+3\left|\theta-\frac56\right|
\ge2\left(\left|\theta-\frac12\right|
+\left|\theta-\frac56\right|\right)
\ge\frac23.
\]

Also,

\[
\boxed{\delta_1+\delta_2\ge\sqrt{\frac23},}
\tag{6.7}
\]

because \((\delta_1+\delta_2)^2\ge\delta_1^2+\delta_2^2\).

For the maximum, if \(D=\max(\delta_1^2,\delta_2^2)\), then (6.5) implies

\[
\frac13
\le\left|\theta-\frac12\right|+\left|\theta-\frac56\right|
\le\frac D2+\frac D3=\frac{5D}{6}.
\]

Consequently,

\[
\boxed{\max(\delta_1,\delta_2)\ge\sqrt{\frac25}.}
\tag{6.8}
\]

The corresponding figures in the inspected source node were \(1/13\) for the sum of squares, \(1/3\) for the sum, and \(1/5\) for the maximum. Those were correctly described as optimal consequences of its weaker scalar inequalities. Equations (6.6)–(6.8) use additional projection geometry.

### 6.4. Sharpness by explicit diagonal matrices

The stronger constants are optimal for the matrix hypotheses in §6.2, without any further relation between the two source projections.

Choose \(n=8\), let \(F_1\) project onto the first two standard basis vectors of \(H\), and let \(F_2\) project onto the first one. Choose a diagonal \(V\), and write \(Q_i\) for the negative projection of \(T_i\).

**Sharp sum and squared-sum bounds.** Take \(m=6\) and
\(V=\operatorname{diag}(1,1,1,1,1,-1)\). Thus \(\theta=5/6\), and the total dimension is 48. Formula (6.3) gives

\[
\operatorname{rank}Q_1=16,\qquad
\operatorname{rank}Q_2=12.
\]

Choose a diagonal rank-24 projection \(E_1\ge Q_1\), choose \(E_2=Q_2\), and take \(W_1=W_2=I\). Exactly eight diagonal entries differ between the first pair of projections, and none between the second. Therefore

\[
\delta_1^2=4\cdot\frac8{48}=\frac23,
\qquad\delta_2=0.
\]

This attains both (6.6) and (6.7).

**Sharp maximum bound.** Take \(m=10\), with seven positive and three negative entries in \(V\). Then \(\theta=7/10\), total dimension 80, and

\[
\operatorname{rank}Q_1=32,\qquad
\operatorname{rank}Q_2=28.
\]

Choose diagonal projections \(E_1\ge Q_1\) of rank 40 and \(E_2\le Q_2\) of rank 20, again with \(W_i=I\). Each projection pair differs in eight entries, so

\[
\delta_1^2=\delta_2^2=4\cdot\frac8{80}=\frac25.
\]

This attains (6.8). These finite matrices verify sharpness of the standalone matrix theorem; they are not models of the complete Leavitt group presentation.

### 6.5. The maximal operator-norm gap

Put \(\varepsilon_i=\|W_iR_iW_i^*-T_i\|\). If \(\varepsilon_i<2\), the projection rank lemma forces

\[
r_i=\Phi_{q_i}(\theta).
\]

For row one this forces \(\theta=1/2\); for row two it forces \(\theta=5/6\). Both cannot hold. At least one pair of reflections therefore has unequal negative ranks, and for that pair the norm is exactly 2. Thus

\[
\boxed{\max(\varepsilon_1,\varepsilon_2)=2.}
\tag{6.9}
\]

This is the largest possible distance between two unitaries. It applies on any nonzero common carrier, regardless of that carrier's ambient density.

The conclusion does not imply that an actual group relator has defect 2. The row differences in this theorem must first be connected to the actual group-word defects, on the specified common carrier. That is the missing implication.

### 6.6. Approximately shared gauges

Suppose instead the two rows use involutions \(V_1,V_2\) on the same multiplicity space, and there is a unitary \(S\) such that

\[
\epsilon_g=\|V_2-SV_1S^*\|_{2,m}.
\]

Write \(\theta_i=\operatorname{tr}_m((I+V_i)/2)\). Equation (6.1), applied to the positive projections, gives

\[
|\theta_1-\theta_2|\le\frac{\epsilon_g^2}{4}.
\tag{6.10}
\]

The two row inequalities now give

\[
\boxed{
\frac{\delta_1^2}{2}+\frac{\delta_2^2}{3}
+\frac{\epsilon_g^2}{4}\ge\frac13.
}
\tag{6.11}
\]

Indeed, use the triangle inequality along
\(1/2,\theta_1,\theta_2,5/6\), then apply the bounds just proved. Consequently,

\[
\delta_1^2+\delta_2^2
\ge2\left(\frac13-\frac{\epsilon_g^2}{4}\right)_+,
\tag{6.12}
\]

and

\[
\max(\delta_1,\delta_2)^2
\ge\frac65\left(\frac13-\frac{\epsilon_g^2}{4}\right)_+.
\tag{6.13}
\]

Here \(x_+=\max(x,0)\). If gauge comparison is instead in operator norm and
\(\|V_2-SV_1S^*\|<2\), their positive ranks agree exactly. The operator-norm conclusion (6.9) then still holds.

If the common carrier has ambient normalized trace \(\beta\), squared Hilbert–Schmidt norms of operators supported on it scale by \(\beta\). Thus the ambient squared row energy is at least \(2\beta/3-o(1)\) when the gauge discrepancy tends to zero. This inference requires the **same** carrier for the rows and the gauge comparison. A density estimate for some other projection does not supply it.

### 6.7. Reproducible exact arithmetic checks

The following self-contained Python code constructs the diagonal sign lists in §6.4 and checks ranks and squared defects with exact rational arithmetic. The proof is the preceding argument; the calculation is an independent check of the two equality examples.

```python
from fractions import Fraction as F

def targets(m, positive):
    gauge = [1] * positive + [-1] * (m - positive)
    label1 = [-1] * 2 + [1] * 6
    label2 = [-1] + [1] * 7
    return [[a * b for a in label for b in gauge]
            for label in (label1, label2)]

def source(target, negative_rank):
    negative = [i for i, x in enumerate(target) if x == -1]
    positive = [i for i, x in enumerate(target) if x == 1]
    if negative_rank <= len(negative):
        chosen = negative[:negative_rank]
    else:
        chosen = negative + positive[:negative_rank - len(negative)]
    chosen = set(chosen)
    return [-1 if i in chosen else 1 for i in range(len(target))]

def audit(m, positive):
    t1, t2 = targets(m, positive)
    d = 8 * m
    r1, r2 = source(t1, d // 2), source(t2, d // 4)
    energy = [F(sum((a-b)**2 for a, b in zip(r, t)), d)
              for r, t in ((r1, t1), (r2, t2))]
    opnorm = [max(abs(a-b) for a, b in zip(r, t))
              for r, t in ((r1, t1), (r2, t2))]
    ranks = [sum(x == -1 for x in t) for t in (t1, t2)]
    return d, ranks, energy, opnorm

assert audit(6, 5) == (48, [16, 12], [F(2, 3), F(0)], [2, 0])
assert audit(10, 7) == (80, [32, 28], [F(2, 5), F(2, 5)], [2, 2])

# Binary atomic bound: s_i=1, t_i=2/3.
inverse = abs(F(2, 3) - 1)
complete = abs(2 * F(2, 3) - 1)
assert inverse == complete == F(1, 3)
assert 2 * inverse + complete == 1

print(audit(6, 5))
print(audit(10, 7))
print('All exact arithmetic checks passed.')
```

## 7. The missing step has an exact finite-obstruction formulation

It is useful to specify what a completed proof must actually deliver. Finite generation is enough for the following statement; finite presentability is not required.

**Theorem.** Let

\[
G=\langle S\mid\mathcal R\rangle
\]

have a finite generating set \(S\) and at most countably many relators. Let \(w\) be a word whose image \(z\) in \(G\) is an involution. The following are equivalent:

1. Every homomorphism of \(G\) to every norm matrix corona kills \(z\).
2. There are a finite subset \(\mathcal R_0\subseteq\mathcal R\) and \(\epsilon>0\) such that, for every dimension \(d\) and every unitary tuple \(U=(U_s)_{s\in S}\),

   \[
   \max_{r\in\mathcal R_0}\|r(U)-I\|<\epsilon
   \quad\Longrightarrow\quad
   \|w(U)-I\|<1.
   \tag{7.1}
   \]

We take the maximum over an empty relator set to be zero.

**Proof that 1 implies 2.** Enumerate the relators, repeating them if necessary when the list is finite. If 2 fails, for each \(n\) there are a dimension \(d_n\) and a tuple \(U^{(n)}\) such that the first \(n\) relators have defects below \(1/n\), while
\(\|w(U^{(n)})-I\|\ge1\). The generator sequences define a homomorphism from the free group on \(S\) into the corona. Every fixed relator vanishes there, so it factors through \(G\). The norm formula shows that the image of \(w\) has distance at least 1 from the identity, contradicting 1.

**Proof that 2 implies 1.** Lift the images of the finitely many generators of any corona representation to unitary tuples \(U^{(n)}\). The finitely many relator defects in (7.1) tend to zero, so eventually \(\|w(U^{(n)})-I\|<1\). Therefore the quotient norm of \(\rho(z)-1\) is at most 1. But a unitary involution different from the identity has spectrum containing \(-1\), and hence has distance exactly 2 from the identity. Thus \(\rho(z)=1\). ∎

For the finite generating set of \(\Delta\) in §3, a countable presentation can be obtained by including all words that equal the identity. Thus the equivalence applies without a separate finite-presentation theorem.

This gives a concrete completion target: prove an inequality such as (7.1) for a finite, explicitly identified set of ordinary group relators. Neither the atomic gap nor the stronger selector gap specifies that relator set or proves that its defects control the required coefficient rows.

There is a related logical caution. If (7.1) has already been proved, sufficiently accurate models have no nonzero rounded marked corner. A decoder assertion required only when that corner is nonzero then becomes vacuous in that range. Consequently an unspecified existential “atomic-return decoder” is not automatically a weaker theorem than marked MF collapse. Its mathematical value comes from a proved construction or estimate from the actual group relations.

## 8. Explicit countermodels to attempted shortcuts

### 8.1. Rectangular Leavitt maps satisfy all coefficient equations exactly

Let \(V=\mathbb C^r\) and \(W=V\oplus V\), with \(r\ge1\). Let \(s_0,s_1:V\to W\) be the two coordinate inclusions and let \(t_0,t_1:W\to V\) be the coordinate projections. Then

\[
t_is_j=\delta_{ij}I_V,
\qquad
s_0t_0+s_1t_1=I_W.
\]

Every relation is exact. The trace calculation gives
\(\operatorname{Tr}_V(t_is_i)=r\),
\(\operatorname{Tr}_W(s_it_i)=r\), and
\(\operatorname{Tr}_W(I_W)=2r\); there is no contradiction.

The obstruction in §5 requires every operator to belong to **one square corner with one identity**. Identifying \(I_V\) with \(I_W\) would be an additional, false assertion in this example. Equal coefficient names, separate multiplication tables, or separately correct local factorizations do not establish that identification.

The one-branch variant is equally explicit. Take the inclusion \(X:\mathbb C^r\to\mathbb C^{r+1}\) into the first \(r\) coordinates and its adjoint \(Y\). Then

\[
YX=I_r,\qquad I_{r+1}-XY=P_{\rm last}\ne0.
\]

This is why the Jacobson relation discussed in §9 needs a square-coefficient decoder.

### 8.2. Every finite positive-root diagram has an exact finite model

This reconstructs the mechanism of Cairn's [positive-root finite-model theorem](https://github.com/SauersML/group-approximation/blob/e9bf60a141aed49af506f24c53028d83824be1f4/research/finite-positive-root-fragments-have-marked-regular-models.md).

**Theorem.** Let \(A\) be any algebra over a finite field \(\mathbb F_p\). For fixed finite \(n\), the group

\[
U_n^+(A)=\{I+X:X\text{ strictly upper triangular over }A\}
\]

is locally finite.

**Proof.** Choose finitely many generators \(g_1,\dots,g_m\), and write \(X_i=g_i-I\). Let \(B\) be the \(\mathbb F_p\)-span of all products

\[
X_{i_1}\cdots X_{i_k},\qquad1\le k<n.
\]

There are at most \(m+m^2+\cdots+m^{n-1}\) spanning words, so \(B\) is finite as a set. A product of \(n\) strictly upper triangular \(n\)-by-\(n\) matrices vanishes: a potentially nonzero entry would require a strictly increasing chain of \(n+1\) indices among \(n\) choices. This is valid over a noncommutative coefficient algebra.

Thus \(B\) is closed under multiplication and \(B^n=0\). The set \(1+B\) is a group because

\[
(1+b)^{-1}=1-b+b^2-\cdots+(-b)^{n-1}.
\]

It is finite and contains every \(g_i\). ∎

Now take any finite collection of literal positive-root words over the Leavitt algebra and any relations among them that actually hold in \(U_n^+(R)\). Their images generate a finite group \(H\). If the collection contains \(I+qE_{13}\), that element is nonidentity in \(H\). The left regular representation of \(H\) is an exact finite-dimensional unitary model of the entire collection, retaining the mark.

For the involutive mark, left multiplication partitions \(H\) into disjoint pairs. Its regular permutation matrix is a direct sum of two-by-two swaps, so exactly half its eigenvalues are \(-1\), and

\[
\|\lambda_H(z)-I\|=2,
\qquad
\|\lambda_H(z)-I\|_2^2=2.
\]

Thus even a positive-density marked model can satisfy the entire finite positive-root diagram exactly. A vanishing-defect estimate that kills the mark cannot be deduced from such a diagram alone. This countermodel does not satisfy all opposite-root and global relations of \(\Delta\); its scope is the specified positive-root fragment.

### 8.3. Balanced prefix coefficients also have finite models, including opposite roots

This reconstructs Cairn's [degree-zero core theorem](https://github.com/SauersML/group-approximation/blob/e9bf60a141aed49af506f24c53028d83824be1f4/research/degree-zero-leavitt-core-has-locally-finite-marked-models.md).

For a binary word \(u=i_1\cdots i_k\), put

\[
s_u=s_{i_1}\cdots s_{i_k},\qquad
t_u=t_{i_k}\cdots t_{i_1}.
\]

For words \(u,v\) of length \(k\), define \(e_{u,v}=s_ut_v\). Repeated use of \(t_is_j=\delta_{ij}\) gives

\[
e_{u,v}e_{a,b}=\delta_{v,a}e_{u,b},
\qquad
\sum_{|u|=k}e_{u,u}=1.
\]

The second identity follows by iterating \(s_0t_0+s_1t_1=1\). The matrix units are linearly independent: if
\(\sum c_{u,v}s_ut_v=0\), multiply on the left by \(t_a\) and on the right by \(s_b\) to get \(c_{a,b}1=0\). Since \(1\ne0\), every coefficient vanishes.

It follows that

\[
B_k=\operatorname{span}_{\mathbb F_2}\{s_ut_v:|u|=|v|=k\}
\cong M_{2^k}(\mathbb F_2).
\]

For \(|u|=|v|=j<k\),

\[
s_ut_v=\sum_{|w|=k-j}s_{uw}t_{vw},
\]

so \(B_j\subseteq B_k\). Every finite inventory in the union \(\bigcup_kB_k\) lies in one finite matrix ring.

Consequently, a finite inventory of elementary root words with these balanced coefficients, at arbitrary root positions, takes values in the finite group \(\operatorname{GL}_{20}(B_k)\) for some \(k\). Every identity between those words in the elementary group remains true in that finite group. When \(q=s_1t_1\) is included, its elementary root survives. A regular representation again gives an exact marked unitary model.

This rules out a finite obstruction confined to balanced prefix coefficients, even with opposite-root positions and constant Weyl words. It does not rule out relations that use an uncancelled \(s_i\), \(t_i\), other nonzero-degree coefficients, or a genuinely different global construction.

### 8.4. Sparse norm-corona projections do not vanish

Let \(d_n=n\), and let \(p_n\) project onto the first standard basis vector. Then

\[
\|p_n\|=1,\qquad\operatorname{tr}_n(p_n)=\frac1n,
\qquad\|p_n\|_{2,n}=\frac1{\sqrt n}.
\]

Thus \(p=[(p_n)]\) is a nonzero projection of norm 1 in the norm matrix corona, although its normalized traces tend to zero.

For each fixed \(j\ge1\), let \(p_n^{(j)}\) project onto the \(j\)-th basis vector when \(n\ge j\), and choose it arbitrarily at the finitely many earlier coordinates. The quotient projections \(p^{(j)}\) are pairwise orthogonal and unitarily equivalent to \(p\): use the coordinate permutation interchanging 1 and \(j\). For each fixed \(M\), their first \(M\) members sum to a projection below 1.

There is no contradiction with finite dimensionality. The number \(M\) is fixed before the coordinate tends to infinity. This gives arbitrarily many orthogonal copies below the ambient identity, not two copies below the original rank-one projection. In fact, the corner represented by \(p_n\) is a quotient of scalar sequences and cannot support (5.2).

### 8.5. Even normal generation and an infinite orthogonal marked orbit are compatible with MF

The preceding phenomenon can be realized by an actual faithful group representation, as in Cairn's [finitary alternating example](https://github.com/SauersML/group-approximation/blob/e9bf60a141aed49af506f24c53028d83824be1f4/research/infinite-orthogonal-mark-orbit-is-mf-compatible.md).

Let \(A_{\rm fin}\) be the even permutations of the positive integers with finite support, and let

\[
w=(1\ 2)(3\ 4).
\]

For \(g\in A_{\rm fin}\), define \(u_n(g)\) to be its natural permutation matrix on the first \(n\) letters once its support is contained there, and \(I_n\) otherwise. For every fixed pair \(g,h\), these matrices multiply exactly for all sufficiently large \(n\). If \(g\ne1\), it moves a basis vector, so eventually
\(\|u_n(g)-I\|\ge\sqrt2\). Therefore these maps give a faithful norm-corona representation of \(A_{\rm fin}\).

We also verify that \(w\) normally generates the group, without using a simplicity theorem. Its normal closure contains the conjugate
\(w'=(1\ 2)(3\ 5)\): conjugate by the even permutation \((4\ 5)(6\ 7)\). The product
\(ww'=(3\ 4)(3\ 5)\) is a 3-cycle. Every 3-cycle is conjugate to this one by an even finitary permutation, since any unwanted parity in a conjugator can be corrected on two unused letters.

Every even permutation is a product of 3-cycles. To check this directly, write it as an even number of transpositions and pair them. Equal transpositions cancel; two sharing one letter give a 3-cycle; and a disjoint pair satisfies

\[
(a\ b)(c\ d)=(a\ b\ c)(b\ c\ d).
\]

Thus the normal closure is all of \(A_{\rm fin}\).

In the faithful corona representation, \((I-u_n(w))/2\) eventually has rank two. Choose conjugates of \(w\) supported on pairwise disjoint four-letter sets. The corresponding negative spectral projections are pairwise orthogonal, and all are unitarily conjugate through images of group elements. They remain nonzero in the corona.

This disproves the implication

\[
\begin{gathered}
\text{a finite-order normal generator}\\
+\text{infinitely many orthogonal conjugates of its negative projection}
\end{gathered}
\quad\Longrightarrow\quad
\text{MF invisibility}.
\]

The example is not finitely generated, so it does not contradict the active-carrier theorem in §4. Its role is to refute the stated inference from orthogonal packing and normal generation alone.

### 8.6. A group representation is not a coefficient-ring representation

The Steinberg commutator

\[
[x_{ij}(a),x_{jk}(b)]=x_{ik}(ab)
\]

encodes multiplication by a group commutator. It does not assert
\(\rho(x_{ij}(a))=I+\pi(a)E_{ij}\) for a complex-linear coefficient map \(\pi\). An arbitrary unitary representation need not have that form.

A basic type check already excludes a unital ring map from the characteristic-two ring \(R\) to a nonzero complex matrix corner:

\[
0=\pi(1+1)=p+p=2p
\]

would force \(p=0\). Nevertheless groups such as \(\operatorname{GL}_k(\mathbb F_2)\) have nontrivial complex unitary representations, for example their regular representations. Thus complex unitary group representations cannot generally be decoded into unital representations of their characteristic-two coefficient rings.

A proposed decoder must specify what its complex coefficient operators mean and prove the needed equations directly. Treating them as the images of the original ring generators under an automatic ring homomorphism is invalid.

### 8.7. Fixed group-algebra corners cannot contain a Leavitt family

This reconstructs the [group-algebra corner obstruction](https://github.com/SauersML/group-approximation/blob/e9bf60a141aed49af506f24c53028d83824be1f4/research/group-algebra-corners-exclude-traceless-leavitt-inputs.md).

Let \(G\) be any group. On its complex group algebra, define

\[
\tau\left(\sum_g a_g g\right)=a_1.
\]

Then \(\tau(ab)=\tau(ba)\), since the identity coefficient sums over inverse pairs. Also,

\[
\tau(a^*a)=\sum_g|a_g|^2.
\]

The matrix amplification \(\tau_N=\operatorname{Tr}_N\otimes\tau\) is likewise tracial and strictly positive on nonzero elements of the form \(A^*A\).

If \(p=p^*=p^2\ne0\) in \(M_N(\mathbb C[G])\), then
\(\tau_N(p)=\tau_N(p^*p)>0\). Normalize it to obtain a tracial state on the algebraic corner. If that corner contained elements satisfying

\[
t_is_i=p\ (i=0,1),\qquad s_0t_0+s_1t_1=p,
\]

cyclicity would give \(2=1\), a contradiction.

The same trace is obtained from the left regular representation on \(\ell^2(G)\), and extends to its finite matrix von Neumann algebra. Thus the obstruction also applies to any nonzero projection corner there.

It follows that a purported universal, exact construction of a Leavitt family from fixed group-algebra expressions on a marked nonzero algebraic projection would fail in the regular representation of **every** group. A successful finite-matrix-only argument must use the finite-coordinate condition in an essential way. This does not exclude model-dependent spectral constructions; it excludes this fixed algebraic shortcut.

### 8.8. Small relator errors do not automatically permit exactification

Here is a complete elementary instance of the familiar almost-commuting-unitary obstruction. It explains why exact finite-representation arguments cannot simply be applied to approximate representations.

Let \(\omega=e^{2\pi i/n}\), let
\(Ue_j=\omega^j e_j\), and let \(Ve_j=e_{j+1}\), with indices modulo \(n\). Then

\[
UV=\omega VU,
\qquad UVU^*V^*=\omega I,
\qquad\|UV-VU\|=|\omega-1|\to0.
\]

For \(n\ge13\), there are no commuting unitaries \(A,B\) such that

\[
\|A-U\|<\frac1{10},\qquad\|B-V\|<\frac1{10}.
\tag{8.1}
\]

**Proof.** If (8.1) held, use the principal logarithms of the near-identity unitaries \(U^*A\), \(V^*B\) to form unitary paths

\[
U_t=U\exp(t\log(U^*A)),\qquad
V_t=V\exp(t\log(V^*B)),\quad0\le t\le1.
\]

The spectral theorem shows \(\|U_t-U\|<1/10\) and \(\|V_t-V\|<1/10\): each eigenangle moves monotonically along its short arc from 0 to an angle of absolute value below \(\pi\).

Put \(C_t=U_tV_tU_t^*V_t^*\). Telescoping its four unitary factors gives

\[
\|C_t-C_0\|\le2\|U_t-U\|+2\|V_t-V\|<\frac25.
\]

For \(n\ge13\), \(|\omega-1|=2\sin(\pi/n)<1/2\). Therefore
\(\|C_t-I\|<9/10\), so the principal matrix logarithm \(\log C_t\) exists and varies continuously. Since every commutator has determinant 1,

\[
k(t)=\frac{\operatorname{Tr}(\log C_t)}{2\pi i}
\]

is an integer: diagonalize the unitary \(C_t\), use its principal eigenangles, and use that the exponential of their sum is the determinant. It is a continuous integer-valued function, hence constant.

But \(C_0=\omega I\), and \(n>2\), so its principal eigenangle is \(2\pi/n\) and \(k(0)=1\). At \(t=1\), the alleged commutation gives \(C_1=I\) and \(k(1)=0\). Contradiction. ∎

This does not show that the Leavitt or Jacobson presentation has the same instability. It demonstrates why a separate dimension-independent stability or decoding argument is a mathematical obligation, rather than a formal consequence of small relator defects.

## 9. The Jacobson route: exact finite-dimensional collapse, proved without property T

The smaller one-branch algebra is

\[
J=\mathbb F_2\langle S,T\mid TS=1\rangle,
\qquad Q=1-ST.
\]

It has a concrete representation on the vector space with basis \(e_0,e_1,\ldots\): let \(Se_i=e_{i+1}\), let \(Te_0=0\), and let \(Te_{i+1}=e_i\). Then \(TS=I\), while \(Q\) projects onto \(\mathbb F_2e_0\). In particular \(Q\ne0\).

Let

\[
\Gamma_J=\operatorname{St}_5(J),\qquad w_J=x_{13}(Q).
\]

As in §3, the elementary-matrix image proves that \(w_J\) is a nontrivial involution.

### 9.1. Infinite dual coefficient families

The defining relation gives

\[
TQ=T-TST=0,\qquad QS=S-STS=0,\qquad Q^2=Q.
\]

For \(i,j\ge0\), it follows that

\[
QT^iS^jQ=\delta_{ij}Q.
\tag{9.1}
\]

Indeed, when \(i=j\), cancel \(T^iS^i=1\). If \(i>j\), a positive power of \(T\) remains immediately before \(Q\), giving zero. If \(i<j\), a positive power of \(S\) remains immediately after \(Q\), again giving zero.

### 9.2. Every exact finite-dimensional unitary representation kills the head root

**Theorem.** Every homomorphism
\(\pi:\Gamma_J\to U(d)\), with \(d<\infty\), satisfies \(\pi(w_J)=I\).

**Proof.** Consider the infinitely many commuting involutions

\[
A_i=\pi(x_{12}(S^iQ)),\qquad i\ge0.
\]

They commute and square to \(I\) by the additive root relation in characteristic two. A family of commuting self-adjoint matrices in finite dimension is simultaneously diagonalizable. For completeness, diagonalize one matrix; its eigenspaces are invariant under the others. Repeat on a proper invariant eigenspace whenever some remaining matrix is nonscalar there. Dimension decreases at every split, so the process terminates in a common eigenbasis.

In that basis, each \(A_i\) has diagonal entries in \(\{1,-1\}\), so there are at most \(2^d\) possibilities. Choose \(i\ne j\) with \(A_i=A_j\). The kernel of \(\pi\) then contains

\[
x_{12}(S^iQ+S^jQ).
\]

By (9.1), commuting it with \(x_{41}(QT^i)\) yields

\[
[x_{41}(QT^i),x_{12}(S^iQ+S^jQ)]
=x_{42}(Q).
\]

The kernel is normal, so it contains this element. Two constant-coefficient commutators now give

\[
[x_{14}(1),x_{42}(Q)]=x_{12}(Q),
\qquad
[x_{12}(Q),x_{23}(1)]=x_{13}(Q)=w_J.
\]

Thus \(\pi(w_J)=I\). ∎

Every homomorphism to a finite group also kills \(w_J\), because its composition with the faithful regular unitary representation is an exact finite-dimensional unitary representation. This conclusion does not use classification of the finitary kernel, a presentation theorem, or property T.

### 9.3. The same argument makes every exact finite-dimensional representation of the Leavitt group trivial

There is a unital coefficient homomorphism

\[
J\longrightarrow R,\qquad S\longmapsto s_0,
\quad T\longmapsto t_0,
\]

because \(t_0s_0=1\). It sends

\[
Q=1-ST\longmapsto1-s_0t_0=s_1t_1=q.
\]

Sending root generators by the coefficient map and keeping their five indices defines a group homomorphism

\[
\Gamma_J\longrightarrow\Delta
\]

that sends \(w_J\) to \(z\). Checking well-definedness requires only the three defining Steinberg relations; addition and multiplication are preserved by the ring homomorphism. **Injectivity of this map is unnecessary for the argument.**

If \(\pi:\Delta\to U(d)\) is a homomorphism, its restriction along this map kills \(w_J\), so \(\pi(z)=I\). By the normal-generation theorem of §3, \(\pi\) is trivial.

We have therefore proved, without property T:

\[
\boxed{\text{Every finite-dimensional unitary representation of }
\operatorname{St}_{20}(L_{\mathbb F_2}(1,2))\text{ is trivial.}}
\tag{9.2}
\]

This is an exact-representation theorem. It is not the requested non-MF theorem, which concerns asymptotic representations in unbounded dimensions.

### 9.4. Why the proof does not pass automatically to MF approximations

The collision in §9.2 may require indices as large as \(2^d\). In a sequence with \(d=d_n\to\infty\), the resulting \(i_n,j_n\) need not stabilize. Asymptotic multiplicativity controls each **fixed** group word, not a coordinate-dependent family of words whose indices diverge.

Even if one could round the entire commuting root family at each coordinate, the commutator involving \(QT^{i_n}\) would still require a uniform error estimate not supplied by pointwise approximation. Replacing that estimate by the exact group identity is the missing quantifier step.

There is a precise finite-window calibration. Set

\[
a_i=x_{12}(QT^i),\quad b_j=x_{23}(S^jQ),\quad c=x_{13}(Q).
\]

For \(0\le i,j<N\), the Steinberg relations and (9.1) give

\[
[a_i,b_j]=c^{\delta_{ij}},
\]

and all \(a_i\) commute with each other, all \(b_j\) commute with each other, and \(c\) commutes with all of them. Every generator here is an involution.

This finite Heisenberg table has an exact unitary model on
\((\mathbb C^2)^{\otimes N}\). Let

\[
Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\qquad
X=\begin{pmatrix}0&1\\1&0\end{pmatrix}.
\]

Send \(a_i\) to \(Z\) on the \(i\)-th tensor factor, \(b_i\) to \(X\) there, and \(c\) to \(-I\). Operators on different tensor factors commute, while \(ZX=-XZ\), so the entire stated table is exact and the mark survives with operator-norm separation 2. Its dimension is \(2^N\).

Thus arbitrarily large exact finite windows and arbitrarily strong finite-window dimension lower bounds can coexist. This construction models the stated Heisenberg table, not the full Jacobson group.

### 9.5. A conditional route from Jacobson MF collapse to Leavitt MF collapse

If every norm-corona representation of \(\Gamma_J\) killed \(w_J\), restricting any corona representation of \(\Delta\) along the homomorphism above would kill \(z\). Normal generation would give

\[
\operatorname{Rad}_{\rm MF}(\Delta)=\Delta.
\]

This implication is completely proved. Its premise is the [open Jacobson head-root claim](https://github.com/SauersML/group-approximation/blob/e9bf60a141aed49af506f24c53028d83824be1f4/research/binary-jacobson-steinberg-head-root-is-mf-invisible.md), not a consequence of (9.2).

For comparison, in a finite-dimensional **ring** representation, \(TS=1\) immediately implies \(ST=1\), so \(Q=0\). That argument cannot be applied to arbitrary unitary group representations by assuming a coefficient-ring representation; §8.6 explains the type error. The theorem in §9.2 avoids that error for exact finite-dimensional representations, but leaves the growing-index error control unresolved for approximate ones.

## 10. A separate attempted route: uniform conjugacy to powers

Cairn also records a [spectral-recurrence criterion](https://github.com/SauersML/group-approximation/blob/e9bf60a141aed49af506f24c53028d83824be1f4/research/spectral-recurrence-power-return-non-mf-criterion.md). Here is a complete proof and an explicit demonstration of why ordinary conjugacy identities are insufficient.

### 10.1. A valid conditional non-MF criterion

Suppose \(G=\langle S\mid\mathcal R\rangle\) is finitely presented, \(w\) is a word, and there are words \(a_m\) for all positive integers \(m\), together with one constant \(C\), such that **every** finite-dimensional unitary tuple satisfies

\[
\|a_m(U)w(U)a_m(U)^*-w(U)^m\|
\le C\max_{r\in\mathcal R}\|r(U)-I\|
\quad\text{for every }m.
\tag{10.1}
\]

Then every corona representation kills \(w\). In particular, if \(w\ne1\) in \(G\), then \(G\) is not operator-MF.

**Proof.** Fix one matrix tuple and write \(W=w(U)\). For every \(\eta>0\), there is a positive integer \(m\) with \(\|W^m-I\|<\eta\). To prove this, diagonalize \(W\), writing its eigenvalues as \(e^{2\pi i\alpha_j}\), \(1\le j\le d\). Divide the torus \([0,1)^d\) into \(Q^d\) boxes of side \(1/Q\), and place the \(Q^d+1\) points corresponding to \(k\alpha\), \(0\le k\le Q^d\), into them. Two occupy one box. Their positive index difference \(m\) makes every coordinate of \(m\alpha\) within \(1/Q\) of an integer, so \(\|W^m-I\|\le2\pi/Q\). Choose \(Q\) large.

Using that \(a_m(U)\) is unitary and (10.1),

\[
\|W-I\|
=\|a_m(U)Wa_m(U)^*-I\|
\le C\operatorname{Def}_{\mathcal R}(U)+\eta.
\]

Let \(\eta\downarrow0\). This gives
\(\|w(U)-I\|\le C\operatorname{Def}_{\mathcal R}(U)\) for every tuple. Apply it coordinatewise to generator lifts of a corona representation. Their finite relator defect tends to zero, so \(w\) dies. ∎

The hypothesis is uniform in the exponent chosen **after** the finite matrix tuple is frozen. That is its load-bearing content.

### 10.2. Exact conjugacy to every positive power is compatible with MF

Let \(G\) be the group of rational affine transformations

\[
x\longmapsto ax+b,
\qquad a\in\mathbb Q_{>0},\quad b\in\mathbb Q.
\]

This is a countable group under composition. Let \(w(x)=x+1\) and \(a_m(x)=mx\). Then

\[
a_mwa_m^{-1}(x)=x+m=w^m(x)
\]

for every positive integer \(m\), while \(w\ne1\).

Nevertheless \(G\) is operator-MF. We give a direct finite-model proof. For a finite subset \(F\subseteq G\), include any finitely many products one wants to test. Write all coefficients of these affine maps with integer numerators and denominators. Choose a prime \(p\) which avoids:

- all denominators;
- the numerators of the nonzero dilation coefficients;
- the numerator of at least one nonzero coefficient difference for each distinct pair of maps to be separated.

There are only finitely many forbidden nonzero integers, so such a prime exists: otherwise all primes would divide their finite product, contradicting Euclid's infinitude-of-primes argument. Reduction of the coefficients modulo \(p\) gives invertible affine maps of \(\mathbb F_p\). It preserves all the included products, because the rational addition and multiplication formulas reduce correctly, and it distinguishes the specified maps by the choice of prime.

Enumerate \(G\) as \(g_1,g_2,\ldots\), with the identity first. At stage \(n\), perform this construction for the first \(n\) elements and all their pairwise products, ensuring injectivity on that finite set. Represent the resulting finite affine group by its regular permutation representation, and assign the identity outside the selected finite set. For every fixed pair \(g,h\), multiplicativity is eventually exact. For every fixed \(g\ne1\), its image is eventually a nonidentity permutation and has operator-norm distance at least \(\sqrt2\) from the identity. This is an MF approximation.

Thus the equations \(a_mwa_m^{-1}=w^m\) alone do not prove non-MF. They do not supply the dimension-independent bound (10.1), and this example shows that some such bound must fail. No successful construction satisfying the full uniform hypothesis was obtained here.

## 11. Attempt ledger and dependency audit

The following records the routes considered in this investigation. A countermodel to a restricted set of equations is not a countermodel to the full Leavitt group, and a conditional theorem is not an established construction.

| Attempt | Result obtained | Exact reason it does not complete the requested theorem |
|---|---|---|
| Change the final group by adjoining an infinite cyclic factor | Subgroup inheritance preserves non-MF whenever the starting example is non-MF. | The non-MF proof still depends on the starting example. No independent obstruction is produced. |
| Use the existing premise-free Hilbert-hotel endpoint | The inspected [route](https://github.com/SauersML/group-approximation/blob/e9bf60a141aed49af506f24c53028d83824be1f4/research/hilbert-hotel-model-is-unconditionally-non-mf-proof.md) explicitly identifies its Kazhdan compression input. | Premise-free does not mean property-T-free. This route was not used to prove any new non-MF assertion here. |
| Derive Leavitt coefficient operators from root commutators | The coefficient equations and the normal-generation calculation are exact. | A group representation is not automatically a coefficient-ring representation; the claimed square-carrier decoder is missing. |
| Apply the atomic trace obstruction | Complete, sharp proof in §5. | The three coefficient rows on the same prescribed nonzero corner have not been extracted from arbitrary group approximations. |
| Use the two-selector rank contradiction | Improved sharp bounds and equality examples in §6. | The actual native word occurrences have not been shown to supply both required source ranks and target reflections on one carrier with the shared gauge. |
| Reblock the torsion mark to positive density | Complete proof in §4. | Density is information about the marked element; it does not authenticate other coefficient rows or their common target. |
| Add more finite positive-root identities | Every such diagram has an exact finite marked model, §8.2. | This restricted language cannot imply a vanishing-defect collapse estimate. |
| Add balanced prefix matrix units and opposite roots | Every finite coefficient inventory still lies in a finite matrix ring, §8.3. | These finite exact marked models survive; some additional occurrence outside this restricted coefficient inventory is necessary for this route. |
| Pack infinitely many orthogonal marked conjugates | Explicit faithful MF models, §§8.4–8.5. | Outward packing below the ambient identity does not give a two-to-one return inside the original corner. |
| Construct universal fixed group-algebra Leavitt operators | The regular trace rules this out, §8.7. | Such a construction would contradict the regular representation of every group. A finite-coordinate-specific argument is needed. |
| Replace approximate representations by exact finite-dimensional ones | Exact collapse proved in §9; a separate almost-commuting example in §8.8 demonstrates that exactification is not automatic. | No suitable dimension-independent exactification theorem has been proved for the relevant presentation. |
| Use the Jacobson head root | Complete exact finite-dimensional collapse proof and a proved conditional transfer to \(\Delta\), §9. | The collision indices grow with dimension; pointwise approximation does not control the resulting moving words. |
| Use conjugacy to powers and spectral recurrence | Complete uniform criterion and a faithful MF counterexample to the nonuniform shortcut, §10. | No group and nontrivial word satisfying the required uniform error bound have been constructed. |
| Use infinite bounded-exponent groups | The inspected [operator-norm restricted Burnside node](https://github.com/SauersML/group-approximation/blob/e9bf60a141aed49af506f24c53028d83824be1f4/research/operator-norm-restricted-burnside.md) identifies an unproved dimension-independent approximation step. | Rounding powers of individual unitaries does not prove that all multiplication relations survive rounding. This investigation did not establish that additional stability result. |
| Import nonsoficity or a stronger C*-algebra approximation obstruction | No such implication was assumed. | The operator-MF definition in §2 is the target; an obstruction to a different approximation property requires a proved connecting theorem. |

The Whitehead audit deserves a precise scope statement. Its existing construction exposes adjacent swaps with the same label fraction, while the desired argument needs the specified unequal selector rows. Analytically multiplying an operator by a suitable reflection manufactures an operator with a chosen rank profile; it does not prove that this operator is the value of the required ordinary group word. The stronger inequalities in §6 begin **after** this identification and therefore do not repair it.

All proof dependencies in §§2–10 are elementary group relations, finite-dimensional linear algebra, trace cyclicity, compactness, or explicitly stated conditional hypotheses. None of those proofs invokes property T, a Kazhdan projection, a fixed-point theorem derived from property T, or the existing non-MF existence theorem. The existing property-T-based theorem appears only in the provenance audit, not as a premise of a new existence claim.

## 12. Validation and final mathematical status

The exact arithmetic program embedded in §6.7 was executed from this Markdown file. It returned:

```text
(48, [16, 12], [Fraction(2, 3), Fraction(0, 1)], [2, 0])
(80, [32, 28], [Fraction(2, 5), Fraction(2, 5)], [2, 2])
All exact arithmetic checks passed.
```

The archive hash and file counts in §1 were computed directly. The mathematical proofs were checked by tracing their hypotheses and displayed algebraic identities. No numerical experiment was used to extrapolate a theorem about all dimensions. The equality calculations certify their two specific examples; the all-dimensional inequalities are proved symbolically in §6. No Lean certification of this document is claimed.

The completed results include:

1. An explicit countable, finitely generated Leavitt Steinberg group with a proved nontrivial involution normally generating it.
2. A complete property-T-free proof that every exact finite-dimensional unitary representation of that group is trivial.
3. The torsion active-carrier reduction and its MF-character consequence.
4. The sharp atomic corner gap.
5. Stronger, sharp two-selector Hilbert–Schmidt bounds and the maximal operator-norm gap, under explicit matrix hypotheses.
6. A finite-relator characterization of marked corona invisibility.
7. Explicit finite and corona countermodels locating the failures of the attempted shortcuts.
8. A complete conditional transfer from the Jacobson head-root problem and a separate uniform power-recurrence criterion.

**The unfinished assertion is still (OPEN-Z): every norm-corona representation of the Leavitt candidate kills its marked root.** None of the exact finite-dimensional results or matrix inequalities above proves that assertion without the missing uniform decoding or ordinary-relator estimate. In particular, this document does not provide the requested complete property-T-free existence proof, and it does not assert that such a proof is impossible.

A successful continuation needs to prove an actual implication from finitely many specified group-word defects to a marked-collapse estimate such as (7.1), or construct a different group with a complete independent obstruction. Improving the terminal constants, reusing an exact-representation theorem, or assuming the open decoder would not complete that step.


## 13. Continuation and Cairn contributions

The continuation was explicitly authorized to commit directly to `main`.
The inspected starting head was `9d092d6fa6c912e37b5eb49016715d4ce601b685`.
It added two commits after the head recorded in §1, including a precise
Pauli direct-product obstruction. No completed property-T-free existence
route was found in those changes.

The first contribution prepares a refinement of the existing
`two-shared-gauge-selector-rows-have-an-affine-rank-obstruction` claim and
its direct proof, rather than creating a duplicate claim. It adds the sharp
projection-level bounds of §6, the explicit equality examples, and a small
exact-arithmetic verifier. The original weaker inequalities remain valid.
No open group-level claim is promoted to established by this contribution.

The underlying projection identity is elementary; the contribution claims
an explicit sharpening of the inspected Cairn result, not priority for the
projection identity or a solution of the existence problem.

The contribution was checked with `cairn check --changed`. Both the
unchanged baseline and the contribution report the same 81 existing
findings; the contribution introduces no additional findings and no
diagnostic names either modified selector node. The full graph status is
still invalid, so this is not a claim of a clean global graph build.
The exact-arithmetic verifier passed. The live branch was refreshed before
writing to preserve concurrent contributions.
