# Additional results

Results proved in this repository that the article *Limits of Matrix
Approximation of Groups in Operator Norm* does not use.  Each item names
the Lean declaration that states it; `#audit_closed_axioms <declaration>`
(defined in `GroupApproximation/Meta/AxiomGuard.lean`) prints the axioms it
depends on.

## Prescribed maximal MF quotients

Let `B` be a countable group with `Rad_MF(B) = B` and `1 ≠ d ∈ B` normally
generating `B`; put `A = ⟨d⟩` and, for a countable group `Q`,
`W_Q = B *_A (Q × A)` with `A` embedded in `Q × A` as the second factor.
Then `π_Q : W_Q → Q` (kill `B`, project the second vertex group) is a split
epimorphism, `Rad_MF(W_Q) = π_Q^{-1}(Rad_MF(Q))`, `W_Q` is not MF, and if
`Q` is MF then `Rad_MF(W_Q) = ker π_Q = ⟨⟨d⟩⟩`.  Precomposition with `π_Q`
is a bijection `Hom(Q, M) → Hom(W_Q, M)` for every MF group `M`.
In particular every countable MF group is the maximal MF quotient of a
non-MF group.

Lean: `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrescribedMFQuotients`
(`Manuscript/OneSidedMFRadical/PrescribedQuotients.lean`),
`…manuscriptUniversalFactorization` (`UniversalFactorization.lean`),
`…manuscriptPrintedFullKernelPullbackParagraph` (`PrintedFullKernelPullback.lean`).

The article's former section on this material, in TeX:

```tex
\section{Pullback formulas for MF radicals}\label{sec:prescribed-quotients}

This section is not used in the proof of Theorem~\ref{thm:recognition}.
It proves that the MF radical pulls back along surjections whose kernel
lies in the radical, and it realizes every countable MF group as the
maximal MF quotient of a non-MF group.

\begin{theorem}[prescribed maximal MF quotients]\label{thm:prescribed-quotients}
Let $B$ be a countable group with $\Rad_{\mathrm{MF}}(B)=B$, and let
$1\ne d\in B$ normally generate $B$.  Put $A=\langle d\rangle$ and, for a
countable group $Q$, define
\[
 W_Q=B*_A(Q\times A),
\]
where $A$ is embedded in $Q\times A$ as the second factor.
Then the map $\pi_Q\colon W_Q\to Q$ which kills $B$ and projects the second
vertex group onto $Q$ is a split epimorphism, and
\[
 \Rad_{\mathrm{MF}}(W_Q)
 =\pi_Q^{-1}\bigl(\Rad_{\mathrm{MF}}(Q)\bigr).
\]
The group $W_Q$ is non-MF.  If $Q$ is MF, then
\[
 \Rad_{\mathrm{MF}}(W_Q)=\ker\pi_Q=\normal{d}_{W_Q}.
\]
Moreover, precomposition with $\pi_Q$ induces a bijection
\[
 \operatorname{Hom}(Q,M)\longrightarrow\operatorname{Hom}(W_Q,M)
\]
for every MF group $M$.
\end{theorem}

We begin with the pullback of the radical along a surjection whose kernel
lies in the radical.

\begin{proposition}[full-kernel pullback]\label{prop:full-kernel-pullback}
Let $f\colon G\to Q$ be a surjective homomorphism of countable groups.  If
$\ker f\le\Rad_{\mathrm{MF}}(G)$, then
\[
 \Rad_{\mathrm{MF}}(G)
 =f^{-1}\!\bigl(\Rad_{\mathrm{MF}}(Q)\bigr).
\]
In particular, the conclusion holds whenever
$\Rad_{\mathrm{MF}}(\ker f)=\ker f$.
More generally, for every normal subgroup $N\trianglelefteq G$,
\[
 \operatorname{cl}_{\mathrm{MF}}^G(N)
 =f^{-1}\!\left(\operatorname{cl}_{\mathrm{MF}}^Q(f(N))\right).
\]
Consequently,
\[
 G/N\text{ is MF}
 \quad\Longleftrightarrow\quad
 \ker f\le N\ \text{ and }\ Q/f(N)\text{ is MF}.
\]
\end{proposition}

\begin{proof}
Every corona homomorphism from $G$ kills $\ker f$ and therefore factors
uniquely through $f$.  Conversely, composing a corona homomorphism from $Q$
with $f$ gives one of $G$.  Intersecting these two corresponding families of
kernels gives the displayed MF radical pullback.  For the stated sufficient
condition,
let \(\pi\colon G\to\U(\mathcal Q_{\mathbf d})\) be any corona homomorphism.
Its restriction to \(\ker f\) is trivial because
\(\Rad_{\mathrm{MF}}(\ker f)=\ker f\).  Hence
\(\ker f\le\Rad_{\mathrm{MF}}(G)\).

The same factorization, restricted to homomorphisms that kill $N$, gives the
closure formula.  If this closure equals $N$, then it contains $\ker f$.
Mapping the equality onto $Q$ shows that
$\operatorname{cl}_{\mathrm{MF}}^Q(f(N))=f(N)$.  Conversely, these two
conditions give
\[
 \operatorname{cl}_{\mathrm{MF}}^G(N)
 =f^{-1}(f(N))=N.
\]
The final equivalence now follows from
Proposition~\ref{prop:mf-residual-calculus}, applied in $G$ and $Q$.
\end{proof}

Thus image under $f$ and inverse image under $f$ give mutually inverse
correspondences, preserving inclusion between the normal subgroups with MF
quotient in $G$ and in $Q$.  The map induced by $f$ on the maximal MF
quotients is an isomorphism:
\[
 G/\Rad_{\mathrm{MF}}(G)
 \cong Q/\Rad_{\mathrm{MF}}(Q).
\]
These correspondences respect composition of surjective homomorphisms whose
kernels lie in the MF radical.

In the setting of Theorem~\\ref{thm:prescribed-quotients}, the trivial
map $B\\to Q$ and the projection $Q\\times A\\to Q$ agree on $A$.  They
therefore define an epimorphism
\[
 \pi_Q\colon W_Q\longrightarrow Q.
\]
It is split by the inclusion $Q\to Q\times A\to W_Q$.  The normal-form
theorem for amalgamated free products shows that both vertex maps of the
amalgam $W_Q$ are injective; in particular, $d\ne1$ in $W_Q$.

\begin{proposition}[universal factorization]\label{prop:universal-factorization}
Let $T$ be a group such that every homomorphism $B\to T$ is trivial.  Then
precomposition with $\pi_Q$ is a bijection
\[
 \operatorname{Hom}(Q,T)\longrightarrow\operatorname{Hom}(W_Q,T).
\]
Furthermore,
\[
 \ker\pi_Q=\normal d_{W_Q}.
\]
\end{proposition}

\begin{proof}
Let $f\colon W_Q\to T$ be a homomorphism.  Its restriction to $B$ is
trivial, so its restriction to the amalgamated subgroup $A$ is trivial.  For
$(q,a)\in Q\times A$, we then have
\[
 f(q,a)=f(q,1)f(1,a)=f(q,1).
\]
Thus the restriction of $f$ to $Q\times A$ factors uniquely through the
projection onto $Q$.  The universal property of the amalgam shows that $f$
factors through $\pi_Q$.  The factorization is unique because $\pi_Q$ is
surjective.

The element $d$ belongs to $\ker\pi_Q$.  Conversely, quotienting $W_Q$ by
$\normal d_{W_Q}$ kills $B$, since $\normal d_B=B$, and kills the $A$-factor
of $Q\times A$.  The resulting quotient is $Q$, with quotient map
induced by $\pi_Q$.  Hence $\ker\pi_Q=\normal d_{W_Q}$.
\end{proof}

\begin{proof}[Proof of Theorem~\ref{thm:prescribed-quotients}]
Every homomorphism from $B$ to an MF group is trivial: compose it with a
faithful corona embedding of the target and use
$\Rad_{\mathrm{MF}}(B)=B$.  Proposition~\ref{prop:universal-factorization}
therefore gives the asserted bijection for every MF group $M$.  In
addition, the definition of $\Rad_{\mathrm{MF}}(B)=B$ says directly that
every homomorphism from $B$ to $\U(\mathcal Q_{\mathbf d})$ is trivial.
Applying Proposition~\ref{prop:universal-factorization} with
$T=\U(\mathcal Q_{\mathbf d})$ shows that every corona homomorphism from
$W_Q$ factors uniquely through $\pi_Q$.  Intersecting their kernels gives
\[
 \Rad_{\mathrm{MF}}(W_Q)
 =\pi_Q^{-1}\bigl(\Rad_{\mathrm{MF}}(Q)\bigr).
\]
The kernel of $\pi_Q$ belongs to this radical, and it contains the
nonidentity element $d$.  Thus $W_Q$ is non-MF.  If $Q$ is MF, its MF radical
is trivial, and the displayed equality becomes
\[
 \Rad_{\mathrm{MF}}(W_Q)=\ker\pi_Q=\normal d_{W_Q}.
\]

\end{proof}

If $N\trianglelefteq W_Q$, the same factorization gives
\begin{equation}\label{eq:closure-pullback}
 \operatorname{cl}_{\mathrm{MF}}^{W_Q}(N)
 =\pi_Q^{-1}\!\left(
   \operatorname{cl}_{\mathrm{MF}}^Q(\pi_Q(N))
  \right).
\end{equation}
Indeed, a homomorphism from $W_Q$ to an MF group kills $N$ exactly when its
unique factor through $Q$ kills $\pi_Q(N)$.  Proposition~\ref{prop:mf-residual-calculus}
and \eqref{eq:closure-pullback} give
\[
 W_Q/N\text{ is MF}
 \quad\Longleftrightarrow\quad
 \ker\pi_Q\le N
 \text{ and }
 Q/\pi_Q(N)\text{ is MF}.
\]
Here, if $\ker\pi_Q\le N$, then
$N=\pi_Q^{-1}(\pi_Q(N))$.

For $Q=\mathbb Z$ and every normal subgroup $N\trianglelefteq W_{\mathbb Z}$,
\begin{equation}\label{eq:one-word-quotient-test}
 W_{\mathbb Z}/N\text{ is MF}
 \quad\Longleftrightarrow\quad
 d\in N.
\end{equation}
Indeed, every quotient of $\mathbb Z$ is MF, while
$\ker\pi_{\mathbb Z}=\normal d_{W_{\mathbb Z}}$.
```

## Soficity of recursively enumerated presentations is Π⁰₂-complete

The set of enumerated presentation codes whose group is sofic is
Π⁰₂-complete and its complement is Σ⁰₂-complete.  The hardness half follows
the construction of Bilanovic–Chubb–Roven (Arch. Math. Logic 59 (2020)
293–312, Theorem 3.1) from a finitely presented nonsofic group; the
nonsoficity of that group is that of the Leavitt unit group of OpenAI's
chapter *Nonsofic groups exist* (Ten advances in mathematics and
theoretical computer science, 2026, Chapter 3), re-proved here from Kun's
expander decomposition (arXiv:1606.04471) and the Kun–Thom criterion
(arXiv:1901.03963).

Lean: `GroupApproximation.SoficEnumeratedPi02.sofic_enum_pi02Complete`,
`…nonsofic_enum_sigma02Complete` (`Computability/SoficEnumeratedPi02.lean`);
the wider ledger is `ArithmeticalLedgerEndpoint.arithmeticalLedgerHolds`.

## A fixed finitely presented group whose MF radical encodes the halting problem

There is one finitely presented non-MF group `U` with a computable family
of words `w_p`, each killed by every homomorphism to a norm matrix corona
and lying in `[Rad_MF(U), U]`, such that `w_p = 1` exactly when the
program `p` halts.  In particular the set of `p` with `w_p = 1` is
undecidable, and no sound computably enumerable proof system proves every
true statement `w_p ≠ 1`.

Lean: `GroupApproximation.FiniteDimensionalApproximationIncomplete.fixed_MF_radical_computer`,
`…closed_core` (`Computability/FiniteDimensionalApproximationIncomplete.lean`,
`Computability/MFRadicalComputer.lean`, `Computability/MFRadicalGodel.lean`).

## A finitely presented, point-norm matricially stable, non-MF group

There is a finitely presented group that is point-norm matricially stable
and not MF, whose MF radical is the normal closure of a single nontrivial
element.  It is an instance of a general invisible-extension construction:
for every countable group `Q` there is `C(Q) ↠ Q` with
`Rad_MF(C(Q)) = π^{-1}(Rad_MF(Q))` and `Hom(Q, M) ≅ Hom(C(Q), M)` for every
MF group `M`.

Lean: `GroupApproximation.InvisibleExtensions.stable_nonMF_invisible_extension_exists`
(`Sofic/InvisibleExtensions.lean`).

## Classical results formalized along the way

* Property (T) for `SL₃(ℤ)` from an exact rational sum-of-squares
  certificate: `GroupApproximation.SL3Certificate.sl3_hasKazhdanPropertyT`.
* The level-three congruence subgroup `Γ(3) ≤ SL₃(ℤ)` is torsion-free,
  finitely presented, and has property (T):
  `GroupApproximation.CongruenceSubgroup.gamma3_torsionFree`,
  `…gamma3_finitelyPresented`, `…gamma3_kazhdan`
  (`Kazhdan/TorsionFreeKazhdanPartner.lean`).
* Shalom's theorem that every finitely generated group with property (T)
  is a quotient of a finitely presented group with property (T):
  `GroupApproximation.Shalom.exists_finitelyPresented_kazhdan_cover`
  (`Kazhdan/ShalomFinitePresentation.lean`; the statement carries its
  hypotheses as binders).
