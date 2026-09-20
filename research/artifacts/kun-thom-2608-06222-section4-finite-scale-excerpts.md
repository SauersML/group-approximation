# Kun–Thom arXiv:2608.06222v1, Section 4: the lemma statements consumed by the finite-scale centralizer route (verbatim)

Provenance. Excerpts from the LaTeX e-print source of arXiv:2608.06222v1 (G. Kun and
A. Thom, *Nonsofic wreath products of residually finite groups*), file `secondpaper.tex`,
67198 bytes, timestamp 2026-08-06 16:11. That is the same file, byte count and
timestamp as `research/artifacts/kun-thom-2608-06222-section4-ambient-audit.md`. It was
fetched again from `https://arxiv.org/e-print/2608.06222v1` on 2026-09-19. Line numbers
refer to that file. The trust surface is the one already accepted by
`kun-thom-sofic-centralizer-normalization-citation`: an unrefereed preprint, not
kernel-checked.

The companion audit artifact records every sentence of Section 4 that mentions (T), `h_G`
or the ambient partition. This file adds the statements of Lemmas 4.2–4.4 and the parts
of the main proof that `finite-scale-sofic-profiles-kill-compression-defects-proof`
cites by number. The excerpts are copied exactly, apart from the fences.

## K1. Lemma 4.2 (joint cluster scales), lines 765–805

```
\begin{lemma}\label{lem:joint-cluster-scales}
Let $T=\{t_1,\ldots,t_m\}\subseteq P_\Gamma$ be finite.  For each
$1\leq\ell\leq m$ and $s\in S$, fix a word $w_{\ell,s}\in F$ representing
$t_\ell s t_\ell^{-1}\in\Gamma$.  There are sequences
$\varepsilon_n,q_n,r_n\to_{\cU}0$ and subsets
$I_n\subseteq I_n^0$ such that the components indexed by
$I_n^0\setminus I_n$ have total size $o_{\cU}(|Y_n|)$.  Put
$Y_n^{\mathrm{good}}=\bigsqcup_{i\in I_n}Q_{n,i}$.
The following statements hold for components indexed by $I_n$.
[...]
\item Allowed maps modulo the relation $d\leq1/5$ form a finite groupoid
$\mathcal C_n\rightrightarrows I_n$.
[...]
\end{enumerate}
Moreover, the scales can be chosen so slowly that any prescribed finite
family of error sequences converging to zero is $o_{\cU}(\varepsilon_n)$.
In particular, before choosing the scales one may prescribe the total errors
from the component matchings of the full partitions indexed by $I_n^0$ and
from the finitely many label relations associated with the elements of $T$.
\end{lemma}
```

Its proof cites Alekseev–Thom and uses only `sigma|_Gamma` (audit excerpt D).

## K2. Lemma 4.3, first paragraph of the proof, lines 898–917

This is the only place where Lemma 4.3 uses anything beyond `sigma|_Gamma`, the
representatives `u_n` and Lemma 4.2:

```
Before choosing the cluster scale, apply the quantitative component
matching used in the proof of Proposition~\ref{prop:normalization} to the full
partitions $\{u_nQ_{n,i}:i\in I_n^0\}$ and
$\{Q_{n,j}:j\in I_n^0\}$.  Record its total matching error together with
the label discrepancy below, and use the last assertion of
Lemma~\ref{lem:joint-cluster-scales} to choose $\varepsilon_n$ so slowly that
both sequences are $o_{\cU}(\varepsilon_n)$.  Now restrict the matching to
the components indexed by $I_n$.  Since the omitted components have
vanishing total weight and the full matching changes component sizes by a
factor $1+o_{\cU}(1)$, deleting the pairs that meet the omitted family still
removes only component weight $o_{\cU}(1)$.  After a further such deletion in
the source and target, the matching gives a bijection
$\pi_n:D_n\to R_n$ and numbers
$\delta_n\to_{\cU}0$ such that
\[
        |P_{n,i}\mathbin\triangle Q_{n,\pi_n(i)}|
        \leq\delta_n|P_{n,i}|,
        \qquad i\in D_n.
\]
```

## K3. The matching produced in the proof of Proposition 3.1, lines 503–505 and 595–609

```
For $P\in\cP_n$, choose $Q(P)\in\cQ_n$ maximizing
$|P\cap Q(P)|$ and define its loss by
$\ell_n(P)=|P|-|P\cap Q(P)|$.
[...]
For a retained cell, a witness and
\eqref{eq:component-size-ratio} give
$\rho_n^{-1}|P|\leq|Q(P)|\leq\rho_n|P|$.  Since
$|P\mathbin\triangle Q(P)|=|Q(P)|-|P|+2\ell_n(P)$,
the size comparison and the loss bound give
\begin{equation}\label{eq:component-matching}
 |P\mathbin\triangle Q(P)|
 \leq(\rho_n-1+2\eta_n)|P|.
\end{equation}
For $n$ in an $\cU$-large set, $P\cap Q(P)$ contains more than half
of $Q(P)$.  Since distinct transported cells are disjoint, two retained
cells cannot have the same $Q(P)$.  Thus $P\mapsto Q(P)$ is injective
on a family covering all but $o_{\cU}(|Y_n|)$ vertices, and the sum of
the symmetric differences in \eqref{eq:component-matching} is
$o_{\cU}(|Y_n|)$.
```

The size comparison `rho_n` comes from the ambient median argument (lines 563–578). That
comparison is the only ambient input to this matching.

## K4. Lemma 4.4 (one-sided median), statement, lines 1006–1028

```
\begin{lemma}\label{lem:one-sided-median}
For each $t_\ell$ in a fixed finite set which, together with $\Gamma$,
generates $G$, choose representatives $u_{\ell,n}$ of $\sigma(t_\ell)$ and
let $\pi_{\ell,n}:D_{\ell,n}\to R_{\ell,n}$ be the conull
component matching supplied by
Lemma~\ref{lem:relative-cluster-functor}.  Thus, after deleting component
families of vanishing weight,
\[
 \max_{i\in D_{\ell,n}}
 \frac{|u_{\ell,n}Q_{n,i}\mathbin\triangle
              Q_{n,\pi_{\ell,n}(i)}|}{|Q_{n,i}|}
 \to_{\cU}0.
\]
For every $n$, let $f_n:I_n\to(0,\infty)$, and regard $f_n$ as a function on
$Y_n^{\mathrm{good}}$ which is constant on every $Q_{n,i}$, extending it
by the value $1$ on the global exceptional set.  Suppose that, for every
$\ell$, one has, for $i\in D_{\ell,n}$ outside a family of components of
total weight $o_{\cU}(1)$,
$f_n(\pi_{\ell,n}(i))\leq(1+\kappa_n)f_n(i)$, where
$\kappa_n\to_{\cU}0$.  Then, for every $\ell$, the ratio
$f_n(\pi_{\ell,n}(i))/f_n(i)$ converges to $1$ along $\cU$ in
component-weight measure on $D_{\ell,n}$.
\end{lemma}
```

The proof (lines 1030–1101) takes the ambient partition `\mathcal A_n` at line 1031.

## K5. Main proof: the observables and the single use of Lemma 4.4, lines 1121–1123 and 1189–1199

```
For an object $i\in I_n$, let
$o_n(i)=|\operatorname{Orb}_{\mathcal C_n}(i)|$ and
$k_n(i)=|\mathcal C_n(i,i)|$.
[...]
Thus the displayed inequalities
have exactly the exceptional-set form required in
Lemma~\ref{lem:one-sided-median}.

Apply Lemma~\ref{lem:one-sided-median} first to $o_n$ and then to $k_n$.
We obtain, simultaneously for $1\leq\ell\leq m$,
\[
 \frac{o_n(\pi_{\ell,n}(i))}{o_n(i)}\to_{\cU}1,
 \qquad
 \frac{k_n(\pi_{\ell,n}(i))}{k_n(i)}\to_{\cU}1
        \tag{4}\label{eq:cluster-cardinality-concentration}
\]
in component-weight measure.
```

After (4), lines 1201–1361 use (4), Lemmas 4.2 and 4.3, the bisection weight bound (6)
and the compression relation. The audit artifact's mechanical check shows that the main
proof reaches the ambient partition only through the two applications of Lemma 4.4.

## K6. The index step where a drifting centralizer element dies, lines 1266–1272

```
The induced injective isotropy homomorphism has index
$k_n(i)/k_n(\pi(i))$.
By~\eqref{eq:cluster-cardinality-concentration}, this integer is less than
$2$ for $i\in E_n$ and $n$ in an $\cU$-large set.  It is therefore $1$.
Both sides of~\eqref{eq:hom-injection} are torsors over
their source isotropy groups, so~\eqref{eq:hom-injection}
is bijective.
```
