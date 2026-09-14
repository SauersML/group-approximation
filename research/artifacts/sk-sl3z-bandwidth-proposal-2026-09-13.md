# sk-sl3z-bandwidth: manuscript proposal (§6 format)

**Target text.** Line numbers are from `sk/drafts/rev3.tex` (20:24 assembly), because this remark belongs to rev3's new §2 "LEF groups". The frozen disk copy has no §2.

**Status.**
- Theorem D and its corollary are new Cairn nodes:
  - `subshift-crossed-product-gl-has-no-distorted-elements`;
  - `heisenberg-group-lies-in-no-z-subshift-elementary-group`.
- Both are ESTABLISHED through complete routes, unreviewed, and queued with sk-verify-7.
- They refute the open claim `every-lef-group-embeds-in-a-z-subshift-elementary-group`.

## (a) Current text (rev3.tex l.340–345)
```latex
So $\ell\mapsto\operatorname{diag}(u_\ell,1,1)$ is an injective
homomorphism $L\to\GL_3(R)$ that maps $[L,L]$ into $G$, and
$\Gamma\le[\Delta,\Delta]\le[L,L]$.
\end{proof}

\begin{corollary}
```

## (a, b) Replacement: insert after `\end{proof}` (l.343), before the universal-host corollary
```latex
The groups $G_X$ of Theorem~\ref{thm:main} do not suffice here. Let a
finite symmetric set $S$ generate a subgroup of
$\GL_m(\LC(X,\F_2)\rtimes\Z)$, with entries involving only powers $u^j$,
$|j|\le w$. The ring acts faithfully on
$\bigoplus_{x\in X}\bigoplus_{t\in\Z}\F_2^m$ by
$f\delta_{x,t}=f(T^tx)\delta_{x,t}$ and $u\delta_{x,t}=\delta_{x,t+1}$, and
a word of length $k$ in $S$ moves the index $t$ by at most $wk$. If
$|z^n|_S/n\to0$ and $v$ is supported at one index, the vectors $z^nv$,
$n<N$, span a space of dimension at most $m(2w\max_{n<N}|z^n|_S+1)<N$ for
large $N$. So the minimal polynomials of $z$ on such vectors have bounded
degree, one polynomial over $\F_2$ annihilates $z$, and $z$ has finite
order. In the Heisenberg group $\langle a,b\mid[a,c],[b,c]\rangle$ with
$c=[a,b]$, the element $c$ has infinite order and $c^{n^2}=[a^n,b^n]$. So
this residually finite group, and $\SL_3(\Z)$, which contains it, are
subgroups of no $G_X$. Compare the obstruction of Cyr, Franks, Kra and
Petite for automorphism groups of shifts~\cite{CFKP}.
```
Bibitem (for sk-lit-locators to confirm the journal data):
```latex
\bibitem{CFKP}
V.~Cyr, J.~Franks, B.~Kra, and S.~Petite,
\emph{Distortion and the automorphism group of a shift},
J. Mod. Dyn. \textbf{13} (2018), 147--161.
\href{https://arxiv.org/abs/1611.05913}{arXiv:1611.05913}.
```

## (c) Length
+17 source lines of text and +5 bibliography lines. Dropping the last sentence (the CFKP comparison) and the bibitem saves 7.

## (d) Reader-facing trade-off
- **Gain:** the reader learns that the lamplighter hosts in Corollary `cor:lef` are necessary, and a structural fact about G_X (infinite-order elements are undistorted). The argument is complete in one paragraph, with no new machinery.
- **Cost:** one more paragraph in §2.
- **Trimmed alternative (+6 lines):** state the fact with the Krylov sentence only, and drop the SL_3(Z) clause.

## (e) Checks for the verifier
- The module is a representation, and faithful: coefficients are unique, and the terms A_j u^j δ_{x,0} land in distinct slots.
- The dimension bound uses |z^n| ≤ (τ+ε)n + C, uniformly over one-slot vectors, so N_0 does not depend on v.
- There are finitely many monic polynomials of degree < N_0 over F_2. Their lcm P kills V, hence z by faithfulness. Removing t-factors from P gives a Q with z a unit of the finite ring F_2[t]/(Q).
- For the Heisenberg group, |c^N| ≤ 12√N.
