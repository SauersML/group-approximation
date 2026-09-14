# sk-characters-rigidity-b: manuscript proposal (2026-09-13)

Base text: rev1 on main (5b1890ce6c). The theorem and proof below are UNREVIEWED; they are queued with sk-verify-5.

## (a) Change

**Option A (recommended until review passes): no change to the note.** The result lives in Cairn:
- `subshift-elementary-groups-are-character-rigid`, through the route `subshift-elementary-groups-character-rigid-proof`;
- `subshift-elementary-groups-have-trivial-irs`.

**Option B (after a PASS): a short section after the word-problem section.**

```latex
\section{Characters}

\begin{theorem}\label{thm:characters}
Every character of $G_X$ is a convex combination of the trivial character and the
regular character $\delta_e$. So $L(G_X)$ is the only $\mathrm{II}_1$ factor
representation of $G_X$.
\end{theorem}

\begin{proof}
Let $\chi$ be a character, with GNS triple $(\pi,H,\xi)$ and trace
$\tau=\langle\cdot\,\xi,\xi\rangle$ on $M=\pi(G)''$. For a locally finite subgroup
$K$ let $p_K\in M$ be the projection onto the $K$-fixed vectors.

Fix $y\in X$ and clopen sets $B_n\downarrow\{y\}$. Kakutani--Rokhlin partitions with
bases $B_n$, levels generating the topology, and towers made of full towers of the
previous partition give an increasing union $A_y$ of finite-dimensional subrings
$A_n=\bigoplus_C M_{H_C}(\F_2)$, where $H_C$ is the height of the tower over $C$,
spanned by the matrix units $e_{T^aC}u^{a-b}$. As in the proof of simplicity,
$L_n=\GL_3(A_n)\subseteq G$; put $L_y=\bigcup_nL_n$. Suppose $h\in L_m\setminus\{1\}$
is nontrivial on the tower over $C_0$, and every orbit segment of length $L$ meets
$C_0$. Then in each factor $\GL_N(\F_2)$ of $L_n$, $N=3H_C$, the element $h$ is block
diagonal with at least $H_C/L-1$ nontrivial blocks. So its largest eigenspace has
codimension at least $N/(4L)$ once $H_C\ge4L$. Then $|h^{\GL_N(\F_2)}|\ge2^{N^2/(4L)-2}$,
and nontrivial irreducible characters of $\GL_N(\F_2)$ have degree at least
$\lfloor N^2/4\rfloor$. By Larsen and Tiep~\cite[Theorem~A]{LarsenTiep}, their
normalized values at $h$ are at most $\lfloor N^2/4\rfloor^{-c/(8L)}$ once
$N^2\ge16L$. Writing $\chi|_{L_n}$ as a convex combination of normalized irreducible
characters, and using $\min_CH_C\to\infty$, gives
$\chi(h)=\lim_n\tau(p_{L_n})=:c$. So $\chi$ is constant on $L_y\setminus\{1\}$, with
value $c=\chi(e_{12}(e_P))$ for every nonempty clopen $P$.

For $A=e_{12}(\LC(X,\F_2))\subseteq L_y$ we get $p_{L_y}\le p_A$ and
$\tau(p_{L_y})=c=\tau(p_A)$, so $p_{L_y}=p_A$. The same holds at a point $y'\ne y$.
Moreover $G=\langle L_y,L_{y'}\rangle$: once $B_n\cap B'_m=\varnothing$,
$u=ue_{X\setminus T^{-1}B_n}+ue_{T^{-1}B_n}$ has its summands in $A_n$ and $A'_m$,
and similarly for $u^{-1}$. So $p_A$ is central and
$\chi=c+(1-c)\chi_2$, where $\chi_2=\tau((1-p_A)\pi(\cdot))/(1-c)$ vanishes on every
$L_y\setminus\{1\}$.

Let $g\ne1$, and call $V$ small as in the proof of simplicity. The products
$ge_V$ and $e_Vg$ depend only on constants over a small $V$, so if some
$e_{ij}(e_V)$ fails to commute with $g$, the same holds for every clopen subset
of $V$. Choose $K$ such subsets $V_k$ with disjoint towers, noncommuting
$x_k=e_{i_kj_k}(e_{V_k})$, and a point $y$ outside the towers. The element
$g^{-1}x_lx_kg\,x_lx_k$ lies in $H_{V_l}H_{V_k}\setminus\{1\}\subseteq L_y$, so
in the GNS space of $\chi_2$ with cyclic vector $\xi_2$ the vectors
$\pi_2(x_kgx_k^{-1})\xi_2$ are orthonormal, each with inner product
$\overline{\chi_2(g)}$ with $\xi_2$. Bessel's inequality gives $K|\chi_2(g)|^2\le1$.
So $\chi_2=\delta_e$.
\end{proof}
```

Bibliography item:

```latex
\bibitem{LarsenTiep}
M.~Larsen and P.~H. Tiep, \emph{Uniform character bounds for finite classical groups},
\href{https://arxiv.org/abs/2403.09046}{arXiv:2403.09046} (2024).
```

## (b) Proof text
It is given in full in (a). Two notes for the reader of this proposal:
- "orthonormal for `χ_2`" refers to the GNS space of `χ_2`. The text can instead run the Bessel step inside
  `(1−p_A)H`.
- The Theorem also yields `IRS(G_X)` = mixtures of `δ_{1}` and `δ_{G_X}`. That needs the lazy-return principle, so it
  is left out of the note.

## (c) Length
Option B adds about 45 source lines, roughly two thirds of a page, plus 3 bibliography lines.

## (d) Reader trade-off
Stronger: a new theorem, operator-algebraic superrigidity of `G_X`, is proved at about two thirds of a page. The
reader must trust one new import (Larsen–Tiep Theorem A) plus two elementary counting bounds.

## (e) Status
- Unreviewed:
  - `subshift-tower-unit-group-characters-are-constant` (and its `-proof` route);
  - `subshift-elementary-groups-character-rigid-proof`, into the open claim
    `subshift-elementary-groups-are-character-rigid`;
  - `subshift-elementary-groups-have-trivial-irs` (and its `-proof` route).
- Established by literature import: `larsen-tiep-uniform-character-bound`, via its `-citation` route.
