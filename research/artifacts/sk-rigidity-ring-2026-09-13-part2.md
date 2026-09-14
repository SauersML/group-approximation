# sk-rigidity-ring, part 2: verbatim imports

Lane `sk-rigidity-ring`, 2026-09-13. All sources were read from arXiv TeX sources or publisher pages. The TeX was
fetched on MSI into `/scratch.global/sauer354/sk/sk-rigidity-ring/src-<id>/` and grepped there. Line numbers refer to
those files. Primary papers that were NOT opened are marked as such.

## (I1) Giordano–Putnam–Skau, strong orbit equivalence theorem

Secondary source, read: F. Durand and D. Perrin, *Dimension Groups and Dynamical Systems: Substitutions, Bratteli
Diagrams and Cantor Systems*, Cambridge Stud. Adv. Math. 196 (2022), arXiv:2007.15721 (TeX `chapter6.tex`,
§"The Strong Orbit Equivalence Theorem", l.1539–1603).

Definition (l.1560):
> "When $\alpha$ and $\beta$ have at most one point of discontinuity, we say that $(X,T)$ and $(Y,S)$ are
> {\em strongly orbit equivalent} (SOE)."

Here `α, β` are the orbit cocycles of an orbit equivalence `φ: X → Y` (l.1545–1556).

Theorem (l.1571–1603), label `theoremStrongOrbitEquivalence`:
> "\begin{theorem}[Giordano,Putnam,Skau] Let $(X,T)$ and $(X',T')$ be two minimal Cantor dynamical systems. The
> following are equivalent: [...] \item $(X,T)$ and $(X',T')$ are strong orbit equivalent. \item The dimension groups
> $K^0(X,T)$ and $K^0(X',T')$ are isomorphic as unital ordered groups."

Items (1)–(2) of the theorem are Bratteli–Vershik intertwining conditions and are not used here.

Also (l.1564–1566):
> "one can show that if $\alpha$ is continuous then $(X,T)$ is conjugate to $(Y,S)$ or to $(Y,S^{-1})$"

and (l.2282):
> "entropy is far from being invariant by strong orbit equivalence"

Primary: T. Giordano, I. F. Putnam and C. F. Skau, *Topological orbit equivalence and C*-crossed products*, J. reine
angew. Math. 469 (1995), 51–112, doi:10.1515/crll.1995.469.51. NOT opened: the degruyter fetch from MSI returned an
HTML landing page. The Melleray–Robert arXiv:2109.04701 TeX (l.52, l.67) cites GPS Theorems 2.2 and 2.3 for the
measure and ample-group classifications, which confirms the source but not the numbering of the SOE statement.

## (I2) Herman–Putnam–Skau: K^0 of a minimal Cantor system is a simple dimension group

Durand–Perrin, `chapter5.tex` l.832–836, label `theoremDimensionGroup`:
> "\begin{theorem}[Herman, Putnam, Skau] For any minimal Cantor system $(X,T)$, with $T$ a homeomorphism, the ordered
> group $K^0(X,T)$ is a simple dimension group. \end{theorem}"

Durand–Perrin, `chapter4.tex` §"Invariant measures and states" (l.2084–2140): the map
`α_μ(f) = ∫ f dμ` on `H(X,T,Z)` and the theorem with label `propositionKerov`:
> "\begin{theorem} Let $(X,T)$ be a recurrent dynamical system. The map $\mu\mapsto\alpha_\mu$ is a bijection from the
> space of $T$-invariant Borel probability measures on $(X,T)$ onto the set of states of $K^0(X,T)$. \end{theorem}"

Minimal systems are recurrent.

## (I3) Positivity in simple unperforated groups

Durand–Perrin, `chapter3.tex` l.480–490, label `propositionEffros`:
> "shows that, for an unperforated simple ordered group, the order is determined by the set of states.
> \begin{proposition} If $\G=(G,G^+,u)$ is an unperforated simple unital group, then
> $G^+=\{g\in G\mid p(g)>0\mbox{ for every }p\in S(\G)\}\cup \{0\}$. \end{proposition}"

Durand–Perrin notes (l.2101–2105):
> "Proposition~\ref{propositionEffros} is Corollary 4.2 in \citep{Effros1981} (it is stated there for a simple
> dimension group but actually holds in this slightly more general case). The result appears already in
> \cite{EffrosHandelmanShen1980}"

Dimension groups are unperforated, so (I2) and (I3) give: for minimal `(X,T)`, `[f] ∈ K^0(X,T)^+` iff `[f] = 0` or
`∫ f dμ > 0` for every invariant probability measure `μ`.

## (I4) Isomorphism theorems for linear groups without 1/2 (secondary)

E. I. Bunina and P. A. Vladykina, arXiv:2307.12920, TeX `Paper_Bunina_Vladykina.tex` l.88–91:
> "In 1982 Petechuk~\cite{Petechuk1} described automorphisms of the groups ${\GL}_n, {\SL}_n (n \geqslant 4)$ over
> arbitrary commutative rings. If $n = 3$, automorphisms of given linear groups are not always standard. They are
> standard either if in a ring $2$ is invertible, or if a ring is a domain, or it is a semisimple ring."
>
> "Isomorphisms of the groups ${GL}_{n}(R)$ and ${GL}_{m}(S)$ over arbitrary associative rings with $1/2$ for
> $n, m \geqslant 3$ were described in 1981 by I.Z.\,Golubchik and A.V.\,Mikhalev~\cite{Golubchik1} and
> independently by E.I.\,Zelmanov~\cite{Zelmanov}. In 1997 I.Z\, Golubchik~\cite{Golubchik3} described isomorphisms
> between these groups for $n,m \geqslant 4$, but over arbitrary associative rings with~$1$."

Their bibliography (l.700–702, l.735–739):
- "\bibitem{Golubchik1} Golubchik I.Z. \emph{Isomorphisms of the linear general group $\GL_n$, $n \geqslant 4$, over
  an associative ring}. Contemp. Math., 1992, {\bf 131}(1), 123--136."
- "\bibitem{Golubchik3} Golubchik I.Z., Mikhalev A.V. \emph{Isomorphisms of the general linear group over associative
  ring}. Vestnik MSU, ser. math.,1983, {\bf 3}, 61--72.(In Russian)"
- "\bibitem{Petechuk1} Petechuk V.M. \emph{Automorphisms of matrix groups over commutative rings}. Mathematical
  Sbornik, 1983, {\bf 45}, 527--542."
- "\bibitem{Petechuk3} Petechuk V.M. \emph{Automorphisms of groups $\SL_3(R), \GL_3(R)$.} Mathematical Notes, 1982,
  {\bf 31}(5), 657--668."

Caution: the two Golubchik labels appear swapped relative to the text. The `n ≥ 4` arbitrary-ring result matches the
Contemp. Math. 131 title. No primary was opened.

## (I5) Golubchik 1995, abstract

I. Z. Golubchik, *Isomorphisms of projective groups over associative rings*, Fundam. Prikl. Mat. 1:1 (1995), 311–314
(mathnet.ru `fpm49`). Abstract as served by mathnet.ru:
> "Let $R$ be a two-sided order in a regular ring $Q$, $1\in R$, $n\geq3$, $H$ a subgroup of the linear group
> $GL_n(R)$ containing the elementary subgroup $E_n(R)$, $\psi$ an automorphism of the projective group $PH$ which is
> identical on $PE_n(R)$. Then $\psi$ is identical on the group $PH$."

This extends automorphisms from `PE_n` to `PH`. It is not an isomorphism theorem for `E_3`.
