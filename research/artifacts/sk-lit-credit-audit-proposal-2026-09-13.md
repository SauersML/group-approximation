# sk-lit-credit-audit proposal: missing credits in the note (2026-09-13)

- **Subject:** main's `simple_kazhdan_sofic_group.tex` at revision 2 (e80dcf20ad, md5 4ad49212…). Line numbers refer to it.
- **Evidence:** `research/artifacts/sk-lit-credit-audit-2026-09-13.md` (verified data, the sentence table, flags).
- **Status:** citations only. No mathematics changes, and no Cairn nodes. Every bibitem below is checked through Crossref or zbMATH, except the parts marked FLAG.
- **Priority:**
  - P1–P5 recommended: origins of notions and implications the note relies on.
  - P6 recommended for McDuff; Murray–von Neumann is optional.
  - P7 recommended.
- **Total if all adopted:** about +4 text lines, about +45 bibliography lines, and 11 new bibitems.

## P1 (ADD): Kazhdan's property (T), l.64–65
(a) Current:
```latex
Property~\textup{(T)} follows from the theorem of Ershov and
Jaikin-Zapirain~\cite{EJZ}.
```
Replacement:
```latex
Property~\textup{(T)}, introduced by Kazhdan~\cite{Kazhdan}, follows from
the theorem of Ershov and Jaikin-Zapirain~\cite{EJZ}.
```
Bibitem:
```latex
\bibitem{Kazhdan}
D.~A. Kazhdan, \emph{Connection of the dual space of a group with the
structure of its closed subgroups}, Funct. Anal. Appl. \textbf{1} (1967),
63--65. \doi{10.1007/BF01075866}.
```
(c) +0 text lines, +4 bibliography lines. (d) The paper's central property gets its origin at no length cost. (e) Crossref-verified.

## P2 (ADD): origins of "hyperlinear" and "sofic", l.44–46
(a) Current:
```latex
Ozawa stated the hyperlinear form in 2003~\cite[p.~527]{Ozawa}, and
Pestov's Open question~9.1 adds the sofic form~\cite{Pestov}. The groups
below answer all three forms positively.
```
Replacement:
```latex
Ozawa stated the hyperlinear form in 2003~\cite[p.~527]{Ozawa}, and
Pestov's Open question~9.1 adds the sofic form~\cite{Pestov}. Hyperlinear
groups were named by R\u{a}dulescu~\cite{Radulescu}, and sofic groups were
introduced by Gromov~\cite{Gromov} and named by Weiss~\cite{Weiss}. The
groups below answer all three forms positively.
```
Bibitems:
```latex
\bibitem{Gromov}
M.~Gromov, \emph{Endomorphisms of symbolic algebraic varieties},
J. Eur. Math. Soc. \textbf{1} (1999), 109--197.
\doi{10.1007/PL00011162}.

\bibitem{Radulescu}
F.~R\u{a}dulescu, \emph{The von Neumann algebra of the non-residually
finite Baumslag group $\langle a,b\mid ab^3a^{-1}=b^2\rangle$ embeds into
$R^\omega$}, in \emph{Hot topics in operator theory}, Theta Ser. Adv.
Math. \textbf{9}, Theta, Bucharest, 2008, 173--185.
\href{https://arxiv.org/abs/math/0004172}{arXiv:math/0004172}.

\bibitem{Weiss}
B.~Weiss, \emph{Sofic groups and dynamical systems}, Sankhy\={a} Ser. A
\textbf{62} (2000), 350--359.
```
- (c) +2 text lines, +12 bibliography lines.
- (d) The reader learns where the two approximation notions come from. This follows Pestov v8, which says "sofic group was first introduced (without a name of its own)" by Gromov, "coined by Benjy Weiss", and "The expression "hyperlinear group" belongs to Radulescu".
- (e) Gromov: Crossref. Weiss: zbMATH 1148.37302. Rădulescu: zbMATH 1199.46137 confirms pages 173–185 and 2008 only. FLAG: the volume title and series number are recalled; sk-lit-locators should confirm them, or cite arXiv:math/0004172 alone as Pestov does.
- The wording avoids "first": Pestov's own phrasing is "introduced", "coined" and "belongs to".

## P3 (ADD, primary credit): sofic ⇒ hyperlinear, l.164–166
(a) Current:
```latex
LEF groups are
sofic, and sofic groups are hyperlinear~\cite[Example~4.5 and
Theorem~3.3]{Pestov}.
```
Replacement:
```latex
LEF groups are
sofic~\cite[Example~4.5]{Pestov}, and sofic groups are
hyperlinear~\cite[Theorem~2]{ElekSzabo}.
```
Bibitem:
```latex
\bibitem{ElekSzabo}
G.~Elek and E.~Szab\'o, \emph{Hyperlinearity, essentially free actions and
$L^2$-invariants. The sofic property}, Math. Ann. \textbf{332} (2005),
421--441. \doi{10.1007/s00208-005-0640-8}.
```
- (c) +0 text lines, +4 bibliography lines.
- (d) The implication is credited to the theorem that proves it, not only to the survey that states it. [Pestov, Example 4.5] stays for LEF ⇒ sofic: Pestov v8 l.481–484 states it for LEF groups through initial subamenability.
- (e) Crossref. The publisher PDF, p. 423, reads "We shall prove that countable sofic groups are hyperlinear (Theorem 2)"; G_X is countable. Quoted in `pestov91-literature-background-2026-09-13-part2.md` §12.

## P4 (ADD): the space of marked groups, l.162–163
(a) Current:
```latex
So these finite simple groups converge to $G$ in the space of marked
groups, and $G$ is LEF.
```
Replacement:
```latex
So these finite simple groups converge to $G$ in the space of marked
groups~\cite{Grigorchuk,Champetier}, and $G$ is LEF.
```
Bibitems:
```latex
\bibitem{Champetier}
C.~Champetier, \emph{L'espace des groupes de type fini}, Topology
\textbf{39} (2000), 657--680. \doi{10.1016/S0040-9383(98)00063-9}.

\bibitem{Grigorchuk}
R.~I. Grigorchuk, \emph{Degrees of growth of finitely generated groups, and
the theory of invariant means}, Math. USSR-Izv. \textbf{25} (1985),
259--300. \doi{10.1070/IM1985v025n02ABEH001281}.
```
(c) +0 text lines, +7 bibliography lines. (d) The title's notion gets its standard references. (e) Crossref (English translation of Grigorchuk). The Russian original, Izv. 48 (1984), is not checked, so it is not added.

## P5 (ADD, primary credit): property (T) gives expanders, l.163–164
(a) Current:
```latex
Since $\EL_3(F)$ has property~\textup{(T)}, their
Cayley graphs form a family of expanders~\cite{Kassabov}.
```
Replacement:
```latex
Since $\EL_3(F)$ has property~\textup{(T)}, their
Cayley graphs form a family of expanders~\cite{Margulis,Kassabov}.
```
Bibitem:
```latex
\bibitem{Margulis}
G.~A. Margulis, \emph{Explicit construction of concentrators}, Problemy
Peredachi Informatsii \textbf{9} (1973), no.~4, 71--80.
```
- (c) +0 text lines, +3 bibliography lines.
- (d) The implication (T) ⇒ expanders is Margulis's. Kassabov is kept for this family through universal lattices.
- (e) zbMATH 0312.22011, which lists "Explicit construction of a concentrator", PPI 9(4) 71–80, 1973. FLAG: the English translation data (Problems Inform. Transmission 9 (1973) 325–332) is recalled, so it is omitted. The singular "concentrator" in zbMATH should be matched once sk-lit-locators sees the paper.

## P6 (ADD McDuff; OPT Murray–von Neumann): l.170–172
(a) Current:
```latex
So $L(G)$ is a
$\mathrm{II}_1$ factor, and $L(G)\mathbin{\bar\otimes}\mathcal R$ is a
McDuff factor that embeds in $\mathcal R^\omega$ and whose unitary group
contains $G$.
```
Replacement:
```latex
So $L(G)$ is a
$\mathrm{II}_1$ factor~\cite{MurrayvonNeumann}, and
$L(G)\mathbin{\bar\otimes}\mathcal R$ is a McDuff factor~\cite{McDuff}
that embeds in $\mathcal R^\omega$ and whose unitary group contains $G$.
```
Bibitems:
```latex
\bibitem{McDuff}
D.~McDuff, \emph{Central sequences and the hyperfinite factor}, Proc.
London Math. Soc. (3) \textbf{21} (1970), 443--461.
\doi{10.1112/plms/s3-21.3.443}.

\bibitem{MurrayvonNeumann}
F.~J. Murray and J.~von Neumann, \emph{On rings of operators. IV}, Ann. of
Math. (2) \textbf{44} (1943), 716--808. \doi{10.2307/1969107}.
```
- (c) +0 text lines, +8 bibliography lines, or +4 with McDuff only.
- (d) Brown's printed question is phrased through McDuff factors, so the term deserves its source. The ICC ⇒ factor citation is optional, since it is textbook material.
- (e) Crossref. FLAG: the end page 808 of Murray–von Neumann is recalled; Crossref shows only 716.

## P7 (ADD): Sturmian subshifts as rotation codings, l.261–264
(a) Current, l.264:
```latex
$\theta+t\alpha\bmod1\ge1-\alpha$~\cite{MorseHedlund}. So $c(\theta)_t=1$
```
Replacement:
```latex
$\theta+t\alpha\bmod1\ge1-\alpha$~\cite{MorseHedlund,Hedlund},
\cite[Chapter~2]{Lothaire}. So $c(\theta)_t=1$
```
Bibitems:
```latex
\bibitem{Hedlund}
G.~A. Hedlund, \emph{Sturmian minimal sets}, Amer. J. Math. \textbf{66}
(1944), 605--620. \doi{10.2307/2371769}.

\bibitem{Lothaire}
M.~Lothaire, \emph{Algebraic combinatorics on words}, Encyclopedia Math.
Appl. \textbf{90}, Cambridge Univ. Press, Cambridge, 2002.
\doi{10.1017/CBO9781107326019}.
```
- (c) +1 text line, +8 bibliography lines.
- (d) The description of X_α as the closure of rotation codings, and its minimality, is Hedlund's. Lothaire's Chapter 2 gives the arc description used at l.265–268.
- (e) Crossref: the book, and the chapter "Sturmian Words", pp. 45–110, doi:10.1017/cbo9781107326019.003. FLAG: the Hedlund end page 620 and the Lothaire series number 90 are recalled. This supersedes sk-citations P9, which cited only Lothaire.

## Not proposed (reasons in the artifact §3)
- Stepin 1983 (LEF ⟺ marked limit).
- Lubotzky and BdlHV as expander sources.
- Wilson GTM for simplicity of PSL_d(F_2).
- Coven–Hedlund and Morse–Hedlund 1938.
- Kirchberg 1993.

## Ready for revision 3
Verified data for sk-editor-3's §2 (artifact §4):
- Ore 1951, Proc. AMS 2 (1951) 307–314, doi:10.1090/S0002-9939-1951-0040298-4.
- Wilson 1980, Math. Z. 174 (1980) 149–157, doi:10.1007/BF01293535.
- Kionke–Schesler, J. Comb. Algebra (2024), doi:10.4171/jca/103. FLAG: volume and pages.
- Archbold–Spielberg, Proc. Edinburgh Math. Soc. 37 (1994) 119–124, doi:10.1017/S0013091500018733, if "topologically free" is used.
- Milnor, Introduction to Algebraic K-Theory (1972), doi:10.1515/9781400881796, for Whitehead's lemma. FLAG: the locator.
