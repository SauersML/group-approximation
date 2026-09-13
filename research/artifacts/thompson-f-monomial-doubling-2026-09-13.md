# Thompson's F: structural reformulations with a finite core, and exact doubling ratios for P_(2,2)

Lane `solve-f-amenability-structure`, 2026-09-13. The two amenability roots were edited by
another session within six hours, so this lane only adds nodes:
`thompson-f-nonamenable-iff-some-monomial-set-doubles` and
`thompson-f-monomial-doubling-ratio-is-a-finite-computation`. Sources were fetched as arXiv
e-prints on MSI (`~/famstruct/`) and read from the TeX, except where a PDF is named.

## 1. Verbatim pins

**Guba, arXiv:2305.07113v4, `jgcc-template.tex`.**
- *l.551:* "Cardinality arguments based on the F\o{}lner criterion show that for amenable group $G$, this system always has a nonzero solution."
- *Lemma `gig`, l.615:* "For any $g_1,...,g_n\in F$ there exists $g\in F$ such that $g_1g,\ldots,g_ng\in M$."
- *Definition, just before l.632:* "This set consists of all elements in the monoid $M$ with normal forms $x_{i_1}\ldots x_{i_d}$, where $i_1\le\cdots\le i_d$ and $i_1\le m$, $i_2\le m+1$, ... , $i_d\le m+d-1$."
- *l.632:* "{\bf Problem} ${\mathcal P}_{d,m}$: {\sl Given two elements $a,b\in K[{\mathcal S}_{m+1,m+d+1}]$, find a nonzero solution of the equation $au=bv$, where $u,v\in K[M]$, or prove that it does not exist.}"
- *Theorem `xmy`, l.645:*
  - "a) For any $m\ge1$, the set of elements $X_m=\{x_0,x_1,...,x_m\}$ is not doubling, that is, there exists a finite subset $Y\subset M$ such that $|X_mY| < 2|Y|$."
  - "b) If $a,b\in K[M]$ are linear combinations of monomials $x_0$, $x_1$, ... , $x_m$ of degree $1$, then the equation $au=bv$ in $k[M]$ has a nonzero solution, where $\deg u=\deg v\le\frac{m(m+1)}2$."
- *Theorem `s24`, l.654 (`P_(2,1)`):* "... has a nonzero solution, where $\deg u,v\le41$."
- *l.663–665:* "The cases that come after that are already unknown. This is $d=2$, $m=2$, where $a$, $b$ are linear combinations of 9 monomials of degree 2: $x_0^2,\, x_0x_1,\, x_0x_2,\, x_0x_3,\, x_1^2,\, x_1x_2,\, x_1x_3,\, x_2^2,\, x_2x_3.$"
- *l.716:* "Donnelly shows in~\cite{Don14} that $F$ is non-amenable if and only if there exists $\varepsilon > 0$ such that for any finite set $Y\subset F$, one has $|AY|\ge(1+\varepsilon)|Y|$, where $A=\{x_0,x_1,x_2\}$". Donnelly's paper itself was not read.
- *Juschenko:* the survey TeX has no hit for "Juschenko". No separate combinatorial criterion by Juschenko was found; the Bleak–Juschenko criterion below is the one located.

**Guba, arXiv:2101.01848 (`grringf.tex`), the source of Theorem `s24`.**
- *l.392:* "... has a nonzero solution with the property $\deg u,v\le41$."
- *l.395:* "Notice that we do not know what is the minimum degree of $u$, $v$ for solutions of this equation. A rough computer search can show that $n > 10$, but we do not even know whether the minimum value of $n$ is close to $10$ or $40$." Here `Y ⊆ S_(4,n)` consists of monomials of degree `n - 4`.
- *l.370:* the construction is Donnelly's, and "What is called {\em ruinous} in Donnelly's paper, is called {\em doubling} in our terminilogy."

**Moore, arXiv:1106.4735, `Hind_Ellis_F.tex`.**
- *l.308:* "Define $\Tbb_n$ to be all elements of $\Tbb$ of cardinality $n$. These correspond to the ways to associate a sum of $n$ ones." Also: "Let $\Abb_n$ denote the collection of all probability measures on $\Tbb_n$."
- *l.862–866:* "An embedding of $\Tbb_m$ into $\Abb_n$ is a convex combination of embeddings of $\Tbb_m$ into $\Tbb_n$. The range of such an embedding is a \emph{copy of $\Tbb_m$ in $\Abb_n$}."
- *l.868–887,* citing Moore, *Amenability and Ramsey theory*, Fund. Math. 220(3) (2013) 263–280: "The following are equivalent: (1) Thompson's group $F$ is amenable. (2) For every $m$ there is an $n$ such that if $c:\Tbb_n \to [0,1]$, then there is a copy $\Xbb$ of $\Tbb_m$ in $\Abb_n$ such that $|c(\nu) - c(\nu')| \leq 1/2$ whenever $\nu,\nu' \in \Xbb$. (3) For every $m$ there is an $n$ such that if $c:\Tbb_n \to \{0,1\}$, then there is a copy $\Xbb$ of $\Tbb_m$ in $\Abb_n$ such that $c$ is constant on $\Xbb$."
- *Question, l.1338–1343:* "For which specific values of $m$ can one prove that there is an $n$ such that if $c:\Tbb_n \to \{0,1\}$ then there is a copy of $\Tbb_m$ in $\Abb_n$ on which $c$ is constant? What bounds (upper or lower) can be proved on $n$ for a given value of $m$?"
- *Conjectures and theorem:* Conjecture `NA_Hindman` (l.350), Conjecture `NA_Ellis` (l.381, idempotent measures in compact convex subsystems), and Theorem `Ellis_to_Hindman` (l.774: "Conjecture \ref{NA_Ellis} implies Conjecture \ref{NA_Hindman}.").

**Moore, arXiv:1807.05469, `no_idempotent.tex`.**
- *l.43–48:* "Free binary systems are shown to not admit idempotent means. This refutes a conjecture of the author. It is also shown that the extension of Hindman's theorem to nonassociative binary systems formulated and conjectured by the author is false."
- *l.92–97:* "I previously (and incorrectly) claimed to have proved the existence of an idempotent mean on a free binary system \cite{amen_F}. ... The question of \(F\)'s amenability remains open." Here `amen_F` is "ArXiv preprint 1209.2063, unpublished note". That e-print and PDF request returned HTML on MSI and was not read.
- **Consequence for the graph:** Moore's Ellis-lemma route and his nonassociative Hindman conjecture are refuted by their author. Only the finitary Ramsey equivalence (items 2 and 3 above) survives as a reformulation.

**Haagerup, Haagerup, Ramirez-Solano, arXiv:1705.00198, `ThompsonT.tex`, abstract l.138–149.**
- "... $\sqrt2+\sqrt3 < \frac1{\sqrt{12}}||(I+C+C^2)(I+D+D^2+D^3)|| \le 2+\sqrt2$. Moreover, the upper bound is attained if the Thompson group $F$ is amenable."
- "Our extensive numerical computations suggest that $\frac{1}{\sqrt{12}}||(I+C+C^2)(I+D+D^2+D^3)||\approx 3.28$, and thus that $F$ might be non-amenable. However, we can in no way rule out that ... $=\, 2+\sqrt2$."

**Bleak–Juschenko, *Ideal structure of the C*-algebra of Thompson group T*.**
- *Source:* PDF from web.ma.utexas.edu/users/juschenko, dated December 2, 2014, md5 `792f9a21dae2ae63453a81f54d417869`.
- *Theorem 1, p.2:* "Thompson's group $F$ is non-amenable if and only if there exists a finite set $H$ which can be decomposed as disjoint union of sets $H_1$ and $H_2$ with $\sum_{g\in H_1}\pi(g)=\sum_{h\in H_2}\pi(h)$ and such that the closed ideal generated by $\sum_{g\in H_1}\lambda(g)-\sum_{h\in H_2}\lambda(h)$ coincides with $C^*_\lambda(T)$."

## 2. Which reformulations have a finite checkable core

| Reformulation | Finite object | What a finite certificate proves | What would prove non-amenability |
|---|---|---|---|
| Moore's Ramsey (3) | for fixed `m, n`: all `2^{Catalan(n)}` colourings of `T_n` | the per-`m` statement, i.e. Moore's Question for that `m` | one `m` failing for **every** `n`, which is not finite |
| Cardinality for `P_(d,m)` (this lane) | finite `Y ⊆ M_D` with `|S Y| < 2|Y|` | `P_(d,m)` solvable over every field | `S_(m+1,m+d+1)` doubling for **all** finite `Y` (equivalent to non-amenability, by the new claim) |
| Ore pair (Kielak) | a candidate pair `a, b` | nothing finite: every `u, v` must be excluded | an invariant ruling out all common multiples |
| Evacuation capacity `C` | a finite subgraph of density `> 4 - 1/C` | that capacity `C` fails (`thompson-f-evacuation-schemes-need-capacity-three`) | a scheme for all finite fragments, which is not finite |
| HHR norm on `C T` | exact moments | lower bounds on the norm | the norm strictly below `2+√2`: an upper bound, which moment data cannot give |
| Bleak–Juschenko | an explicit `H_1, H_2` | nothing finite: the ideal generated must be the whole algebra | a proof of that for one `H` |

In each row a finite object certifies either an amenability-side sub-statement or the
failure of one fixed non-amenability parameter. For the `P_(d,m)` row this is intrinsic:
item 2 of `thompson-f-nonamenable-iff-some-monomial-set-doubles` makes non-amenability
equivalent to a statement over all finite `Y`.

## 3. Exact doubling ratios

**Program.** `experiments/thompson-f/doubling_flow.cpp`.
- For `U = M_(D,L)` it builds the network `source -K-> y -∞-> s y -J-> sink`.
- Minimum cuts give `max_Y (K|Y| - J|S Y|)`, and Dinkelbach iteration gives the exact minimum
  of `|S Y| / |Y|`.
- By `thompson-f-monomial-doubling-ratio-is-a-finite-computation`, `U = M_(D, R_S(D))` gives
  `Λ_S(D)` exactly.

**Checks** (`experiments/thompson-f/doubling_check.py`, on MSI):
- exhaustive subset search agrees on every universe with at most 15 elements;
- `λ*(D, L)` is constant for `R_S(D) <= L <= R_S(D)+4` and `D <= 6`, for `X_1, X_2, S_(2,4), S_(3,5)`;
- `λ*(D, R_S(D) - 1) = Λ_S(D-1)` in every checked case.

**Identity.** `S_(m+1,m+d+1) = X_m X_(m+1) ... X_(m+d-1)` as sets, checked for `m <= 4, d <= 5`.
So `S_(2,4) = X_1 X_2` and `S_(3,5) = X_2 X_3`.

**`Λ_S(D)` (exact).** `R = R_S(D)`: `D+2` for `X_2` and `S_(2,4)`, `D+3` for `S_(3,5)`.

| D | `X_1` | `X_2` | `S_(2,4)` (`P_(2,1)`) | `S_(3,5)` (`P_(2,2)`) | `|M_(D,D+3)|` |
|---|---|---|---|---|---|
| 1 | 3/2 | 9/4 | 7/2 | 28/5 | 5 |
| 2 | 4/3 | 2 | 3 | 9/2 | 21 |
| 3 | 5/4 | 31/17 = 1.8235 | 45/17 = 2.6471 | 277/70 = 3.9571 | 84 |
| 4 | 6/5 | 185/107 = 1.7290 | 263/107 = 2.4579 | 835/231 = 3.6147 | 330 |
| 5 | 7/6 | 571/342 = 1.6696 | 400/171 = 2.3392 | 2816/835 = 3.3725 | 1287 |
| 6 | 8/7 | 704/435 = 1.6184 | 973/435 = 2.2368 | 4178/1307 = 3.1966 | 5005 |
| 7 | — | 2150/1359 = 1.5821 | 2941/1359 = 2.1641 | 7501/2447 = 3.0654 | 19448 |

**Degrees 6–12** (array job 713721, `U = M_(D, R_S(D))`, one core each; seconds = wall time of the
whole Dinkelbach loop). `S_(4,7)` is the fourteen-monomial set of `P_(3,1)`.

| set | D | L = R_S(D) | `|U|` | `Λ_S(D)` exact | decimal | seconds |
|---|---|---|---|---|---|---|
| `S_(2,4)` | 8 | 10 | 43758 | 4737/2245 | 2.110022 | 2.4 |
| `S_(2,4)` | 9 | 11 | 167960 | 7929/3850 | 2.059481 | 9.4 |
| `S_(2,4)` | 10 | 12 | 646646 | 74419/36845 | 2.019786 | 40.5 |
| `S_(2,4)` | 11 | 13 | 2496144 | 159074/80215 | **1.983095** | 175.3 |
| `S_(2,4)` | 12 | 14 | 9657700 | 1081546/555319 | 1.947612 | 753.6 |
| `S_(3,5)` | 8 | 11 | 75582 | 22469/7610 | 2.952562 | 3.1 |
| `S_(3,5)` | 9 | 12 | 293930 | 17279/6039 | 2.861235 | 15.7 |
| `S_(3,5)` | 10 | 13 | 1144066 | 481721/172855 | 2.786850 | 117.4 |
| `S_(3,5)` | 11 | 14 | 4457400 | 3305029/1213918 | 2.722613 | 494.1 |
| `S_(3,5)` | 12 | 15 | 17383860 | 3456957/1295921 | 2.667568 | 1838.4 |
| `X_2` | 8 | 10 | 43758 | 3491/2245 | 1.555011 | 0.7 |
| `X_2` | 9 | 11 | 167960 | 11779/7700 | 1.529740 | 6.9 |
| `X_2` | 10 | 12 | 646646 | 55632/36845 | 1.509893 | 25.5 |
| `X_2` | 11 | 13 | 2496144 | 12224/8187 | **1.493099** | 103.9 |
| `X_2` | 12 | 14 | 9657700 | 459707/310984 | 1.478234 | 702.0 |
| `X_3` | 6 | 9 | 5005 | 2641/1370 | 1.927737 | 0.1 |
| `X_3` | 8 | 11 | 75582 | 7791/4253 | 1.831883 | 1.7 |
| `X_3` | 10 | 13 | 1144066 | 364308/205867 | 1.769628 | 57.3 |
| `X_3` | 11 | 14 | 4457400 | 2185067/1251854 | 1.745465 | 308.2 |
| `S_(4,7)` | 6 | 9 | 5005 | 5822/1307 | 4.454476 | 0.2 |
| `S_(4,7)` | 8 | 11 | 75582 | 2749/676 | 4.066568 | 6.5 |
| `S_(4,7)` | 10 | 13 | 1144066 | 572848/150847 | 3.797543 | 189.3 |
| `S_(4,7)` | 11 | 14 | 4457400 | 4173963/1130002 | 3.693766 | 694.1 |

**Firsts:**
- `S_(2,4)` first drops below `2` at `D = 11`, and `X_2` below `3/2` at `D = 11`. Both certificates are recorded in `thompson-f-p21-cardinality-certificate-in-degree-eleven`. For the cardinality method, this answers Guba's "close to $10$ or $40$" remark (l.395 above): `11`.
- `S_(3,5)` (`P_(2,2)`) has no certificate for `D <= 12`. The minimum at `D = 12` is `2.6676`.

**Consistency with the survey.** `X_2` first drops below `2` at `D = 3 = m(m+1)/2`, as Theorem
`xmy`(b) predicts for `m = 2`. `S_(2,4)` first has a cardinality
certificate at degree `11`. Theorem `s24` records `deg u, v <= 41`.

**Shape of optimal sets** (analysis script on the `CERT_ALL` output, `D <= 7`):
- For `D >= 3`, neither the optimal set nor its complement is closed under raising or lowering
  one letter.
- The optimal sets for `X_2` and `S_(2,4)` have the same size and the same first- and
  last-letter statistics in every degree checked. Set equality was not tested.
- For `S_(3,5)` the two largest letters `R-1, R` occur equally often as last letters (for
  `D = 7`: 2879 each).
- `x_0 Y_(D-1) ⊆ Y_D` fails partially (for `D = 7`: 2363 of 2614).

**Heuristic trend (not a claim).** For all three sets, `log(Λ_S(D) - 1)` is close to linear
in `log D` with slope about `-0.41` over `3 <= D <= 7`.
- For `S_(2,4)` that extrapolation predicted a crossing near `D ≈ 10`; the exact crossing is `D = 11`.
- For `S_(3,5)` the local slope drifts from `-0.42` (`D = 7..8`) to `-0.385` (`D = 10..11`).
  At the last slope the naive crossing is near `D ≈ 45`, and a drifting slope pushes it later. `|M_(38,41)| = C(79,38)` is far beyond
exact enumeration, so a `P_(2,2)` certificate of this shape would need a structured family,
not a search. Moore's Følner lower bound bears on how long such a trend can last, but no
quantitative consequence for `Λ` is derived here.

## 4. Exact gap

- **Solving `P_(2,2)` by cardinality:** exhibit a finite `Y ⊆ M_D` with `|S_(3,5) Y| < 2|Y|`.
  None exists for `D <= 12`, which is exact. Candidates for larger `D` need an explicit
  structured family whose `|S Y|` can be counted without enumeration, e.g. a regular language
  in the letter-gap encoding.
- **Proving non-amenability through this row:** show `S_(3,5)`, or any `S_(m+1,m+d+1)`, doubling
  for all finite `Y`. By the equivalence claim this is equivalent to the root for the whole
  family, so no finite computation settles it.
