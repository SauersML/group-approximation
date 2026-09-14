# sk-panel-referee-4, part 1: symbolic and topological dynamics (2026-09-13)

Lane sk-panel-referee-4: a hostile referee at the Annals, Inventiones or JEMS standard, from symbolic and topological dynamics.

- **Subject:** main's `simple_kazhdan_sofic_group.tex` at tip 07a74132cd. This is revision 2 (e80dcf20ad), md5 4ad49212…, 386 lines; line numbers below refer to it.
- **Read:** the note; `sk/drafts/rev2-decisions.md`; sk-panel-referee-2 and -3 part 1. I do not repeat their findings (the Brown bridge, the Stepanov credit, locators).
- **Checked through Crossref this session:** the nine dynamics references in §5.
- **Not covered:** rev3 (§2 "LEF groups") has not landed. §6 is the dynamics checklist for it.

## 0. Verdict
**No dynamical claim is false.** I re-derived every step that uses dynamics:
- minimality and infiniteness exclude periodic points (l.185);
- small clopen neighborhoods and disjoint unions of small sets (l.182–187);
- covering X by finitely many translates of V (l.235–236);
- the periodic-word lemma (l.121–129);
- least period against word count (l.129–132);
- the models on Z/N_ℓ and the conjugation identity (l.134–145);
- surjectivity onto M_{N_ℓ}(F_2) through distinct shifts of y_ℓ (l.150–153);
- the Sturmian coding, the arc description and the count of ones (l.261–271);
- the easy direction of Question 3 (l.289–290).

**Blocking or near-blocking for a dynamics referee:**
- B1: one background fact has no source;
- B2: one sentence is imprecise in a way the proof depends on;
- B3: Question 3 omits the theorem it imitates.

**What would make it astonishing to a dynamicist:** §3 (A1, A2).

## 1. Blocking or near-blocking

### B1. Bounded complexity, l.130–132: no source
Current:
```latex
be the least period of $y_\ell$. Then $N_\ell$ is at least the number of
these words, which tends to infinity with $\ell$, since a subshift with
boundedly many words of each length is finite.
```
- **The fact:** a subshift with boundedly many words of each length is finite. It is Morse–Hedlund (1938); the sharp form p(n) ≥ n+1 for infinite X is Coven–Hedlund (1973).
- **Why a referee stops:** the note uses it to get N_ℓ → ∞, which the injectivity of the models and the expander family both need.
- **Fix, 0 text lines and +4 bibliography lines:** add `~\cite{MorseHedlund38}` after "finite."
- **Self-contained alternative, +1 line:** "…is finite: if $X$ has at most $K$ words of each length, some $n\le K$ has as many words of length $n+1$ as of length $n$, so every word of length $n$ extends uniquely on each side and every point of $X$ is periodic."
  - Checked: the word count is nondecreasing and bounded by K, so it is constant between some n ≤ K and n+1.
  - Unique extension on both sides makes every point periodic with period at most K.
  - So X is finite.

### B2. Forward recurrence, l.121–124: "occurs in x" is too weak
Current:
```latex
Fix $x\in X$ and $\ell\ge0$. By minimality every word of $X$ occurs in
$x$, and $x_{[0,2\ell)}$ recurs at arbitrarily large positions. Choose
```
- **The problem:** the construction needs every word of X inside $x_{[0,m+2\ell)}$, that is, in the forward half of x. "Occurs in x" gives a two-sided occurrence only.
- **What gives it:** minimality. The ω-limit set of x is nonempty, closed and T-invariant, so it is X. So x is forward recurrent, and every word of X occurs at arbitrarily large positions. Gottschalk–Hedlund.
- sk-panel-referee-1 part 2 flagged the same sentence.

Replacement, +1 line:
```latex
Fix $x\in X$ and $\ell\ge0$. By minimality the forward orbit of $x$ is
dense, so every word of $X$ occurs in $x_{[0,\infty)}$, and $x_{[0,2\ell)}$
recurs at arbitrarily large positions. Choose
```

### B3. Question 3, l.289–291, omits the theorem it imitates
Current:
```latex
If $(X,T)$ is conjugate to $(Y,S)$ or to $(Y,S^{-1})$, then
$G_X\cong G_Y$. Does $G_X\cong G_Y$ imply that $X$ and $Y$ are flip
conjugate, or at least strongly orbit equivalent~\cite{GPS}?
```
- **What is missing:** for topological full groups of minimal Cantor systems, the converse is a theorem. The full group determines the system up to flip conjugacy (Giordano–Putnam–Skau 1999, and Bezuglyi–Medynets 2008 for the derived group). The note's question is the matrix analogue.
- **Why it matters:** saying so tells the reader why "yes" is plausible, and credits the full-group theory the note already relies on (Matui, Grigorchuk–Medynets).
- **Main's graph:** `topological-full-groups-determine-flip-conjugacy` quotes Matui arXiv:math/0404117v3 Thm 2.8(ii) and Bezuglyi–Medynets arXiv:math/0611173v1 Thm 5.13 verbatim, from sk-rigidity-intrinsic.
- **Gap in my check:** I verified the metadata of both papers, not their theorem numbers. sk-lit-locators should confirm them before a locator goes into the note.

Replacement, +1 text line and +8 bibliography lines:
```latex
If $(X,T)$ is topologically conjugate to $(Y,S)$ or to $(Y,S^{-1})$, then
$G_X\cong G_Y$. For topological full groups the converse
holds~\cite{GPS99,BezuglyiMedynets}. Does $G_X\cong G_Y$ imply that $X$ and
$Y$ are flip conjugate, or at least strongly orbit equivalent~\cite{GPS}?
```

## 2. Line-level fixes (0 lines each)
- **F1, l.150–151:** "the rotations of $y_\ell$ are distinct" → "the shifts $T^ty_\ell$, $0\le t<N_\ell$, are distinct". "Rotation" belongs to the circle, and §2 of the note uses it for circle rotations.
- **F2, l.262–263:** "the closure of the codings $c(\theta)$" → "the closure of the set of codings $c(\theta)$". The coding map is discontinuous at the points $-j\alpha$, and the closure adds the left-continuous codings. The words of length n are unchanged, as the note's arc description implicitly uses.
- **F3, l.289:** "conjugate" → "topologically conjugate". This is folded into B3's replacement.
- **F4, l.185 (optional, +0 when merged into the sentence):** "Minimality and infiniteness imply that $T$ has no periodic points" can take a parenthesis: "(a periodic orbit is a closed invariant set)". Standard; leave it out if space is short.

## 3. What would make it astonishing for dynamicists (ranked)

### A1 (recommended, +1 line): the finite models are the same construction over periodic orbits
The note's models live on $\F_2^{\Z/N_\ell\Z}$ with the cyclic shift P and the diagonal matrices D_ℓ(f). That is exactly the crossed product of the periodic orbit $O_\ell$ of $y_\ell$ by $\Z/N_\ell$, since a free transitive action has crossed product $\End(\F_2[O_\ell])$. So the theorem reads: G_X is the marked limit of the groups of the periodic orbits that approximate X.

Add after l.154 ("$\EL_3(M_{N_\ell}(\F_2))=\SL_{3N_\ell}(\F_2)$"):
```latex
In other words, $\SL_{3N_\ell}(\F_2)=\EL_3\bigl(\LC(O_\ell,\F_2)\rtimes\Z/N_\ell\bigr)$
for the periodic orbit $O_\ell$ of $y_\ell$.
```
Checked: the crossed product has basis $e_{\{T^ty_\ell\}}u^j$, of dimension $N_\ell^2$. Sending it to $D_\ell(e_{\{T^ty_\ell\}})P^j$ is the regular representation, which is an isomorphism onto $M_{N_\ell}(\F_2)$ because the orbit has least period $N_\ell$. ρ_ℓ is the composition of the free algebra with this map.

### A2 (recommended if the budget allows, +4 text lines, +5 bibliography lines): the amenable simple group of the system inside its Kazhdan simple group
The derived topological full group $[[T]]'$ is an infinite, finitely generated, simple, amenable group (Matui; Juschenko–Monod). It embeds in $G_X$ through $g\mapsto\operatorname{diag}(w_g,1,1)$, where $w_g\in R$ is the unit implementing g, using the Whitehead identity for commutators of units.
- Source: sk-subgroups, d7c85d2079, `topological-full-group-embeds-in-subshift-elementary-group`, reviewed PASS in sk-review-2 part 3.
- Under the note's models, $w_g$ becomes a permutation matrix of the periodic orbit. So Grigorchuk–Medynets' LEF models of $[[T]]$ are the restriction of the note's models.
- For a dynamicist this is the most striking sentence the note could carry: one minimal subshift gives both a simple amenable group and a simple Kazhdan group containing it.
- Use sk-subgroups' verbatim text; it already avoids diag(a,a⁻¹,1).

### A3 (Cairn only, not for the note)
- Rational eigenvalues: $e^{2\pi i/p}$ is an eigenvalue iff $R\cong M_p(S)$, so $G_X\cong\EL_{3p}(S)$ (sk-open-4, PASS in sk-review-2).
- The $K^0$ and homology dictionary.
- Both are true and pretty, but they answer no printed question and cost definitions.

## 4. Credit and background table (dynamics)
| l. | Claim | Source now | Action |
|---|---|---|---|
| 49–51 | infinite minimal subshift | standard | none |
| 65–67 | periodic approximation, as in GM Thm 2.6 | GM (sk-citations checked) | none |
| 75–77 | Matui's tower pattern for $[[T]]'$ | Matui | none |
| 121–124 | minimality ⇒ dense forward orbit | none | B2 (wording); optional `\cite{GottschalkHedlund}` or `\cite{DurandPerrin}` |
| 130–132 | bounded complexity ⇒ finite | none | B1: `\cite{MorseHedlund38}` |
| 185 | no periodic points | implicit | F4 optional |
| 261–264 | Sturmian subshift = closure of rotation codings; infinite, minimal | MH40 only | C1: add Hedlund 1944 |
| 268–271 | the count of ones | proved inline | none |
| 289–291 | flip conjugacy, SOE | GPS95 | B3: GPS99, Bezuglyi–Medynets |
| — | background textbook | none | C2 (optional): Durand–Perrin 2022 covers minimality, complexity, Sturmian codings, $K^0$ and SOE in one reference |

- **C1 (recommended, 0 text lines, +4 bibliography lines):** l.264 `~\cite{MorseHedlund}` → `~\cite{MorseHedlund,Hedlund44}`. Hedlund's "Sturmian minimal sets" is the paper that treats the minimal sets and their codings; MH40 treats Sturmian trajectories.
- **C2 (optional):** a single textbook citation instead of scattered classical ones. Not needed if B1 and C1 go in.

## 5. Bibitems, checked through Crossref this session
Crossref returns only the first page for MH38 and Hedlund44. The last pages (866, 620) are from memory, so check them before print (sk-lit-locators).
```latex
\bibitem{MorseHedlund38}
M.~Morse and G.~A. Hedlund, \emph{Symbolic dynamics},
Amer. J. Math. \textbf{60} (1938), 815--866.
\doi{10.2307/2371264}.

\bibitem{Hedlund44}
G.~A. Hedlund, \emph{Sturmian minimal sets},
Amer. J. Math. \textbf{66} (1944), 605--620.
\doi{10.2307/2371769}.

\bibitem{GPS99}
T.~Giordano, I.~F. Putnam, and C.~F. Skau,
\emph{Full groups of Cantor minimal systems},
Israel J. Math. \textbf{111} (1999), 285--320.
\doi{10.1007/BF02810689}.

\bibitem{BezuglyiMedynets}
S.~Bezuglyi and K.~Medynets,
\emph{Full groups, flip conjugacy, and orbit equivalence of Cantor minimal
systems}, Colloq. Math. \textbf{110} (2008), 409--429.
\doi{10.4064/cm110-2-6}.

\bibitem{JuschenkoMonod}
K.~Juschenko and N.~Monod,
\emph{Cantor systems, piecewise translations and simple amenable groups},
Ann. of Math. (2) \textbf{178} (2013), 775--787.
\doi{10.4007/annals.2013.178.2.7}.
```
- **Also checked, not proposed:**
  - Coven–Hedlund, Math. Systems Theory 7 (1973) 138–153, doi 10.1007/BF01762232 (sharp complexity);
  - Herman–Putnam–Skau, Internat. J. Math. 3 (1992) 827–864, doi 10.1142/S0129167X92000382 (Kakutani–Rokhlin partitions; not needed, since the note never uses Bratteli diagrams);
  - Durand–Perrin, *Dimension groups and dynamical systems*, Cambridge 2022, doi 10.1017/9781108976039 (Crossref returns only the title and year; the series number is unchecked);
  - GPS95, Crelle 469 (1995) 51–112, doi 10.1515/crll.1995.469.51, matches the note's bibitem.
- The authors' first names were not returned by the grep I ran; the initials follow the standard printed forms.

## 6. Dynamics checklist for rev3 (§2 "LEF groups", not yet landed)
For the reviewer of rev3 once main lands it:
- **Minimality:** L = Z/2 ≀ Δ acts on $2^\Delta$ by shifts and the flip at e. Orbits contain all finite modifications, so they are dense.
- **Topological freeness, not freeness:**
  - for δ ≠ e, the fixed set of the shift is nowhere dense;
  - elements with a nontrivial lamp part move every point;
  - constant configurations are fixed by every shift. So the text must never say "free".
- **Density patch:** the small sets no longer partition every clopen set. The step "g commutes with every $e_{ij}(e_V)$" must go through entries.
  - Row and column entries give $g_{pi}e_V=0$ and $g_{ii}e_V=e_Vg_{jj}$ for small V.
  - Small sets have dense union, and coefficients are locally constant, so the vanishing extends to X.
  - Check that the written patch really proves this.
- **Covering step:** uses minimality of the L-action, and finitely many translates of a small V cover $2^\Delta$.
- **Models:** "legal configurations" is vacuous for the full shift $2^\Delta$, so the text should not suggest a constraint.
- **Word length** replaces |j| throughout, and "no periodic points" becomes "free points are dense (Baire)".
- **Credit:** Kionke–Schesler for the RF-to-simple-LEF embedding without (T); Ore 1951 for the overgroup.

## 7. Line cost and recommendation
- **Recommended:**

  | Item | Text lines | Bibliography lines |
  |---|---|---|
  | B1 | 0 | +4 |
  | B2 | +1 | 0 |
  | B3 | +1 | +8 |
  | C1 | 0 | +4 |
  | A1 | +1 | 0 |
  | F1–F3 | 0 | 0 |
  | **Total** | **+3** | **+16** |

- **Optional:** A2 (+4 text, +5 bibliography lines), F4 and C2.
- **Reader trade-off:**
  - B1–B3 and C1 source every dynamical fact the proof uses, and give Question 3 its context. No new machinery.
  - A1 turns the finite models into dynamics at the cost of one line.
  - A2 gives dynamicists a reason to read the paper, but it costs one classical citation and the $w_g$ formula.
- **No Cairn nodes and no review requests:** this is referee prose, with no new mathematical claim.
