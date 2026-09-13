# sk-questions-oa: operator-algebra questions the group answers, and the sentences the note should carry

Lane sk-questions-oa. Line numbers refer to `manuscript-disk-1646.tex` (the 340-line disk version).
Group: `G_X = EL_3(LC(X,F_2) ⋊_T Z)` for an infinite minimal subshift `X`; infinite, f.g., simple, property (T), LEF, so sofic and hyperlinear.

## Summary verdict
The note already answers the three questions it targets: Brown 2001 (von Neumann form), Ozawa 2003 (hyperlinear form), Pestov 2008 (sofic form). My lane confirms this and finds exactly ONE cheap, verified, new-flavored operator-algebra sentence worth adding, plus one optional sharpening. Everything else in the operator-algebra direction is either already covered by the existing "hyperlinear" clause or too long for a short note.

## Finding 1 (RECOMMEND, one sentence): the factorization property
G_X has property (T) and is not residually finite, because an infinite finitely generated simple group has no nontrivial finite quotient. By Kirchberg's theorem, a property (T) group has Kirchberg's factorization property if and only if it is residually finite. So G_X does not have the factorization property, while being sofic and hyperlinear. In Ozawa's landscape (residually amenable ⊂ factorization property ⊂ hyperlinear for f.g. groups), G_X is an infinite simple group that sits strictly on the hyperlinear side of the factorization-property boundary.
- Prior art: Thom (2010) already gave finitely generated Kazhdan LEF non-residually-finite groups, hence hyperlinear without the factorization property; the note cites him. The new content here is that G_X is SIMPLE, and the factorization-property phrasing places it against Kirchberg's dichotomy. So this is a placement sentence, not a new theorem — credit Kirchberg and Thom.
- Verified: Kirchberg, "Discrete groups with Kazhdan's property T and factorization property are residually finite," Math. Ann. 299 (1994), no. 3, 551--564. Confirmed via EUDML/Springer. The iff form ((T): FP ⟺ RF) is the standard statement.

### Proposed text (verbatim LaTeX)
BEFORE (l.63--65, the Thom sentence at the end of the intro paragraph):
```
Thom had already constructed a finitely generated Kazhdan LEF group
that is not residually finite~\cite[Theorem~1.4]{Thom}; his example
is not simple.
```
AFTER (adds one sentence after it; +2 lines):
```
Thom had already constructed a finitely generated Kazhdan LEF group
that is not residually finite~\cite[Theorem~1.4]{Thom}; his example
is not simple. Being infinite and simple, $G_X$ has no nontrivial
finite quotient, so by Kirchberg it lacks the factorization
property~\cite{Kirchberg} while remaining sofic.
```
Bibitem to add:
```
\bibitem{Kirchberg}
E.~Kirchberg, \emph{Discrete groups with Kazhdan's property~\textup{(T)}
and factorization property are residually finite},
Math. Ann. \textbf{299} (1994), 551--564.
\doi{10.1007/BF01459798}.
```
- Length change: +2 lines of text, +4 lines of bibliography.
- Reader trade-off: it turns "not residually finite, sofic" into a named place in Kirchberg's dichotomy at no extra machinery; the reader gains a second published question the group speaks to. NOTE: the DOI 10.1007/BF01459798 is my best reconstruction of the Math. Ann. 299 article DOI and MUST be confirmed by Crossref before use (sk-citations owns this). If unconfirmed, drop `\doi{...}` and keep volume/pages.
- Status: node `simple-kazhdan-group-lacks-factorization-property` (claim) + `-proof` route + `kirchberg-property-t-fp-implies-rf` (claim) + `-citation` route. Unreviewed; queued for sk-referee-2.

## Finding 2 (OPTIONAL sharpening, one sentence): a property (T) factor in R^ω from a simple group
G_X is ICC: an infinite simple group is centerless, and if a nontrivial element had a finite conjugacy class its centralizer would have finite index, whose normal core would be a proper finite-index normal subgroup — impossible in an infinite simple group. So L(G_X) is a separable II_1 factor. It has property (T) (Connes--Jones), and since G_X is hyperlinear, L(G_X) embeds in R^ω (Ozawa, Prop. 7.1). So the note produces a property (T) II_1 factor inside R^ω that is the group factor of an infinite simple group.
- This is exactly Brown's original von Neumann formulation (embed the group into U(M) for an R^ω-embeddable McDuff factor M): take M = R^ω, which is McDuff and R^ω-embeddable, and U(R^ω) ⊇ G_X by hyperlinearity. So the note's existing "hyperlinear" clause ALREADY answers Brown's factor question literally; this sentence only makes the factor L(G_X) explicit.
- Property (T) R^ω-embeddable II_1 factors already exist (L(SL_3(Z))). The only new element is "from a simple group," which is not obviously an interesting property of the factor. So I rate this LOWER value than Finding 1 for a short note.
- Verified: Ozawa Prop 7.1 (Γ hyperlinear ⟺ LΓ ⊆ R^ω), from arXiv:math/0306067; Connes--Jones, "Property T for von Neumann algebras," Bull. LMS 17 (1985) 57--62 (property (T) group + ICC ⟹ L(G) is a property (T) factor).
- Recommendation: OFFER as a possible one-line remark; default is to NOT add it, since the hyperlinear clause already covers Brown. Node `simple-kazhdan-group-gives-property-t-factor-in-r-omega` (claim) + `-proof`; ICC via `infinite-simple-groups-are-icc`.

## Findings that do NOT earn a sentence (kept out, with reasons)
- Kirchberg/QWEP, LLP, exactness: G_X does not resolve QWEP or Connes embedding; C*(G_X) LLP status is not decided by soficity. No true short statement. Out.
- Quasidiagonality of the canonical trace and MF status: this is the un-traces / un-reduced-cstar territory (`elementary-group-trace-amenable-iff-ring-rf`, corona traces). For the note's LEF group the ring LC(X,F_2)⋊Z is residually finite, so those results give MF/QD-positive statements; they belong to a consequences section the short note deliberately dropped. Defer to sk-operator-algebras; do not add to this note.
- Character rigidity / IRS (Peterson--Thom, Bekka, Dudko--Medynets): sk-characters owns it; if a clean theorem lands it could be one sentence, but it is a separate result, not a question the note already answers. Out of my lane.

## Boundary with peers
- sk-operator-algebras: owns the full menu of C*/vN corollaries and should decide whether any MF/QD sentence returns; I hand it Findings 1--2 and the "kept out" list.
- sk-characters: owns character/IRS.
- sk-citations: owns confirming the Kirchberg DOI and the Connes--Jones reference.
