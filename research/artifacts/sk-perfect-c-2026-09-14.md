# rev4.4 fixes from sk-perfect-c (independent correctness audit), on rev4.3 md5 0648e5f8
Verdict: no errors, no gaps; every step re-derived independently of sk-perfect-a.

ADOPT:
- U1 (l.315–316): Cor 3 expander marking. `marked groups, whose Cayley graphs with respect to the images of a fixed generating set form a family of expanders. It is LEF`
- U2 (l.327) = perfect-a U8: `(Corollary~\ref{cor:wp})`.
- U3 (l.485–487, +1 line): `$\GL_m$ involve only $u^j$ with $|j|\le w$, where $w\ge1$, and an element $g$ of it satisfies $|g^n|/n\to0$ for the word length in these generators, then`
- N1 (l.492–493): append `, so $|[a,b]^n|/n\to0$ by subadditivity`.
- N3 = perfect-a U2 (lamps c).

MAIN'S RESOLUTION OF NOTATION CONFLICTS ACROSS AUDITS:
- A_V unit: `1_V` (perfect-a U1).
- §1 commutator [g,h]: `x` (perfect-d, perfect-a T4).
- §4 "Every S ⊆ ℕ": `C ⊆ ℕ` (perfect-d).
- Questions `(Y,S)` shift: `(Y,T')` (perfect-c N4).
- §3 degree bound w in the SL_3(Z) paragraph: `W` (perfect-a T5).
- §3 lamplighter coordinate h: `\eta` (perfect-a T6).
