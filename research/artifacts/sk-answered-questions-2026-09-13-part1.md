# sk-answered-questions: printed questions answered or sharpened by the note's results (part 1: scope, prior coverage, first rows)

Lane sk-answered-questions (ROSTER-H, wave 10), 2026-09-13 ~22:05 CDT. This part is literature facts only: no Cairn claims and no .tex edits.

## 0. Scope
Results in scope, from rev3 on main (9047d0d3c9) and the rev4 candidates in decision log items 71, 78, 79, 83:
- R1: infinite f.g. simple Kazhdan LEF (so sofic, hyperlinear) groups G_X; marked limits of SL_{3N}(F_2) expanders.
- R2: a f.g. group is LEF iff it is a subgroup of an infinite f.g. simple Kazhdan LEF group (candidate: … a marked limit of finite simple expanders).
- R3: one such host contains every f.g. linear group (rev3); candidate: every recursively presented f.g. LEF group.
- R4: no universal host has solvable word problem (candidate, sk-wp-host).
- R5: GL_m(LC(X,F_q)⋊Z) has no distorted elements, so SL_3(Z), H_3(Z) and BS(1,2) lie in no G_X (candidate).
- R6: every Turing degree is the word-problem degree of some G_X.
- R7: each separable II_1 factor contains G_X for only countably many X (candidate, sk-strong-7).
- R8: G_X is character rigid (candidate; passed sk-characters-rigidity-a).

## 1. Prior coverage on main (not repeated; I build on it)
- `sk-questions-ggt-literature-2026-09-13-part1/2` + proposal (group theory and dynamics, against R1 only). Verdicts:
  - A1: Pestov–Kwiatkowska arXiv:0911.4266 p. 28 ("it remains in particular unknown whether finitely generated simple Kazhdan groups can be hyperlinear/sofic") is ANSWERED by R1, and is the same lineage as Brown–Ozawa–Pestov.
  - B1–B3 (Kionke–Schesler Thm 1.2 prior art; Bradford Questions 7.2 and 7.5; Lubotzky via Bradford Question 6.7): variants only.
  - C1–C8: nearby questions R1 does not answer, including Alekseev–Thom Open problem 6.1 (f.p.), Cornulier (isolated groups), Thom p. 3 (Champetier's groups), Kourovka greps.
- `sk-questions-oa-proposal-2026-09-13` (operator algebras, against R1): Kirchberg factorization property; the property (T) factor L(G_X) in R^ω.
- `sk-strong-7-operator-algebras-2026-09-13` §1: verbatim quotes of Brown 2001 §Questions Q3 and Q7, and of Ozawa's printed wish (R7).

What this lane adds: the sweep against R2–R8, which no earlier lane did, and a table for the introduction.

## 2. First rows (checked at source)
**N1. Kourovka Notebook 20.7 (J. Belk), Boone–Higman.** Current arXiv:1401.0300 text on MSI, l.6931–6934:
> 20.7. (W. Boone and G. Higman) Does every finitely generated group with solvable word problem embed into a finitely presented simple group? It is known that every such group embeds into a simple subgroup of a finitely presented group (W. Boone, G. Higman, J. Austral. Math. Soc., 18, no. 1 (1974), 41–53).

- Relation to R2: R2 is the LEF analogue of the Boone–Higman THEOREM (a characterization through simple overgroups), not an answer to 20.7.
- Use: the locator and bibitem data for the Boone–Higman parallel adopted in decision 79 (b-C5): W. W. Boone and G. Higman, *An algebraic characterization of groups with soluble order problem*, J. Austral. Math. Soc. 18 (1974), 41–53. The title is to be confirmed at source in part 2.
- Verdict: FRAMING, not answered.

**N2. Kourovka greps for R3–R6** (same text file):
- "universal group": 1 hit, a p-subgroup of Hall's universal group. Unrelated.
- "Turing": 1 hit, l.1518 (m-reducibility of numerations). Unrelated.
- "distort": l.8514–8519, left-orderable groups with every element distorted. Unrelated to R5.
- "embedded into a simple / subgroup of a simple / embeddable in a simple": 1 hit, l.6253 (open subgroups of simple t.d.l.c. groups). Unrelated.
- "word problem" (26 hits) includes:
  - 5.15 (Cannonito): f.p. RF groups with recursive but not primitive recursive WP;
  - 5.16 (Cannonito–Miller): locally linear groups in f.p. groups;
  - 20.7 (N1).

  None is answered by R3/R4/R6.
- "II_1": 0 hits. "expander": 1 hit (the Ershov–Jaikin-Zapirain problem, already C4 in sk-questions-ggt).
- Verdict: the Kourovka Notebook contains no printed problem answered by R2–R8. Bound: these greps plus those of sk-questions-ggt; not an end-to-end reading.

**N3. Brown 2001, §Questions** (quoted verbatim in sk-strong-7 §1.3):
- Q7 is the note's lineage question, ANSWERED by R1; the note already says so.
- Q3 ("Can a free group factor or a II$_1$ factor with property T contain a weakly dense, QD C$^*$-subalgebra? How about a Popa algebra?") is NOT answered: L(G_X) is a new candidate, but no construction is known (sk-strong-7 open item).

**N4. Ozawa, There is no separable universal II_1-factor, PAMS 132 (2004)**, the printed wish after Theorem 2 (quoted in sk-strong-7 §1): "it would be interesting to know whether all (or at least one of) Γ_α's are embeddable into the unitary group U(R^ω)".
- The Γ_α are Gromov–Olshanskii groups, so R7 does not answer the wish as printed.
- R7 realizes the same separability argument with an R^ω-embeddable family.
- Verdict: VARIANT (sharpening in spirit), pending sk-verify-10. Direct verification against the PDF text is in part 2.

## 3. In progress (part 2)
Sources downloaded to MSI `/scratch.global/sauer354/sk/sk-answered-questions/`:
- Capraro–Lupini arXiv:1309.2034; Pestov BSL arXiv:0804.3968;
- Kharlampovich–Myasnikov–Sapir arXiv:1204.6506; arXiv:2111.01190 (problems on algorithmic descriptions of groups); arXiv:2402.01882 (universal groups);
- Cyr–Franks–Kra–Petite arXiv:1611.05913;
- Ioana ICM arXiv:1712.00151; Popa's Fields 2007 open problems; Chifan–Drimbe–Ioana arXiv:2205.07442; Ozawa arXiv:math/0210411;
- Lubotzky arXiv:1105.2389; Peterson–Thom arXiv:1303.4007;
- Belk–Bleak–Matucci–Zaremsky arXiv:2309.06224 and the Boone–Higman progress survey;
- arXiv:2504.12707; arXiv:2509.12161; Brown arXiv:math/0111286; Ozawa arXiv:math/0306067; Alekseev–Thom arXiv:2608.05362.
