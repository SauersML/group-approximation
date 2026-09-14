# sk-kourovka-hunt: printed problems settled or sharpened by the 09-13/09-14 verified results (2026-09-14)

Lane sk-kourovka-hunt, a literature lane with no Cairn claims. The task: find PRINTED problems that today's verified results answer or sharpen. The older results (Brown Q7, Ozawa, Pestov 9.1, Pestov–Kwiatkowska, Elek–Szabó, Kionke–Schesler, Kourovka 20.7, Rauzy, Cornulier (2e), Alekseev–Thom 6.1, Cyr–Franks–Kra–Petite 5.1–5.3) are in `research/artifacts/sk-answered-questions-2026-09-13-part2.md` and are not repeated here.

## Sources and search bounds
- **Kourovka Notebook:** the e-print TeX `21tkt.tex` on MSI (26953 lines; it cites the Sauer–Schesler 2026 preprint, so it is a 2026 update of arXiv:1401.0300). Greps:
  - "uniform(ly) exponential growth";
  - "simple amenable" and "amenable simple";
  - Kazhdan and "(T)";
  - sofic, hyperlinear, "locally embeddable";
  - "full group";
  - maximal subgroups, commutator width, "boundedly generated", "uniformly simple", "coarse embed";
  - "conjugacy problem", "property A", "exact".
- **Cornulier, Séminaire Bourbaki 1064** (arXiv:2002.09342): e-print `bou1064.tex`, subsection "Problèmes et questions ouvertes", read in full (items (1)–(8)).
- **Sauer–Schesler, arXiv:2605.30163:** e-print `nonuniformgrowth.tex`, l.266–310, all four printed questions.
- **Sauer–Schesler, arXiv:2606.15945:** e-print `nonuniformgrowth_hyp.tex`, l.157.
- **Not searched this lane:** the Bekka–de la Harpe–Valette open problems, the AIM and Guyot problem lists, and Thom's ICM 2018 paper. Pestov BSL and Capraro–Lupini were swept by sk-answered-questions, with no answered problem beyond the paper's lineage.

## Matches

| # | Printed problem (verbatim) | Locator | Today's result | Status |
|---|---|---|---|---|
| M1 | "Le groupe $\lb\vpi\rb'$ a-t-il une croissance exponentielle uniforme? A-t-il un diamètre semi-libre (resp. sans torsion) uniforme (c'est-à-dire, existe-t-il un entier $N$ tel que pour tout système générateur, la $N$-boule contient un couple d'éléments engendrant librement un semi-groupe libre (resp. contient un élément sans torsion)?" | Cornulier, Bourbaki 1064, "Problèmes et questions ouvertes", item (7); here $\vpi$ is an infinite minimal subshift | For a primitive substitution of constant length 2 with a non-periodic fixed point, $[[T]]'$ has non-uniform exponential growth. Unconditional for Thue–Morse; the general dyadic case rests on the Mossé import. | **FIRST CLAUSE ANSWERED NEGATIVELY for these subshifts** (PASS twice: sk-verify-16, sk-verify-17). Open for Sturmian $\vpi$ (sk-sturmian-growth part2: no constant towers). The second clause is untouched. No printed answer found. |
| M2 | "(a) Does there exist a finitely generated simple group that is of exponential growth but not of uniformly exponential growth?" | Kourovka 21.117(a) (E. Schesler), `21tkt.tex` l.14289–14290 | The Thue–Morse $[[T]]'$ is infinite, f.g., simple and AMENABLE of non-uniform exponential growth (`simple-amenable-group-of-non-uniform-exponential-growth`). The Thue–Morse $G_X$ is simple, Kazhdan and LEF of non-uniform exponential growth (`simple-kazhdan-lef-group-of-non-uniform-exponential-growth`, sk-verify-14 PASS; the Thue–Morse case needs no Mossé input). | **SHARPENED.** The printed answer (l.14296) is Thompson's $V$ (Sauer–Schesler 2026), which is neither amenable nor Kazhdan nor LEF. |
| M3 | "de la Harpe asked whether there exists a group of non-uniform exponential growth that has Kazhdan's property (T)." | de la Harpe 2002 survey, §7, as quoted by Sauer–Schesler arXiv:2606.15945 l.157 (secondary; the survey was not opened) | The Thue–Morse $G_X$: simple, Kazhdan and LEF of non-uniform exponential growth. | **SHARPENED.** The printed answer is Sauer–Schesler 2606.15945, an acylindrically hyperbolic group, which is not simple. Hull caution (sk-free-8): simple quotients of their group might already give "simple Kazhdan", so the new part rests on LEF. |

**Kourovka 21.117(b)** asks: "Does there exist a finitely generated hereditarily just-infinite group that is of exponential growth but not of uniformly exponential growth?" The printed answer (l.14296) says $V$ answers "both questions". However, Sauer–Schesler 2605.30163 (l.281–294) separate simple groups from hereditarily just-infinite groups (the Wilson–Grigorchuk trichotomy) and claim only the finitely presented and simple questions. Our examples are simple and not residually finite, so they add nothing to (b) in the residually finite sense. No claim.

**Sauer–Schesler 2605.30163, Question `que:vcd`:** "Does there exist a finitely generated group of non-uniform exponential growth that has finite virtual cohomological dimension?" Both examples contain torsion, so they do not bear on it.

## No printed problem found for the other results (bounded as above)
- **LEF with solvable word problem ⇔ subgroup of a simple Kazhdan LEF host with solvable word problem:** Kourovka 20.7 and Boone–Higman–Thompson are covered in sk-answered-questions F1–F2. No LEF variant is printed.
- **Continuum many $G_X$, none a subgroup of another:** Kourovka 4.60 (P. Hall) already has the printed answer "continuum" for 2-generated simple groups; no printed question asks for mutual non-embeddability.
- **Non-exact simple Kazhdan LEF groups (Osajda):** there are no Kourovka hits for "property A", "exact" or "coarse embed". Kourovka 15.7 (C*-simplicity and unique trace without amenable normal subgroups) is answered in print by Breuillard–Kalantar–Kennedy–Ozawa and Le Boudec. C*-simplicity of $G_X$ is open, so there is no bearing.
- **Character rigidity:** no hits.
- **Bounded elementary generation (78), bounded conjugation-invariant norms:** no "uniformly simple" or "boundedly simple" hit. Kourovka 12728 (boundedly generated residually finite groups linear?) does not apply, since $G_X$ is not residually finite.
- **Conjugacy-problem degree equal to the jump:** Kourovka 5.21 (Collins; answered by Darbinyan 2021) and 5.22 (Collins; answered by Ol'shanskii–Sapir 2004) are answered, and no simple-group variant is printed.
- **Continuum many classes of maximal subgroups:** the Kourovka hits (8.35, l.15087, l.15105, l.23343) concern finite or algebraic groups.
- **Outer automorphism inn(diag(u,1,1)):** no hits.
- **SL₃(Z) lies in no $G_X$:** covered earlier (sk-answered-questions V2, N2).
- **Kourovka 18.109** (Kazhdan groups onto infinitely many rank-1 Lie-type groups): does not apply, since $G_X$ is simple.
- **Kourovka Vannacci problem (l.13085–13097)** on residually finite hereditarily just-infinite amenable groups: requires residual finiteness.
- **Kourovka l.14026** "Is every group sofic?": outside today's list; the repository already records that nonsofic groups exist.
- **Cornulier item (2c)** (subgroups of $[[\vpi]]$ of exponential or polynomial growth): subgroups of intermediate growth exist by Matte Bon (arXiv:1408.0762, recalled from the listing in sk-cornulier-q7's sources), and today's results do not bear on it.
- **Cornulier items (5) (FDC of $[[\vpi]]$) and (8) (minimal generating-set size):** not today's results.

## For the paper
No change. M1–M3 concern growth, which is off the note's theme. The Cairn nodes carry the Mossé condition and the Hull caution.
