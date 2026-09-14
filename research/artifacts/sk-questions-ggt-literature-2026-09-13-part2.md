# sk-questions-ggt: published group-theory and dynamics questions (part 2: second sweep, limits of the search, bibliographic data)

Continues `sk-questions-ggt-literature-2026-09-13-part1.md` (cd2f758f80). Same method: pdftotext on MSI, then grep and context reading.
Result of this sweep: no printed question below is answered by G_X as stated.

## 1. Second sweep
**Cornulier, "Groupes pleins-topologiques [d'après Matui, Juschenko, Monod, ...]", Séminaire Bourbaki 1064 (Jan. 2013), arXiv:2002.09342.**
The section "Problèmes et questions ouvertes" concerns [[ϕ]]′ for an infinite minimal subshift ϕ. It lists:
- (1) the Følner function;
- (2a)–(2f) subgroup structure. (2f) asks to "Classifier les morphismes entre les différents groupes [[ϕ]] ou [[ϕ]]′", and whether [[ϕ]]′ is non-cohopfian;
- (3) quasi-isometry classification;
- (4) proper actions on CAT(0) cube complexes;
- (5) finite decomposition complexity;
- (6) quasi-isometrically embedded trees and free semigroups;
- (7) uniform exponential growth, uniform free and torsion-free diameter;
- (8) "Soit sϕ cardinal minimal d'une famille génératrice de [[ϕ]]′. Existe-t-il des sous-décalages minimaux avec sϕ arbitrairement grand ?"

None is about G_X. Three have natural G_X analogues, owned by other lanes:
- (2f)/(3): classification of the G_X up to isomorphism, for sk-rigidity-ring and sk-rigidity-intrinsic;
- (8): the minimal number of generators of G_X, for sk-generators;
- (1): not applicable, since G_X is Kazhdan and non-amenable.

**Kourovka Notebook, extra greps** (approximable, ultraproduct, metric approximation, stable, finitely generated simple). Unrelated hits:
- 6.45 (Wiegold);
- 9.8 (intermediate growth);
- the ultraproduct problems at l.6956–7011 and l.7983–7996;
- 21.117 (Schesler; answered by Thompson's group V);
- 21.118 ("(A. Thom). Is there any group which is not isomorphic to the quotient of a residually finite group by an amenable normal subgroup?").

**Juschenko, "Amenability of discrete groups by examples", ETH course PDF (the AMS SURV 266 draft), Appendix C "Open problems in amenability".**
- Items C.1–C.38. None concerns property (T), LEF, or Kazhdan simple groups.
- C.5 ("Is there a 2-generated infinite simple amenable group?") was answered by Kionke–Schesler (arXiv:2304.09307, Theorem 1.1).
- C.25 asks whether Thompson's F is sofic.
- C.31–C.38 concern topological full groups and amenability.

**Other sources:**
- Caprace–Rémy, arXiv:math/0607664: no question lines.
- Gelander, arXiv:1807.06979, Question 6.2 ("Is every IRS in G co-sofic?", for locally compact G): unrelated. The IRS of G_X belong to sk-characters.
- Becker–Chapman, arXiv:2005.06652, Problem 1.5 (uniform flexible instability of hyperbolic groups): unrelated.
- Ershov, arXiv:0908.3734, Question 4.7 (GGS groups): unrelated.
- Juschenko–Monod, arXiv:1204.2132: no questions.
- de Cornulier–Guyot–Pitsch, Proposition 11: "There exists an infinite isolated group with Kazhdan's Property T". The examples are non-Hopfian groups Γ/Z of Abels type (§5.x, Proposition 5.11). They are finitely presented and not simple, so unrelated to G_X. Their soficity is the open point that Cornulier's Math. Ann. paper records (part 1, C2).
- Alekseev–Thom, arXiv:2608.05362 v1 (5 Aug 2026), Open problems section:
  > Open problem 6.1. Are there examples of finitely presented sofic groups with Kazhdan's property (T) that are not residually finite?

  The preceding text: "Kar and Nikolov constructed finitely presented sofic groups which are not residually finite [9]. These examples do not have Kazhdan's property." A finitely presented infinite simple sofic Kazhdan group would answer 6.1, since an infinite simple group is not residually finite. G_X is not finitely presented. The main node `sofic-fp-simple-kazhdan-group-from-fp-simple-ring` (sk-fp-sofic-a, f929240f29, OPEN) is the ring route to such a group.
- Kionke–Schesler, arXiv:2304.09307 (l.1674–1676):
  > A finitely presented LEF group is residually finite; see [72].

  Here [72] is Vershik–Gordon. This is the printed source for "G_X is not finitely presented".

## 2. Limits of the search
- AIMPL "Amenability of discrete groups" (aimpl.org/amenablediscrete): the site certificate has expired, and `curl -k` returns only a JavaScript shell with no problem text. Not checked. Juschenko's Appendix C appears to reproduce the workshop list (its preface mentions the workshop problems) but is not guaranteed identical.
- Lubotzky–Oppenheim, "Non p-norm approximated groups": not checked (the arXiv id I used was wrong).
- Glebsky–Rivera 2008, Vershik–Gordon 1997, Mann's book, Grigorchuk's problem surveys: not checked.
- The Baumslag–Myasnikov–Shpilrain problem site: only probFP.html was checked.
- Every other source was read only in grep context windows, not end to end.

## 3. Bibliographic data (Crossref, 2026-09-13)
- H. Bradford, Quantifying local embeddings into finite groups, J. Algebra 608 (2022), 214–238, doi:10.1016/j.jalgebra.2022.04.039. Question numbers quoted above are from arXiv:2104.07111 (§7); the journal numbering was not checked. arXiv:2211.15249 cites it as [Bra22] with "Question 6.5" and "Problem 6.6", so the journal numbering likely differs.
- H. Bradford and D. Dona, Topological full groups of minimal subshifts and quantifying local embeddings into finite groups, Ergodic Theory Dynam. Systems 43 (2023), no. 5, 1492–1510, doi:10.1017/etds.2022.12. Checked against the PDF (arXiv v1): the abstract, and Theorem 1.1 "Let Γ be a finitely generated subgroup of ⟦σ⟧. Then: ℒ_Γ(n) ⪯ (2R_X(n))!. In particular this inequality holds for Γ = ⟦σ⟧′."
- S. Kionke and E. Schesler, From telescopes to frames and simple groups, J. Comb. Algebra (2024), doi:10.4171/jca/103. The Crossref record has no volume or pages; the theorem numbers are from arXiv:2304.09307 v1.
- P.-E. Caprace and B. Rémy, Simplicity and superrigidity of twin building lattices, Invent. Math. 176 (2009), 169–221, doi:10.1007/s00222-008-0162-6.
- V. Alekseev and A. Thom, Centralizers of sofic approximations of Kazhdan groups, arXiv:2608.05362 (2026).
- A. Thom, Examples of hyperlinear groups without factorization property, arXiv:0810.2180 v1. The abstract says: "This group provides also an example of a sofic Kazhdan group which is not residually finite, answering a question from [ES05]." Theorem 1.4 states only LEF plus no factorization property.
