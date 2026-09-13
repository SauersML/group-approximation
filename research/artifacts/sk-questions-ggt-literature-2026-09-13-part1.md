# sk-questions-ggt: published group-theory and dynamics questions that G_X answers or sharpens (part 1)

Lane sk-questions-ggt, 2026-09-13. Here G_X = EL_3(LC(X,F_2) ⋊_T Z) for an infinite minimal subshift X, which is infinite, finitely generated, simple, Kazhdan and LEF (disk note, l.44-53).
Operator-algebra questions belong to sk-questions-oa (landed 165f201aba, 45988bba10) and are not repeated here.

## 0. Method and bound
- Text was extracted with pdftotext on MSI (poppler 25.11 under gcc 13 libstdc++) from arXiv PDFs downloaded on 2026-09-13.
- For each source I grepped for `Question|Problem|Conjecture|open question|natural to ask|would be interesting|remains open|we do not know|is unknown`, and for `Kazhdan|property (T)|simple|LEF|sofic|hyperlinear`. Then I read the surrounding context windows. Every quote below was copied from those windows.
- These were not end-to-end readings: the bound is "every printed question located by these greps".

Sources:
- Kourovka Notebook, arXiv:1401.0300. The downloaded file includes "Comment of 2025" entries and 2026 preprint references, so it is the current edition.
- Bradford, arXiv:2104.07111 and arXiv:2211.15249 (v2, 2024).
- Bradford–Dona, arXiv:2106.09145.
- Bradford, arXiv:2201.05052.
- Kionke–Schesler, arXiv:2304.09307 and arXiv:2106.08742.
- de Cornulier–Guyot–Pitsch, arXiv:math/0511714.
- Cornulier, "A sofic group away from amenable groups" (normalesup.org/~cornulier/sofic.pdf).
- Thom, arXiv:0810.2180.
- Pestov–Kwiatkowska, arXiv:0911.4266.
- Nekrashevych, arXiv:1511.08241.
- Grigorchuk–Medynets, arXiv:1105.0719.
- Arzhantseva–Păunescu, arXiv:1212.6780.
- Arzhantseva–Cherix, arXiv:2008.12954.
- Glebsky, arXiv:1506.06940.
- arXiv:1712.01052 ("Finitary approximations of groups").
- Becker–Lubotzky, arXiv:1809.00632.
- Kun–Thom, arXiv:1901.03963.
- Fournier-Facio–Gerasimova et al., arXiv:2307.13155.
- arXiv:2512.09180.
- Alekseev–Thom, arXiv:2512.15494.
- arXiv:2608.05362 ("Centralizers of sofic approximations of Kazhdan groups").
- Katzlinger survey, arXiv:1907.07424.
- arXiv:2305.00248 (open questions in descriptive set theory and dynamics).
- Bleak–Donoven–Harper–Hyde, arXiv:2607.21754.
- The Baumslag–Myasnikov–Shpilrain problem page (probFP.html).

## 1. Verdicts

### A. Printed questions that G_X answers as stated
**A1. Pestov–Kwiatkowska, arXiv:0911.4266, lecture notes, arXiv p. 28 (text l.1378-1384).**
> It is in view of such results that Ozawa asked whether every finitely generated Kazhdan group that is sofic is residually finite. A negative answer was announced by Thom [26]. Consequently, a hope to use property (T) in order to construct non-hyperlinear groups is a bit diminished now, but surely not gone, as it remains in particular unknown whether finitely generated simple Kazhdan groups can be hyperlinear/sofic.

- This is the Ozawa/Pestov question again, in a later survey. It is the same lineage, not a new question.
- It is already recorded on main: `research/artifacts/pestov91-literature-background-2026-09-13-part4.md` l.218 and `ex-novelty-pestov91-deep-pass-2026-09-12.md` l.54.
- Verdict: ANSWERED, and ALREADY RECORDED. The note needs no change; the lineage sentence is the user's decision.

No other question in the sources above is answered by G_X as printed.

### B. Printed statements and questions where G_X is a new instance, or would give a stronger form
**B1. Kionke–Schesler, "From telescopes to frames and simple groups", arXiv:2304.09307 v1.** Abstract:
> We show that every finitely generated residually finite (amenable) group embeds into a finitely generated (amenable) LEF simple group.

Theorem 1.2 (= Theorem 9.14):
> Let H be a finitely generated, residually finite (amenable) group. There is a finitely generated, residually finite (amenable) group G and an infinite, simple, (amenable) LEF group Q such that (1) there is an embedding ι : H → G, (2) there is a projection π : G → Q, (3) the composition π ◦ ι is injective.

- Their text (l.87-95) calls "which groups embed into finitely generated, simple amenable groups" a natural question whose "complete answer ... seems yet to be out of reach".
- G_X-type groups cannot be amenable. The analogue with property (T) added, "every f.g. RF group embeds in an infinite f.g. simple Kazhdan LEF group", is sk-universal-embedding-a's target.
- Kionke–Schesler Theorem 1.2 is the prior result without (T), and any such corollary must credit it.
- Verdict: PRIOR ART for the embedding lanes. There is no printed (T) question here.

**B2. Bradford, "Quantifying local embeddings into finite groups", arXiv:2104.07111, §7.**
> Question 7.2. What is the LEF growth of [[T ]]0 ? How does it depend on the dynamical properties of (X, T )?

> Question 7.5. Does there exist an uncountable family G of pairwise non-isomorphic finitely generated LEF groups, such that for all Γ, ∆ ∈ G, if LΓ ≈ L∆ then Γ ∼= ∆?

- Bradford–Dona, arXiv:2106.09145 (per the arXiv HTML abstract and Theorem 1.1, fetched 2026-09-13):
  - Theorem 1.1: for Γ a finitely generated subgroup of [σ], ℒ_Γ(n) ⪯ (2R_X(n))!;
  - the abstract says they "exhibit a continuum of finitely generated LEF groups distinguishable by their LEF growth".
- So Question 7.5 is addressed in the general LEF setting, and 7.2 has upper bounds.
- The main node `elementary-group-lef-growth-separates-subshifts` (OPEN; its lower bound is the crux) asks the analogue of 7.2 for S_X. If it is established, the continuum of Question 7.5 comes out inside infinite simple Kazhdan LEF groups.
- Verdict: G_X gives a VARIANT (a Kazhdan simple instance) of 7.2/7.5, not an answer to either as printed. It is sk-lef-growth's lane.

**B3. Bradford, "Local permutation stability", arXiv:2211.15249 v2, §6.**
> In a related direction, the following question was posed by A. Lubotzky.
> Question 6.7. Does there exist a finitely generated locally stable group with Kazhdan's Property (T )?

- Bradford adds: "Lubotzky's Question 6.7 is answered in the negative" in [14]; arXiv:2307.13155 l.170 says infinite property (T) groups are "never locally HS- or P-stable".
- G_X is an infinite LEF Kazhdan group, so it is a non-locally-stable instance of that theorem, not an answer.
- Verdict: NOT NEEDED IN THE NOTE.

### C. Nearby printed questions that G_X does NOT answer (recorded against overclaiming)
**C1. arXiv:2608.05362, Open problem 6.1.** "Are there examples of finitely presented sofic groups with Kazhdan's property (T) that are not residually finite?" (quoted via the arXiv HTML; the same problem is already on main in `pestov91-literature-background-2026-09-13-part2.md` l.164 from an earlier source).
- G_X is not finitely presented: a f.p. LEF group is RF (Vershik–Gordon), and an infinite simple group is not RF.
- Relevant to sk-fp-sofic-a/b.

**C2. Cornulier, "A sofic group away from amenable groups", l.55-57.**
> Examples of isolated groups were provided in [CGP]. In that paper, examples of infinite isolated groups with Kazhdan's Property T were given [CGP, Paragraph 5.4], but it is not known if they are sofic.

- Isolated groups are finitely presented, so G_X is not one of them.

**C3. Thom, arXiv:0810.2180, p. 3.**
> C. Champetier (see [Cha00]) showed the existence of Kazhdan groups with no subgroups of finite index. These groups cannot have Kirchberg's factorization property and it remains an intriguing question to decide whether they can be hyperlinear.

- "They" means Champetier's groups (inductive limits of hyperbolic groups), so G_X does not answer this as printed.
- The one-line variant is TRUE: G_X is a hyperlinear, even LEF, Kazhdan group with no proper finite-index subgroups, since the core of a finite-index subgroup is a normal subgroup of finite index.
- I found no earlier printed question in exactly that form. sk-questions-oa landed `simple-kazhdan-group-lacks-factorization-property`, which covers the factorization angle.
- The same page lists "two sources of simple groups with Kazhdan's property (T)": Kac–Moody lattices [CR06], and Tarski monster quotients of Kazhdan hyperbolic groups [Gro87].

**C4. Kourovka Notebook.**
- The greps LEF / locally embeddable / hyperlinear / limit of finite / marked group return NO problem.
- "sofic" occurs only in 21.86 (M. Gromov, B. Weiss; posed by A. Lubotzky): "Is every group sofic?". Nonsofic groups exist (repo, OpenAI 2026-08-01); that status is not this lane's business.
- Kazhdan problems:
  - 18.108 and 18.109 (A. Jaikin-Zapirain), on groups with (τ)/(T) mapping onto finite simple groups: unrelated;
  - 14.34, a profinite group with an amenable and a Kazhdan dense subgroup: in the archive of solved problems, unrelated;
  - A14.34 / 3846, on branch groups with (T): unrelated.

**C5. de Cornulier–Guyot–Pitsch, Questions 1-4, on limits of isolated groups:** unrelated.

**C6. Arzhantseva–Cherix, arXiv:2008.12954.**
- Question 66 (full residual finiteness growth versus the finite-group profile): unrelated.
- Remark (l.1058): "It would be interesting to find an example of an LEF group with the second inequality being strict, cf. Question 66". The inequality is between the finite-family profile and LEF growth. No G_X statement is known; a possible target for sk-lef-growth.

**C7. Alekseev–Thom, arXiv:2512.15494, Proposition 6.6.**
> Let 1 → N → G → Q → 1 be a short exact sequence with N Kazhdan and Q an infinite simple group. Then, G is sofic-(τ ) or Q is sofic.

- This is a theorem, not a question. It is consistent with G_X (Q sofic).

**C8. Others checked, nothing bearing on G_X:**
- Kionke–Schesler Questions 10.4 and 11.2–11.6, and Problem 5.1;
- Nekrashevych 1511.08241 (A(G) = D(G)?);
- Katzlinger's survey (Vershik's Koopman irreducibility problem);
- arXiv:2305.00248, Questions 1.6-1.8 (Gao: Borel complexity of conjugacy for Cantor minimal systems and minimal subshifts);
- Arzhantseva–Păunescu Questions 7.9, 8.5, 8.6;
- Glebsky Open Question 23;
- arXiv:1712.01052, Question 2.5 etc.;
- arXiv:2512.09180, Question E;
- Bradford's Problems 7.1, 7.4, 7.6 and Questions 7.3, 7.7, 7.8;
- the problem page probFP.html (no Kazhdan, sofic or LEF problem).

## 2. One citation precision point (for sk-citations; not an error in the mathematics)
Disk l.63-65: "Thom had already constructed a finitely generated Kazhdan LEF group that is not residually finite~\cite[Theorem~1.4]{Thom}; his example is not simple."

Thom's Theorem 1.4 verbatim:
> There exists a finitely generated Kazhdan group G which is locally embeddable into finite groups (in particular sofic and hence hyperlinear) but does not have the factorization property.

- "Not residually finite" is stated on p. 3 just before it ("... Kazhdan group which is not residually finite and hence does not have the factorization property") and in the abstract. It is not in the theorem.
- Either cite `\cite{Thom}` without the theorem number, or keep the theorem number and say "that does not have the factorization property". The first costs zero lines.

## 3. Status
- Nothing in this part is a Cairn claim. All items are literature facts with verbatim quotes.
- Part 2 continues the sweep: Juschenko's book (Appendix B), Cornulier's Bourbaki survey arXiv:2002.09342, more Kourovka terms, the embeddings-into-simple-groups references [8,20,60] in arXiv:2304.09307, and questions on marked limits of finite simple groups with (T). Then the proposal artifact.
