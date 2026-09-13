# Pestov 9.1: priority, timeline and credit (2026-09-13)

Lane `pc-priority-credit` of the PC swarm, main at `2d7d577ab`.

**Evidence standard.**
- Printed sources: read from arXiv e-print sources or publisher PDFs.
- Times: GitHub's own records, meaning push events from the repository activity API and check-run start times. Commit
  author dates are listed alongside.
- Models: the `message.model` field of the local session transcripts. Commits are matched to transcripts through the
  `Claude-Session` trailer and the transcript's `bridge-session` or `remote_session_change` record.

## 0. Verdicts

- **Who asked first.** Ozawa, in arXiv:math/0306067v1, submitted 3 Jun 2003 16:48:05 UTC: "It is unknown whether there
  exists a simple property (T) group Γ which is hyperlinear."
  - Pestov prints the question as Open question 8.1 of arXiv:0804.3968v1 (24 Apr 2008). By v8 (4 Aug 2008) it is 9.1,
    headed "Cf. Ozawa".
  - Kirchberg (1994) is the nearest earlier text. He shows that infinite simple Kazhdan groups do not embed in the
    unitary group of the hyperfinite II_1 factor, and asks whether their C*-algebras are non-exact. He does not ask about
    hyperlinearity.
- **Earlier or independent answers.** None found in print, within the bound of §2.
  - Arzhantseva (2014) still lists "Does there exist an infinite simple sofic group with Kazhdan's property (T)?" as
    unknown. Her infinite simple Kazhdan example is only asymptotically sofic, which is a weaker property.
  - Inside the project, a lane of another session found the same group three minutes after the first lane.
  - It published only after the first landing (§2.4).
- **Our first public record.** `f375478c7`, pushed 2026-09-13 03:18:28 UTC. Then:
  - review PASS `0efeac410`, 03:48:56;
  - root established `8b65f0932`, 04:09:25;
  - second independent review `badc66e2d`, 05:56:36.
- **Credit.** Claude (Anthropic) produced the mathematics and both reviews, in Claude Code agent fleets under the
  author's direction.
  - No custom proof tool, Codex or GPT agent appears in the records.
  - Literature inputs to acknowledge are in §4.3.

## 1. Who asked first

### 1.1 Ozawa 2003

*About the QWEP conjecture*, arXiv:math/0306067.
- Versions: v1 3 Jun 2003 16:48:05 UTC; v2 10 May 2004 05:34:54 UTC.
- Journal: Internat. J. Math. 15 (2004), 501–530, as cited by Pestov. Not opened.
- The passages below read the same in v1 and v2 (`qwep.tex`).

**Introduction** (v1 lines 173–182):

> Since many exotic groups (or "monsters"), such as periodic simple groups with Kazhdan's property (T) and
> non-uniformly embeddable groups of Gromov, are arising as limits of hyperbolic groups, it is particularly interesting
> to know whether all hyperbolic groups are hyperlinear. In particular, if such simple property (T) groups or
> non-uniformly embeddable groups are not hyperlinear, then there would exist non-hyperlinear hyperbolic groups.

**Later, right after a proof** (v1 line 2155, v2 line 2190):

> It is unknown whether there exists a simple property (T) group Γ which is hyperlinear. By the above theorem, the full
> C*-algebra C*Γ of such a group Γ cannot have the LLP.

**Earlier in the same part** (v1 line 2094): "infinite simple groups with Kazhdan's property (T) (for existence of such
groups, see [Gromov]) do not have the property (F) as it was shown by Kirchberg".

This is the earliest printed ask found.
- It asks about existence, and only about hyperlinearity.
- It omits "infinite", since finite groups are trivially hyperlinear.
- It frames non-hyperlinearity as the interesting outcome.

### 1.2 Pestov 2008

*Hyperlinear and sofic groups: a brief guide*, arXiv:0804.3968.
- Eight versions: v1 24 Apr 2008 16:49:05 UTC; v8 4 Aug 2008 16:03:22 UTC.
- Journal: Bull. Symb. Log. 14(4) (2008), 449–480, as printed in Arzhantseva's 2014 bibliography (ref. [22]). The
  journal version was not opened.

**Passage.** v1 `hypsof.tex` lines 712–716, in `\section{Some classes of groups to look at}`:

> The two candidates for a counter-example are mentioned in Questions [q:T?] and [q:weiss].
>
> **Open question** (Cf. Ozawa [ozawa]). Let G be an infinite simple group with Kazhdan's property (T). Can it be
> hyperlinear (sofic)?

**Numbering.**
- `question` shares the `theorem` counter, which is numbered within sections.
- In v1 this is the eighth section, and the question is its first numbered environment. So v1 prints it as Open
  question 8.1. This is computed from the source; the v1 PDF was not rendered.
- v8 inserts the section "Von Neumann algebras and tracial ultraproducts" before it, so v8 prints 9.1. ex-novelty
  confirmed this on the v8 PDF, p. 21.
- v2–v7 were not checked.

**Wording and citation.** The wording is identical in v1 and v8. `[ozawa]` is "N. Ozawa, About the QWEP conjecture,
Internat. J. Math. 15 (2004), 501–530" (v8 line 1206).

### 1.3 Anything earlier

**Kirchberg,** *Discrete groups with Kazhdan's property T and factorization property are residually finite*, Math. Ann.
299 (1994), 551–563, doi:10.1007/BF01459798. Received 26 Mar 1992, revised 26 May 1993. PDF pp. 551–553 and 562–563
were read.
- **Corollary 1.2.** For a group with property T, these are equivalent:
  - (i) property (F);
  - (ii) a faithful unitary representation into the hyperfinite II_1 factor;
  - (iv) residual finiteness.
- **§5 "Remarks and questions."**
  > Gromov [7] suggested the existence of simple infinite property T groups G with every element of finite order [...].
  > Then such a G does not have property (F) by Theorem 1.1. Is C*(G) not exact?

  It goes on: for Gromov's examples, C*(G) fails the local lifting property if C*(SL_2(Z)) has Lance's WEP.
- **What this shows.** Kirchberg excludes embeddings into U(R), not into U(R^ω). His question is about exactness, not
  hyperlinearity.

**Rădulescu,** arXiv:math/0004172 (*The von Neumann algebra of the non-residually finite Baumslag group ... embeds into
R^ω*). A grep of the e-print source for Kazhdan, property (T) and simple group finds nothing.

**Bound.**
- Read: Ozawa v1 and v2; Pestov v1 and v8; 5 of Kirchberg's 13 pages.
- Grep only: Rădulescu 2000.
- Not opened: the Brown–Ozawa book (2008) and Kirchberg, Invent. Math. 112 (1993).
- Within this bound, Ozawa 2003 is the earliest printed ask.

## 2. Earlier or independent answers

### 2.1 Base passes on main

**ex-novelty deep pass,** `research/artifacts/ex-novelty-pestov91-deep-pass-2026-09-12.md` (`2bbd83a42`):
- LaTeX greps of 12 sources;
- v8 PDF pp. 20–22;
- 369 OpenAlex citing titles.

**ex-pestov91-harden,** `research/artifacts/pestov-9-1-writeup-2026-09-13-part3.md` §10:
- OpenAlex titles and abstracts of works citing Ozawa (141), Pestov (176), Thom 0810.2180 (60), Ershov–Jaikin-Zapirain
  (91), Grigorchuk–Medynets (24), Kassabov (50), Mimura–Sako (23), Caprace–Rémy (92) and Kassabov–Lubotzky–Nikolov (67);
- 24 keyword searches, including Kac–Moody AND sofic or hyperlinear;
- LaTeX greps of Mimura 1809.08918, Mimura–Sako, Mimura–Ozawa–Sako–Suzuki and five more.

That pass already covers Mimura and Kac–Moody lattices. Kac–Moody lattices are finitely presented, so they are never LEF,
and nothing found makes one sofic or hyperlinear.

**Result of both passes.**
- Neither found an earlier infinite simple Kazhdan group that is sofic, hyperlinear or LEF.
- Pestov–Kwiatkowska (arXiv:0911.4266, 2009) still call the question open.
- Alekseev–Thom (arXiv:2608.05362, 5 Aug 2026) is the latest expert list of known examples. It names no simple one.

### 2.2 This pass

**Read in full.**
- **Arzhantseva,** *Asymptotic approximations of finitely generated groups*, Extended Abstracts Fall 2012, Trends in
  Mathematics 1 (Springer, 2014), pp. 7–15, doi:10.1007/978-3-319-05488-9_2. Per p. 7 it is "a transcript of a talk the
  author gave since 2008".
  - **p. 11,** among the things not known: "Does there exist an infinite simple sofic group with Kazhdan's property (T)?"
  - **p. 13, Theorem 11:** "there exists an infinite simple asymptotically residually finite (hence, asymptotically
    sofic) group with Kazhdan's property (T)". The proof (p. 14) takes a torsion-free Tarski monster quotient of a
    torsion-free hyperbolic Kazhdan group, which has infinite girth.
  - **Why this is not soficity.** Asymptotic approximation lets the generating set change with the radius (Definition 9,
    p. 12). So the survey records the sofic form of the question as open in 2014, and its example does not answer it.
- **Pisier,** *Tensor Products of C\*-Algebras and Operator Spaces* (Cambridge, 2020), Chapter 17, "Property (T) and
  residually finite groups", pp. 311–316, doi:10.1017/9781108782081.018.
  - Its one example is Thom's. Proposition 17.9: a Kazhdan group that is hyperlinear, even sofic, but not residually
    finite, so C\*(G) has neither the WEP nor the LLP.
  - It says nothing about simple groups. The chapter "The WEP does not imply the LLP" was not opened.

**Tried, no signal.**
- **arXiv API, 20 queries.**
  - simple AND Kazhdan or property T AND sofic or hyperlinear;
  - "locally embeddable", LEF, "Steinberg algebra", "topological full group", subshift, "crossed product",
    "elementary matrices" and "Leavitt path algebra", each AND Kazhdan or property T;
  - "Kac-Moody" AND lattice AND sofic or hyperlinear;
  - "simple ring" AND elementary AND "normal subgroups";
  - the Arzhantseva title.

  Queries sorted newest first, so a September 2026 preprint would appear at the top. Every query returned HTTP 429 or
  timed out, the same wall as harden's pass. No arXiv result is claimed.
- **WebSearch:** the session budget was exhausted.

**OpenAlex, titles and abstracts.**
- **Citers since 2025-01-01 of the main records.**
  - Ozawa (W2123001453, 138 citers in all): 3, none on simple Kazhdan groups.
  - Pestov's guide (W2153827714, 173 in all): 9. The one abstract that says "simple" is *Word metrics in some wreath
    products where the passive group is finite and simple* (2025).
- **Citers of Ozawa, all years, with "simple" in title or abstract.** 8 works, on Tsirelson's problem, operator
  systems, model theory and wreath products. None names a simple Kazhdan group.
  - The same filter on Pestov's citers hit HTTP 429. Harden's abstract scan of all of them (§2.1) covers it.
- **Keyword searches over all works.**
  - "simple Kazhdan group sofic": 0 works.
  - "simple property (T) group hyperlinear": 1, Arzhantseva 2014 above.
  - "infinite simple group locally embeddable into finite groups property (T)": 3, including *On algebraic properties of
    topological full groups* (2014). None answers the question.
  - "elementary group simple ring property (T)", "Steinberg algebra property (T)", "topological full group property (T)
    elementary matrices": 19, 18 and 1 works, mostly off topic. The group-theoretic ones are groups graded by root
    systems, elementary subgroups of Chevalley groups, units of integral group rings, and ping-pong in Thompson's groups.
    None constructs a simple group.

**Bound of this pass.**
- Arzhantseva's survey and Pisier's chapter, read in full.
- 12 recent citer records, 8 keyword-filtered citers, 6 keyword searches.
- Nothing from arXiv or web search, because of rate limits.
- So a preprint too recent for OpenAlex to have indexed would not be seen.

### 2.3 Steinberg algebras and EL_n over simple rings

- **Known and credited** (Part 3 §9):
  - The ring `R = LC(X,F_q) ⋊ Z` is the Steinberg algebra of an effective minimal ample groupoid, so it is simple.
    Sources: Brown–Clark–Farthing–Sims (complex coefficients); Clark–Edie-Michell Cor. 4.6 and Steinberg Cor. 3.6 (any
    field).
  - Periodic approximation giving LEF is Grigorchuk–Medynets' mechanism, arXiv:1105.0719 Theorem 2.6.
- **Normal subgroups of EL_3(R).**
  - Classical sandwich theorems need stable-range or module-finiteness hypotheses.
  - The first review (`ex-review-groups-2026-09-12-part1.md` §1.3) records that the proof uses none of them and is self-contained.
  - This pass did not settle whether some classical theorem already covers R. That bears on credit for the simplicity
    step, not on priority for the group.

### 2.4 Parallel discovery inside the project

Two Claude Code sessions found S within three minutes of each other.

| lane | trailer session | transcript | construction first in the lane's records | first public record |
|---|---|---|---|---|
| `ex-kazhdan-simple-hyperlinear` | `01HaPd2YJDm2EQdhXtMepr2X` | subagent of session e26eab2c | 02:38:47 UTC, 9 min after launch (02:29:38) | `f375478c7`, pushed 03:18:28 |
| `isk-hyperlinear-kazhdan` | `01UM7nByUPBRzW6q2CVrVhTz` | fork in session 829306b2 | 02:41:58 UTC, continued from 02:26:00 | `5dfab98df`, pushed 04:06:51 |

**Prompts.** Neither prompt contains the construction.
- The first lane's brief (02:29:38) lists "EL_n over simple rings (Ershov–Jaikin (T))" among candidate hosts.
- The same brief asserts that "residual finiteness and LEF fail for infinite simple groups". S contradicts that for LEF.
- No user-side record of the isk fork before 02:42 mentions a subshift.

**The isk fork.**
- It first saw `f375478c7`, in a git log, at 03:43:58 UTC. Its records already name root detection at 03:26:23.
- Its artifact `research/artifacts/isk-hyperlinear-kazhdan-2026-09-12.md` says it "derived the construction and both
  main steps before reading Part 1".
- It adds a second LEF proof, by periodic truncation.

**Priority.** Inside the project, priority goes to `f375478c7`, the first public record. The isk lane is an independent
co-discoverer and the author of the second LEF proof.
